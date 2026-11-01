"""Review a pull request with the Claude API and post the result as one PR review.

The review points out places for the developers to check, as inline comments on the changed
lines. The system prompt, with the aspects to look at and what not to report, is a file each
repository keeps.

Usage: claude_review.py --repo OWNER/NAME --pr NUMBER --prompt FILE --head DIR [--model MODEL]
                        [--dry-run | --print]

The prompt and the guidelines are read from the current directory, the reviewed code from the
checkout of the pull request's head in DIR, so that a pull request cannot change how it is
reviewed or what runs with the API key.

--dry-run fetches the pull request and prints what would be sent, without calling the API or
posting anything. --print calls the API and prints the review instead of posting it.
"""

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Literal

import anthropic
from anthropic import beta_tool
from pydantic import BaseModel

GUIDELINE_FILES = ["AGENTS.md", "CLAUDE.md", "README.md"]
# A changed file up to this size is sent whole; a larger one as the regions around its changes.
WHOLE_FILE_CHARS = 20_000
# Lines of context around each changed region of a larger file.
EXCERPT_CONTEXT = 40
# Room for adaptive thinking and the review together; thinking counts against it.
MAX_OUTPUT_TOKENS = 64_000
REVIEW_HEADING = "**Claude review** (automated)"
REVIEW_AUTHOR = "github-actions[bot]"
MAX_TOOL_CALLS = 40
# A run past this many tokens sent anew, written to the cache or generated, the bulk of what a run
# costs, gets no more tool results and writes the review from what it has; the largest runs so far
# took about 160,000. Cache reads, a small part of the cost, are bounded by MAX_TOOL_CALLS.
MAX_RUN_TOKENS = 500_000
MAX_TOOL_OUTPUT_CHARS = 20_000
# The compare API lists at most this many changed files.
COMPARE_MAX_FILES = 300
REPO_ROOT = Path()
# The source of the Rust standard library of the toolchain the default branch pins, which the
# workflow fetches; without it the std tools say so.
STD_ROOT = Path(os.environ["RUST_SRC"]).resolve() if os.environ.get("RUST_SRC") else None

tool_calls = 0
run_tokens = 0


class Comment(BaseModel):
    path: str
    line: int
    aspect: str
    severity: Literal["blocking", "check", "suggestion"]
    body: str


class Review(BaseModel):
    summary: str
    comments: list[Comment]


def gh(*args: str) -> str:
    return subprocess.run(["gh", *args], check=True, capture_output=True, text=True).stdout


def commentable_lines(diff: str) -> dict[str, set[int]]:
    """Line numbers on the new side of the diff that GitHub accepts review comments on."""
    lines: dict[str, set[int]] = {}
    path = None
    new_line = 0
    for row in diff.splitlines():
        if row.startswith("+++ "):
            path = row[6:] if row.startswith("+++ b/") else None
            continue
        hunk = re.match(r"@@ -\d+(?:,\d+)? \+(\d+)(?:,\d+)? @@", row)
        if hunk:
            new_line = int(hunk.group(1))
            continue
        if path is None or row.startswith(("---", "-", "\\")):
            continue
        if row.startswith(("+", " ")):
            lines.setdefault(path, set()).add(new_line)
            new_line += 1
    return lines


def file_diffs(diff: str) -> dict[str, str]:
    """Each file's part of a unified diff, by its path after the change (before it, for a deleted
    file)."""
    parts: dict[str, str] = {}
    for chunk in re.split(r"^(?=diff --git )", diff, flags=re.M):
        new = re.search(r"^\+\+\+ b/(.*)$", chunk, re.M)
        old = re.search(r"^--- a/(.*)$", chunk, re.M)
        # A binary file, a rename or a mode change has no `+++`/`---` line, only the header.
        header = re.match(r"diff --git a/.* b/(.*)$", chunk, re.M)
        path = new.group(1) if new else old.group(1) if old else header.group(1) if header else None
        if path:
            parts[path] = chunk
    return parts


def file_changes(chunk: str) -> tuple[set[int], dict[int, list[str]]]:
    """The lines a file's diff adds, by their number after the change, and the lines it removes,
    by the number of the line after the change that follows them."""
    added: set[int] = set()
    removed: dict[int, list[str]] = {}
    new_line = None
    for row in chunk.splitlines():
        hunk = re.match(r"@@ -\d+(?:,\d+)? \+(\d+)(?:,\d+)? @@", row)
        if hunk:
            new_line = int(hunk.group(1))
        elif new_line is None or row.startswith("\\"):
            continue
        elif row.startswith("+"):
            added.add(new_line)
            new_line += 1
        elif row.startswith("-"):
            removed.setdefault(new_line, []).append(row[1:])
        else:
            new_line += 1
    return added, removed


def annotated(text: str, added: set[int], removed: dict[int, list[str]], whole: bool) -> str:
    """The file after the change, numbered, `+` after the number of a line the change adds and the
    lines it removes as `-` lines where they stood: whole, or the regions within EXCERPT_CONTEXT
    lines of a change, the gaps marked."""
    lines = text.splitlines()
    changed = added | set(removed)
    near = {n for c in changed for n in range(c - EXCERPT_CONTEXT, c + EXCERPT_CONTEXT + 1)}
    keep = [n for n in range(1, len(lines) + 1) if whole or n in near]
    out, previous = [], 0
    for n in keep:
        if n != previous + 1:
            out.append(f"[lines {previous + 1}-{n - 1} not shown; read them with read_file]")
        out += [f"     - {r}" for r in removed.get(n, [])]
        out.append(f"{n}{'+' if n in added else ':'} {lines[n - 1]}")
        previous = n
    if previous < len(lines):
        out.append(f"[lines {previous + 1}-{len(lines)} not shown; read them with read_file]")
    out += [f"     - {r}" for r in removed.get(len(lines) + 1, [])]
    return "\n".join(out)


def changed_file_views(chunks: dict[str, str]) -> tuple[dict[str, str], list[str]]:
    """A view of each changed text file after the change, whole when small; files that are not
    text are listed apart. The guideline files, which the system prompt holds, lockfiles and
    deleted files get none: their diff is sent instead."""
    views: dict[str, str] = {}
    omitted: list[str] = []
    for path, chunk in chunks.items():
        file = repo_file(path)
        if path in GUIDELINE_FILES or path.endswith(".lock") or file is None:
            continue
        try:
            text = file.read_text()
        except UnicodeDecodeError:
            omitted.append(path)
            continue
        added, removed = file_changes(chunk)
        if added or removed:
            views[path] = annotated(text, added, removed, len(text) <= WHOLE_FILE_CHARS)
    return views, omitted


def use_tool(run) -> str:
    """Runs one tool call within the budget and cuts its output to a size the context can take."""
    global tool_calls
    tool_calls += 1
    if tool_calls > MAX_TOOL_CALLS or run_tokens > MAX_RUN_TOKENS:
        return "The budget of this review is used up; write the review from what you have."
    output = run()
    if len(output) > MAX_TOOL_OUTPUT_CHARS:
        return output[:MAX_TOOL_OUTPUT_CHARS] + "\n[output cut; narrow the request]"
    return output


def git(*args: str) -> str:
    result = subprocess.run(["git", *args], cwd=REPO_ROOT, capture_output=True, text=True)
    return result.stdout or result.stderr


@beta_tool
def grep(pattern: str, path: str = ".") -> str:
    """Search the repository's tracked files and return the matching lines as path:line:text.

    Args:
        pattern: An extended regular expression.
        path: A file or directory relative to the repository root.
    """
    return use_tool(lambda: git("grep", "-n", "-E", "-e", pattern, "--", path) or "no matches")


@beta_tool
def list_files(path: str = ".") -> str:
    """List the repository's tracked files under a directory.

    Args:
        path: A directory relative to the repository root.
    """
    return use_tool(lambda: git("ls-files", "--", path) or "no files")


@beta_tool
def read_file(path: str, start_line: int = 1, end_line: int = 400) -> str:
    """Read lines of a file in the repository, numbered.

    Args:
        path: A file relative to the repository root.
        start_line: The first line to read, from 1.
        end_line: The last line to read.
    """
    return use_tool(lambda: numbered_lines(repo_file(path), path, start_line, end_line))


@beta_tool
def grep_std(pattern: str, path: str = ".") -> str:
    """Search the source of the Rust standard library of the repository's pinned toolchain and
    return the matching lines as path:line:text.

    Args:
        pattern: An extended regular expression.
        path: A file or directory relative to the library, such as `core/src/iter/adapters`.
    """
    return use_tool(lambda: std_grep(pattern, path))


@beta_tool
def read_std(path: str, start_line: int = 1, end_line: int = 400) -> str:
    """Read lines of a file of the Rust standard library of the repository's pinned toolchain,
    numbered.

    Args:
        path: A file relative to the library, such as `core/src/iter/adapters/zip.rs`.
        start_line: The first line to read, from 1.
        end_line: The last line to read.
    """
    return use_tool(lambda: numbered_lines(std_path(path), path, start_line, end_line))


def std_path(path: str) -> Path | None:
    """The file or directory at path in the standard library's source, or None when there is none."""
    if STD_ROOT is None:
        return None
    target = (STD_ROOT / path).resolve()
    if not target.is_relative_to(STD_ROOT) or not target.exists():
        return None
    return target


def std_grep(pattern: str, path: str) -> str:
    target = std_path(path)
    if target is None:
        return f"no {path} in the standard library source" if STD_ROOT else "the standard library source is not available"
    result = subprocess.run(["grep", "-rnE", "--include=*.rs", "-e", pattern, str(target)], capture_output=True, text=True)
    return result.stdout.replace(f"{STD_ROOT}/", "") or "no matches"


def repo_file(path: str) -> Path | None:
    """The file at path in the checkout, or None when it is missing or a link leads outside it."""
    file = (REPO_ROOT / path).resolve()
    if not file.is_relative_to(REPO_ROOT) or not file.is_file():
        return None
    return file


def numbered_lines(file: Path | None, path: str, start_line: int, end_line: int) -> str:
    if file is None or not file.is_file():
        return f"no file {path}"
    lines = file.read_text(errors="replace").splitlines()[start_line - 1 : end_line]
    return "\n".join(f"{n}: {line}" for n, line in enumerate(lines, start_line))


def gh_api_items(path: str) -> list[dict]:
    """The items of a paginated GitHub API list."""
    output = gh("api", "--paginate", path, "--jq", ".[]")
    return [json.loads(line) for line in output.splitlines()]


def earlier_reviews(repo: str, pr: str) -> tuple[str, str | None, bool]:
    """The earlier automated reviews of the pull request with the replies to their comments, the
    commit the latest of them reviewed, and whether a reply is newer than it.

    The latest review judged each earlier comment replied to before it, so of the older reviews
    only the comments without a reply or with a newer reply are given, the others counted."""
    reviews = [
        r
        for r in gh_api_items(f"repos/{repo}/pulls/{pr}/reviews")
        if r["user"]["login"] == REVIEW_AUTHOR and r["body"].startswith(REVIEW_HEADING)
    ]
    if not reviews:
        return "", None, False
    latest = reviews[-1]
    comments = gh_api_items(f"repos/{repo}/pulls/{pr}/comments")
    replies = [c for c in comments if c.get("in_reply_to_id")]
    new_reply = any(r["created_at"] > latest["submitted_at"] for r in replies)
    parts, settled = [], 0
    for review in reviews:
        if review is latest:
            body = re.sub(r"\n*<!-- usage: .* -->", "", review["body"])
            parts.append(f"## Latest review, of commit {review['commit_id']}\n\n{body}")
        for comment in comments:
            if comment["pull_request_review_id"] != review["id"] or comment.get("in_reply_to_id"):
                continue
            answers = [r for r in replies if r["in_reply_to_id"] == comment["id"]]
            judged = answers and all(r["created_at"] < latest["submitted_at"] for r in answers)
            if review is not latest and judged:
                settled += 1
                continue
            parts.append(f"### {comment['path']}:{comment['original_line']}\n\n{comment['body']}")
            parts += [f"Reply from {r['user']['login']}: {r['body']}" for r in answers]
    if settled:
        parts.append(f"{settled} comments of older reviews were replied to before the latest review judged them.")
    return "\n\n".join(parts), latest["commit_id"], new_reply


def diff_since(repo: str, base: str, head: str, pr_files: set[str]) -> tuple[str, bool] | None:
    """The changes from base to head to the pull request's files as a unified diff, and whether a
    merge commit lies in between (it may bring in changes of the base branch to those files); None
    when base was rewritten by a force-push, a file has no patch, or the comparison is longer than
    the lists the compare API returns (250 commits, 300 files)."""
    try:
        compare = json.loads(gh("api", f"repos/{repo}/compare/{base}...{head}"))
    except subprocess.CalledProcessError:
        return None
    if compare.get("status") not in ("ahead", "identical"):
        return None
    commits, files = compare.get("commits", []), compare.get("files", [])
    if compare.get("total_commits", 0) > len(commits) or len(files) >= COMPARE_MAX_FILES:
        return None
    merged = any(len(c["parents"]) > 1 for c in commits)
    parts = []
    for f in files:
        if f["filename"] not in pr_files:
            continue
        if "patch" not in f:
            return None
        old = f.get("previous_filename", f["filename"])
        parts.append(f"diff --git a/{old} b/{f['filename']}\n--- a/{old}\n+++ b/{f['filename']}\n{f['patch']}\n")
    return "".join(parts), merged


def system_blocks(prompt_file: Path) -> list[dict]:
    """The review instructions and the repository's guidelines, which every review shares.

    They are cached for an hour, so that the re-review after a round of fixes reads them at a
    twentieth of the price.
    """
    guidelines = "\n\n".join(
        f"# Guidelines: {name}\n\n{Path(name).read_text()}" for name in GUIDELINE_FILES if Path(name).is_file()
    )
    return [
        {"type": "text", "text": prompt_file.read_text()},
        {"type": "text", "text": guidelines, "cache_control": {"type": "ephemeral", "ttl": "1h"}},
    ]


def line_ranges(lines: set[int]) -> str:
    """Lines as ranges, `3-7, 12`."""
    ranges: list[list[int]] = []
    for n in sorted(lines):
        if ranges and n == ranges[-1][1] + 1:
            ranges[-1][1] = n
        else:
            ranges.append([n, n])
    return ", ".join(f"{a}-{b}" if a != b else f"{a}" for a, b in ranges) or "none"


def build_prompt(
    pr: dict,
    chunks: dict[str, str],
    views: dict[str, str],
    since: str | None,
    merged: bool,
    lines: dict[str, set[int]],
    omitted: list[str],
    earlier: str,
) -> str:
    parts = [f"# Pull request: {pr['title']}\n\n{pr['body'] or '(no description)'}"]
    if since is not None:
        files = "\n".join(f"{path}: {line_ranges(lines.get(path, set()))}" for path in (f["path"] for f in pr["files"]))
        parts.append(f"# Files the pull request changes, with the lines it changes or keeps as context\n\n{files}")
        note = (
            "\n\nThe commits since include a merge of the base branch, so a change below may come from the base"
            " branch rather than from this pull request; the whole pull request is in its files above."
            if merged
            else ""
        )
        parts.append(f"# The changes below are those since the commit the latest review saw ({since}){note}")
    for path, view in views.items():
        parts.append(f"# File: {path}\n\n```\n{view}\n```")
    rest = "".join(chunk for path, chunk in chunks.items() if path not in views)
    if rest:
        parts.append(f"# The rest of the diff\n\n```diff\n{rest}\n```")
    if omitted:
        parts.append("# Changed files not included (not text)\n\n" + "\n".join(omitted))
    if earlier:
        parts.append(f"# Earlier automated reviews\n\n{earlier}")
    return "\n\n".join(parts)


def request_review(client: anthropic.Anthropic, model: str, system: list[dict], prompt: str) -> tuple[Review, str]:
    """Runs the review; the conversation is cached as it grows (5 minutes: a later review sends
    another prompt), so each tool call re-reads the earlier turns from the cache."""
    global run_tokens
    runner = client.beta.messages.tool_runner(
        model=model,
        max_tokens=MAX_OUTPUT_TOKENS,
        stream=True,
        system=system,
        messages=[{"role": "user", "content": prompt}],
        tools=[grep, list_files, read_file, grep_std, read_std],
        max_iterations=MAX_TOOL_CALLS + 5,
        cache_control={"type": "ephemeral"},
        output_config={"effort": "high"},
        output_format=Review,
        betas=["server-side-fallback-2026-07-01"],
        fallbacks="default",
    )
    usage = dict.fromkeys(["input", "write_5m", "write_1h", "read", "output", "thinking"], 0)
    for stream in runner:
        add_usage(usage, stream.get_final_message().usage)
        run_tokens = sum(usage[kind] for kind in ("input", "write_5m", "write_1h", "output"))
    summary = f"{tool_calls} tool calls, tokens {usage}"
    print(f"usage: {summary}", file=sys.stderr)
    response = runner.until_done()
    if response.stop_reason != "end_turn":
        sys.exit(f"no review: stop_reason {response.stop_reason}")
    return response.parsed_output, summary


def add_usage(usage: dict[str, int], part) -> None:
    """Adds one response's token counts to usage."""
    usage["input"] += part.input_tokens
    usage["read"] += part.cache_read_input_tokens or 0
    usage["output"] += part.output_tokens
    if part.cache_creation:
        usage["write_5m"] += part.cache_creation.ephemeral_5m_input_tokens
        usage["write_1h"] += part.cache_creation.ephemeral_1h_input_tokens
    else:
        usage["write_5m"] += part.cache_creation_input_tokens or 0
    if part.output_tokens_details:
        usage["thinking"] += part.output_tokens_details.thinking_tokens or 0


def review_payload(review: Review, head_sha: str, lines: dict[str, set[int]], omitted: list[str], usage: str) -> dict:
    inline = [c for c in review.comments if c.line in lines.get(c.path, set())]
    outside = [c for c in review.comments if c not in inline]
    body = [f"{REVIEW_HEADING}\n\n{review.summary}"]
    body += [f"- `{c.path}:{c.line}`: {comment_text(c)}" for c in outside]
    if omitted:
        body.append("Not reviewed (not text): " + ", ".join(f"`{p}`" for p in omitted))
    # Kept with the review, where the API can read it back after the run's log has expired.
    body.append(f"<!-- usage: {usage} -->")
    return {
        "commit_id": head_sha,
        "event": "COMMENT",
        "body": "\n\n".join(body),
        "comments": [{"path": c.path, "line": c.line, "side": "RIGHT", "body": comment_text(c)} for c in inline],
    }


def comment_text(comment: Comment) -> str:
    return f"[{comment.severity}, {comment.aspect}] {comment.body}"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", required=True)
    parser.add_argument("--pr", required=True)
    parser.add_argument("--prompt", required=True, type=Path)
    parser.add_argument("--head", required=True, type=Path)
    parser.add_argument("--model", default="claude-opus-5-5")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--dry-run", action="store_true")
    mode.add_argument("--print", action="store_true")
    args = parser.parse_args()
    global REPO_ROOT
    REPO_ROOT = args.head.resolve()

    pr = json.loads(gh("pr", "view", args.pr, "-R", args.repo, "--json", "title,body,headRefOid,files"))
    checked_out = git("rev-parse", "HEAD").strip()
    if checked_out != pr["headRefOid"]:
        sys.exit(f"the pull request moved from {checked_out} to {pr['headRefOid']} after the checkout; run again")
    diff = gh("pr", "diff", args.pr, "-R", args.repo)
    lines = commentable_lines(diff)
    earlier, reviewed, new_reply = earlier_reviews(args.repo, args.pr)
    if reviewed == pr["headRefOid"] and not new_reply:
        print(f"nothing new since the review of {reviewed}: no commit and no reply")
        return
    # A re-review is sent the changes since the commit the latest review saw.
    paths = [f["path"] for f in pr["files"]]
    since_diff = diff_since(args.repo, reviewed, pr["headRefOid"], set(paths)) if reviewed else None
    since = reviewed if since_diff is not None else None
    sent, merged = since_diff if since_diff is not None else (diff, False)
    chunks = file_diffs(sent)
    views, omitted = changed_file_views(chunks)
    prompt = build_prompt(pr, chunks, views, since, merged, lines, omitted, earlier)

    if args.dry_run:
        system = sum(len(block["text"]) for block in system_blocks(args.prompt))
        print(f"model: {args.model}\nsystem: {system} chars\nprompt: {len(prompt)} chars")
        print(f"earlier reviews: {len(earlier)} chars")
        merge_note = " (across a merge of the base branch)" if merged else ""
        print(f"diff: {'since ' + since + merge_note if since else 'whole pull request'}, {len(sent)} chars")
        print("shown as files:", *views, sep="\n  ")
        print("as diff:", *(p for p in chunks if p not in views), sep="\n  ")
        print("omitted:", *omitted, sep="\n  ")
        print("commentable lines:", *(f"{p}: {len(n)}" for p, n in lines.items()), sep="\n  ")
        return

    review, usage = request_review(anthropic.Anthropic(), args.model, system_blocks(args.prompt), prompt)
    payload = review_payload(review, pr["headRefOid"], lines, omitted, usage)
    if args.print:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
        return
    subprocess.run(
        ["gh", "api", f"repos/{args.repo}/pulls/{args.pr}/reviews", "--method", "POST", "--input", "-", "--jq", ".html_url"],
        input=json.dumps(payload), check=True, text=True,
    )


if __name__ == "__main__":
    main()
