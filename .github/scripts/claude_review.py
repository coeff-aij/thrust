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
MAX_TOOL_OUTPUT_CHARS = 20_000
REPO_ROOT = Path()

tool_calls = 0


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


def excerpt(text: str, changed: set[int]) -> str:
    """The numbered lines of text within EXCERPT_CONTEXT lines of a changed line, the gaps marked."""
    lines = text.splitlines()
    keep = sorted(
        {n for line in changed for n in range(line - EXCERPT_CONTEXT, line + EXCERPT_CONTEXT + 1) if 1 <= n <= len(lines)}
    )
    out, previous = [], 0
    for n in keep:
        if n != previous + 1:
            out.append(f"[lines {previous + 1}-{n - 1} not shown; read them with read_file]")
        out.append(f"{n}: {lines[n - 1]}")
        previous = n
    if previous < len(lines):
        out.append(f"[lines {previous + 1}-{len(lines)} not shown; read them with read_file]")
    return "\n".join(out)


def read_changed_files(paths: list[str], changed: dict[str, set[int]]) -> tuple[dict[str, str], list[str]]:
    """Each changed file after the change: whole when small, otherwise the regions around its
    changed lines in `changed`. Files that are not text are listed apart."""
    contents: dict[str, str] = {}
    omitted: list[str] = []
    for path in paths:
        lines = changed.get(path)
        file = repo_file(path)
        if file is None:
            continue
        try:
            text = file.read_text()
        except UnicodeDecodeError:
            omitted.append(path)
            continue
        if lines is None:
            continue
        contents[path] = text if len(text) <= WHOLE_FILE_CHARS else excerpt(text, lines)
    return contents, omitted


def use_tool(run) -> str:
    """Runs one tool call within the budget and cuts its output to a size the context can take."""
    global tool_calls
    tool_calls += 1
    if tool_calls > MAX_TOOL_CALLS:
        return f"The budget of {MAX_TOOL_CALLS} tool calls is used up; write the review from what you have."
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
    return use_tool(lambda: numbered_lines(path, start_line, end_line))


def repo_file(path: str) -> Path | None:
    """The file at path in the checkout, or None when it is missing or a link leads outside it."""
    file = (REPO_ROOT / path).resolve()
    if not file.is_relative_to(REPO_ROOT) or not file.is_file():
        return None
    return file


def numbered_lines(path: str, start_line: int, end_line: int) -> str:
    file = repo_file(path)
    if file is None:
        return f"no file {path} in the repository"
    lines = file.read_text(errors="replace").splitlines()[start_line - 1 : end_line]
    return "\n".join(f"{n}: {line}" for n, line in enumerate(lines, start_line))


def gh_api_items(path: str) -> list[dict]:
    """The items of a paginated GitHub API list."""
    output = gh("api", "--paginate", path, "--jq", ".[]")
    return [json.loads(line) for line in output.splitlines()]


def earlier_reviews(repo: str, pr: str) -> tuple[str, str | None]:
    """The earlier automated reviews of the pull request, with the replies to their comments, and
    the commit the latest of them reviewed."""
    reviews = [
        r
        for r in gh_api_items(f"repos/{repo}/pulls/{pr}/reviews")
        if r["user"]["login"] == REVIEW_AUTHOR and r["body"].startswith(REVIEW_HEADING)
    ]
    comments = gh_api_items(f"repos/{repo}/pulls/{pr}/comments")
    parts = []
    for review in reviews:
        body = re.sub(r"\n*<!-- usage: .* -->", "", review["body"])
        parts.append(f"## Review of commit {review['commit_id']}\n\n{body}")
        for comment in comments:
            if comment["pull_request_review_id"] != review["id"] or comment.get("in_reply_to_id"):
                continue
            parts.append(f"### {comment['path']}:{comment['original_line']}\n\n{comment['body']}")
            parts += [
                f"Reply from {reply['user']['login']}: {reply['body']}"
                for reply in comments
                if reply.get("in_reply_to_id") == comment["id"]
            ]
    return "\n\n".join(parts), (reviews[-1]["commit_id"] if reviews else None)


def diff_since(repo: str, base: str, head: str, pr_files: set[str]) -> tuple[str, bool] | None:
    """The changes from base to head to the pull request's files as a unified diff, and whether a
    merge commit lies in between (it may bring in changes of the base branch to those files); None
    when base was rewritten by a force-push or a file has no patch."""
    try:
        compare = json.loads(gh("api", f"repos/{repo}/compare/{base}...{head}"))
    except subprocess.CalledProcessError:
        return None
    if compare.get("status") not in ("ahead", "identical"):
        return None
    merged = any(len(c["parents"]) > 1 for c in compare.get("commits", []))
    parts = []
    for f in compare.get("files", []):
        if f["filename"] not in pr_files:
            continue
        if "patch" not in f:
            return None
        parts.append(f"--- a/{f.get('previous_filename', f['filename'])}\n+++ b/{f['filename']}\n{f['patch']}")
    return "\n".join(parts), merged


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
    diff: str,
    since: str | None,
    merged: bool,
    lines: dict[str, set[int]],
    contents: dict[str, str],
    omitted: list[str],
    earlier: str,
) -> str:
    parts = [f"# Pull request: {pr['title']}\n\n{pr['body'] or '(no description)'}"]
    if since is None:
        parts.append(f"# Diff\n\n```diff\n{diff}\n```")
    else:
        files = "\n".join(f"{path}: {line_ranges(lines.get(path, set()))}" for path in (f["path"] for f in pr["files"]))
        parts.append(f"# Files the pull request changes, with the lines it changes or keeps as context\n\n{files}")
        note = (
            "\n\nThe commits since include a merge of the base branch, so a change below may come from the base"
            " branch rather than from this pull request; the whole pull request is in its files above."
            if merged
            else ""
        )
        parts.append(f"# Diff since the commit the latest review saw ({since}){note}\n\n```diff\n{diff}\n```")
    for path, text in contents.items():
        parts.append(f"# File after the change: {path}\n\n```\n{text}\n```")
    if omitted:
        parts.append("# Changed files not included (not text)\n\n" + "\n".join(omitted))
    if earlier:
        parts.append(f"# Earlier automated reviews\n\n{earlier}")
    return "\n\n".join(parts)


def request_review(client: anthropic.Anthropic, model: str, system: list[dict], prompt: str) -> tuple[Review, str]:
    """Runs the review; the conversation is cached as it grows (5 minutes: a later review sends
    another prompt), so each tool call re-reads the earlier turns from the cache."""
    runner = client.beta.messages.tool_runner(
        model=model,
        max_tokens=MAX_OUTPUT_TOKENS,
        stream=True,
        system=system,
        messages=[{"role": "user", "content": prompt}],
        tools=[grep, list_files, read_file],
        max_iterations=MAX_TOOL_CALLS + 5,
        cache_control={"type": "ephemeral"},
        output_config={"effort": "high"},
        output_format=Review,
        betas=["server-side-fallback-2026-07-01"],
        fallbacks="default",
    )
    usage = {"input": 0, "cache_write": 0, "cache_read": 0, "output": 0}
    for stream in runner:
        message = stream.get_final_message()
        usage["input"] += message.usage.input_tokens
        usage["cache_write"] += message.usage.cache_creation_input_tokens or 0
        usage["cache_read"] += message.usage.cache_read_input_tokens or 0
        usage["output"] += message.usage.output_tokens
    summary = f"{tool_calls} tool calls, tokens {usage}"
    print(f"usage: {summary}", file=sys.stderr)
    response = runner.until_done()
    if response.stop_reason != "end_turn":
        sys.exit(f"no review: stop_reason {response.stop_reason}")
    return response.parsed_output, summary


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
    earlier, reviewed = earlier_reviews(args.repo, args.pr)
    # A re-review is sent the changes since the commit the latest review saw.
    paths = [f["path"] for f in pr["files"]]
    since_diff = diff_since(args.repo, reviewed, pr["headRefOid"], set(paths)) if reviewed else None
    since = reviewed if since_diff is not None else None
    sent, merged = since_diff if since_diff is not None else (diff, False)
    contents, omitted = read_changed_files(paths, commentable_lines(sent))
    prompt = build_prompt(pr, sent, since, merged, lines, contents, omitted, earlier)

    if args.dry_run:
        system = sum(len(block["text"]) for block in system_blocks(args.prompt))
        print(f"model: {args.model}\nsystem: {system} chars\nprompt: {len(prompt)} chars")
        print(f"earlier reviews: {len(earlier)} chars")
        merge_note = " (across a merge of the base branch)" if merged else ""
        print(f"diff: {'since ' + since + merge_note if since else 'whole pull request'}, {len(sent)} chars")
        print("included:", *contents, sep="\n  ")
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
