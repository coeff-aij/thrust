"""Review a pull request with the Claude API and post the result as one PR review.

The review points out places for the developers to check, as comments on the changed lines, or on
a changed file when the line is not part of the diff. The system prompt, with the aspects to look
at and what not to report, is a file each repository keeps.

Usage: claude_review.py --repo OWNER/NAME --pr NUMBER --prompt FILE --head DIR [--model MODEL]
                        [--guidelines FILE...] [--dry-run | --print]

The prompt and the guidelines are read from the current directory, the reviewed code from the
checkout of the pull request's head in DIR, so that a pull request cannot change how it is
reviewed or what runs with the API key. The tools that read the Rust standard library are given
only when RUST_SRC names its source.

--dry-run fetches the pull request and prints what would be sent, without calling the API or
posting anything. --print calls the API and prints the review instead of posting it.
"""

import argparse
import functools
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Literal, NamedTuple

import anthropic
from anthropic import beta_tool
from pydantic import BaseModel

from review_github import REVIEW_AUTHOR, REVIEW_HEADING, automated_reviews, gh, gh_api_items

GUIDELINE_FILES = ["AGENTS.md", "CLAUDE.md", "README.md"]
# On a first review, a changed file is sent whole when it is short or the change adds at least
# half of its lines; otherwise, and on every re-review, as the regions around its changes.
WHOLE_FILE_LINES = 150
WHOLE_FILE_CHARS = 8_000
# Lines of context around each changed region of a file sent in excerpts.
EXCERPT_CONTEXT = 40
# Room for adaptive thinking and the review together; thinking counts against it.
MAX_OUTPUT_TOKENS = 64_000
MAX_TOOL_CALLS = 25
# A run past this many tokens sent anew, written to the cache or generated, the bulk of what a run
# costs, gets no more tool results and writes the review from what it has; the largest runs so far
# took about 150,000. Cache reads, a small part of the cost, are bounded by MAX_TOOL_CALLS.
MAX_RUN_TOKENS = 250_000
MAX_TOOL_OUTPUT_CHARS = 20_000
# The part of a cited commit's diff shown under a reply; commit_diff reads the rest.
REPLY_DIFF_CHARS = 4_000
# The compare API lists at most this many changed files.
COMPARE_MAX_FILES = 300
# A commit hash as replies cite it: 7 to 40 hex digits, at least one of them a decimal digit, so
# that hex-only words such as "defaced" are not taken for one.
COMMIT_SHA = re.compile(r"\b(?=[a-f]*\d)[0-9a-f]{7,40}\b")
REPO_ROOT = Path()
# The source of the Rust standard library of the toolchain the default branch pins, which the
# workflow fetches; without it the std tools are not given.
STD_ROOT = Path(os.environ["RUST_SRC"]).resolve() if os.environ.get("RUST_SRC") else None
# The repository and the commits of the pull request, which commit_diff reads.
REPO = ""
PR_COMMITS: list[str] = []

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


def changed_file_views(
    chunks: dict[str, str], guidelines: list[str], re_review: bool
) -> tuple[dict[str, str], set[str], list[str]]:
    """A view of each changed text file after the change, the files sent whole among them, and the
    files that are not text, listed apart. The guideline files, which the system prompt holds,
    lockfiles and deleted files get no view: their diff is sent instead."""
    views: dict[str, str] = {}
    whole: set[str] = set()
    omitted: list[str] = []
    for path, chunk in chunks.items():
        file = repo_file(path)
        if path in guidelines or path.endswith(".lock") or file is None:
            continue
        try:
            text = file.read_text()
        except UnicodeDecodeError:
            omitted.append(path)
            continue
        added, removed = file_changes(chunk)
        if not added and not removed:
            continue
        if not re_review and sent_whole(text, added):
            whole.add(path)
        views[path] = annotated(text, added, removed, path in whole)
    return views, whole, omitted


def sent_whole(text: str, added: set[int]) -> bool:
    """Whether a changed file is short, or the change adds at least half of its lines."""
    count = len(text.splitlines())
    short = count <= WHOLE_FILE_LINES and len(text) <= WHOLE_FILE_CHARS
    return short or 2 * len(added) >= count


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


@beta_tool
def commit_diff(sha: str, path: str = "") -> str:
    """Read what one commit of the pull request changes: its diff of a file, or the files it
    changes when no path is given. The checkout has no history, so this is the way to read a commit.

    Args:
        sha: A commit of the pull request, abbreviated to at least 7 hex digits.
        path: A file relative to the repository root, or empty for the list of changed files.
    """
    return use_tool(lambda: commit_change(sha, path))


def pr_commit(sha: str) -> str | None:
    """The commit of the pull request that sha abbreviates, or None when there is not exactly one."""
    matches = [c for c in PR_COMMITS if c.startswith(sha.lower())]
    return matches[0] if len(matches) == 1 else None


@functools.cache
def commit_data(sha: str) -> dict:
    return json.loads(gh("api", f"repos/{REPO}/commits/{sha}"))


def commit_change(sha: str, path: str, limit: int | None = None) -> str:
    """A commit's title and its diff of path, cut to limit characters when given, or the files it
    changes when path is empty or not among them."""
    full = pr_commit(sha)
    if full is None:
        return f"{sha} is not a commit of this pull request."
    commit = commit_data(full)
    files = {f["filename"]: f for f in commit["files"]}
    head = f"Commit {full[:12]} ({commit['commit']['message'].splitlines()[0]})"
    if path not in files:
        names = list(files)
        more = f" and {len(names) - 20} more" if len(names) > 20 else ""
        changes = (", ".join(names[:20]) or "no file") + more
        return f"{head} changes {changes}." if not path else f"{head} does not change {path}; it changes {changes}."
    patch = files[path].get("patch")
    if patch is None:
        return f"{head} changes {path}; GitHub gives no text diff of it."
    if limit is not None and len(patch) > limit:
        patch = patch[:limit] + "\n[diff cut; commit_diff shows more]"
    return f"{head}, its diff of {path}:\n\n```diff\n{patch}\n```"


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
        return f"no {path} in the standard library source"
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


class Sent(NamedTuple):
    """The diff a review is sent, the commit it is the changes since (None for the whole pull
    request), whether a merge of the base branch lies in between, and what was sent, and why, in
    words for the usage record."""

    diff: str
    since: str | None
    merged: bool
    note: str


def earlier_reviews(repo: str, pr: str) -> tuple[str, str | None, bool]:
    """The earlier automated reviews of the pull request with the replies to their comments, the
    commit the latest of them reviewed, and whether a reply is newer than it.

    The latest review judged each earlier comment replied to before it, so of the older reviews
    only the comments without a reply or with a newer reply are given, the others counted."""
    reviews = automated_reviews(repo, pr)
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
            line = f":{comment['original_line']}" if comment.get("original_line") else ""
            parts.append(f"### {comment['path']}{line}\n\n{comment['body']}")
            parts += [reply_text(r, comment["path"]) for r in answers]
    if settled:
        parts.append(f"{settled} comments of older reviews were replied to before the latest review judged them.")
    return "\n\n".join(parts), latest["commit_id"], new_reply


def reply_text(reply: dict, path: str) -> str:
    """A reply, with what each commit it cites changes in the commented file."""
    shas = dict.fromkeys(COMMIT_SHA.findall(reply["body"]))
    cited = [commit_change(sha, path, REPLY_DIFF_CHARS) for sha in shas] or ["The reply cites no commit."]
    return "\n\n".join([f"Reply from {reply['user']['login']}: {reply['body']}", *cited])


def what_to_send(repo: str, reviewed: str | None, head: str, pr_files: set[str], diff: str) -> Sent:
    """The whole pull request's diff on a first review; on a re-review the changes since the
    commit the latest review saw, unless the compare API cannot give them."""
    if reviewed is None:
        return Sent(diff, None, False, "whole pull request, first review")
    since = diff_since(repo, reviewed, head, pr_files)
    if isinstance(since, str):
        return Sent(diff, None, False, f"whole pull request, as the changes since {reviewed[:12]} are not available: {since}")
    since_diff, merged = since
    across = " across a merge of the base branch" if merged else ""
    return Sent(since_diff, reviewed, merged, f"changes since {reviewed[:12]}{across}")


def diff_since(repo: str, base: str, head: str, pr_files: set[str]) -> tuple[str, bool] | str:
    """The changes from base to head to the pull request's files as a unified diff, and whether a
    merge commit lies in between (it may bring in changes of the base branch to those files); or
    why the compare API cannot give them."""
    try:
        compare = json.loads(gh("api", f"repos/{repo}/compare/{base}...{head}"))
    except subprocess.CalledProcessError:
        return f"the compare API has no comparison of {base[:12]} with the head"
    if compare.get("status") not in ("ahead", "identical"):
        return f"the head does not descend from {base[:12]} (a rebase or a force-push)"
    commits, files = compare.get("commits", []), compare.get("files", [])
    if compare.get("total_commits", 0) > len(commits) or len(files) >= COMPARE_MAX_FILES:
        return "the comparison is longer than the compare API lists (250 commits, 300 files)"
    merged = any(len(c["parents"]) > 1 for c in commits)
    parts = []
    for f in files:
        if f["filename"] not in pr_files:
            continue
        if "patch" not in f:
            return f"the compare API gives no diff of {f['filename']}"
        old = f.get("previous_filename", f["filename"])
        parts.append(f"diff --git a/{old} b/{f['filename']}\n--- a/{old}\n+++ b/{f['filename']}\n{f['patch']}\n")
    return "".join(parts), merged


def system_blocks(prompt_file: Path, guideline_files: list[str]) -> list[dict]:
    """The review instructions and the repository's guidelines, which every review shares.

    They are cached for an hour, so that the re-review after a round of fixes reads them at a
    twentieth of the price.
    """
    guidelines = "\n\n".join(
        f"# Guidelines: {name}\n\n{Path(name).read_text()}" for name in guideline_files if Path(name).is_file()
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
    commits: list[dict],
    chunks: dict[str, str],
    views: dict[str, str],
    sent: Sent,
    lines: dict[str, set[int]],
    omitted: list[str],
    earlier: str,
) -> str:
    parts = [f"# Pull request: {pr['title']}\n\n{pr['body'] or '(no description)'}"]
    titles = "\n".join(f"{c['sha'][:12]} {c['commit']['message'].splitlines()[0]}" for c in commits)
    parts.append(f"# Commits of the pull request, oldest first\n\n{titles}")
    if sent.since is not None:
        files = "\n".join(f"{path}: {line_ranges(lines.get(path, set()))}" for path in (f["path"] for f in pr["files"]))
        parts.append(f"# Files the pull request changes, with the lines it changes or keeps as context\n\n{files}")
        note = (
            "\n\nThe commits since include a merge of the base branch, so a change below may come from the base"
            " branch rather than from this pull request; the whole pull request is in its files above."
            if sent.merged
            else ""
        )
        parts.append(f"# The changes below are those since the commit the latest review saw ({sent.since}){note}")
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
        tools=[grep, list_files, read_file, commit_diff, *([grep_std, read_std] if STD_ROOT else [])],
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


def review_payload(
    review: Review, head_sha: str, lines: dict[str, set[int]], pr_paths: set[str], omitted: list[str], record: str
) -> tuple[dict, list[dict]]:
    """The review as the API creates it, with its comments on changed lines, and its comments on
    changed files whose line is not part of the diff. A comment on a file the pull request does not
    change goes onto the first changed file with a diff, or into the body when there is none."""
    inline = [c for c in review.comments if c.line in lines.get(c.path, set())]
    on_file = [c for c in review.comments if c not in inline and c.path in pr_paths]
    outside = [c for c in review.comments if c not in inline and c not in on_file]
    anchor = min(lines, default=None)
    moved: list[dict] = []
    body = [f"{REVIEW_HEADING}\n\n{review.summary}"]
    if anchor:
        # A file the pull request does not change takes no comment: the finding becomes a comment
        # on a changed file, so that it has a thread to reply in and the freshness check sees it.
        moved = [{"path": anchor, "body": comment_text(c, f"(about `{c.path}:{c.line}`, which this pull request does not change) ")} for c in outside]
        outside = []
    body += [f"- `{c.path}:{c.line}`: {comment_text(c)}" for c in outside]
    if omitted:
        body.append("Not reviewed (not text): " + ", ".join(f"`{p}`" for p in omitted))
    # Kept with the review, where the API can read it back after the run's log has expired.
    body.append(f"<!-- usage: {record.replace('--', '- -')} -->")
    payload = {
        "commit_id": head_sha,
        "body": "\n\n".join(body),
        "comments": [{"path": c.path, "line": c.line, "side": "RIGHT", "body": comment_text(c)} for c in inline],
    }
    return payload, [{"path": c.path, "body": comment_text(c, f"(line {c.line}) ")} for c in on_file] + moved


def comment_text(comment: Comment, line_note: str = "") -> str:
    return f"[{comment.severity}, {comment.aspect}] {line_note}{comment.body}"


ADD_FILE_THREAD = """
mutation($review: ID!, $path: String!, $body: String!) {
  addPullRequestReviewThread(input: {pullRequestReviewId: $review, path: $path, body: $body, subjectType: FILE}) {
    thread { id }
  }
}
"""


def delete_pending_reviews(repo: str, pr: str) -> None:
    """Deletes the bot's pending reviews of the pull request: GitHub allows one per user, and a run
    cut off between creating and submitting a review would otherwise block every later run."""
    for r in gh_api_items(f"repos/{repo}/pulls/{pr}/reviews"):
        if r["user"]["login"] == REVIEW_AUTHOR and r["state"] == "PENDING":
            gh("api", f"repos/{repo}/pulls/{pr}/reviews/{r['id']}", "--method", "DELETE")


def create_review(repo: str, pr: str, payload: dict) -> dict:
    created = subprocess.run(
        ["gh", "api", f"repos/{repo}/pulls/{pr}/reviews", "--method", "POST", "--input", "-"],
        input=json.dumps(payload), check=True, capture_output=True, text=True,
    )
    return json.loads(created.stdout)


def post_review(repo: str, pr: str, payload: dict, file_comments: list[dict]) -> None:
    """Posts the review. Without file comments it is created and submitted in one call. With them
    it is created pending with its line comments, given its file comments through the GraphQL API
    (the REST API takes none in a review), then submitted, also when a file comment fails. If the
    submission fails, the pending review is deleted before the error is raised."""
    delete_pending_reviews(repo, pr)
    if not file_comments:
        print(create_review(repo, pr, {**payload, "event": "COMMENT"})["html_url"])
        return
    review = create_review(repo, pr, payload)
    try:
        try:
            for c in file_comments:
                gh("api", "graphql", "-f", f"query={ADD_FILE_THREAD}", "-f", f"review={review['node_id']}", "-f", f"path={c['path']}", "-f", f"body={c['body']}")
        finally:
            events = f"repos/{repo}/pulls/{pr}/reviews/{review['id']}/events"
            print(gh("api", events, "--method", "POST", "-f", "event=COMMENT", "-f", f"body={payload['body']}", "--jq", ".html_url"))
    except BaseException:
        delete_pending_reviews(repo, pr)
        raise


def sent_record(sent: Sent, prompt: str, system: list[dict], views: dict[str, str], whole: set[str], chunks: dict[str, str]) -> str:
    """What a review is sent, for the usage record and the dry run."""
    system_chars = sum(len(block["text"]) for block in system)
    return (
        f"sent {sent.note}; prompt {len(prompt)} chars, system {system_chars} chars;"
        f" files whole {len(whole)}, in excerpts {len(views) - len(whole)}, as diff {len(chunks) - len(views)}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", required=True)
    parser.add_argument("--pr", required=True)
    parser.add_argument("--prompt", required=True, type=Path)
    parser.add_argument("--head", required=True, type=Path)
    parser.add_argument("--model", default="claude-opus-5-5")
    parser.add_argument("--guidelines", nargs="+", default=GUIDELINE_FILES)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--dry-run", action="store_true")
    mode.add_argument("--print", action="store_true")
    args = parser.parse_args()
    global REPO_ROOT, REPO, PR_COMMITS
    REPO_ROOT, REPO = args.head.resolve(), args.repo

    pr = json.loads(gh("pr", "view", args.pr, "-R", args.repo, "--json", "title,body,headRefOid,files"))
    checked_out = git("rev-parse", "HEAD").strip()
    if checked_out != pr["headRefOid"]:
        sys.exit(f"the pull request moved from {checked_out} to {pr['headRefOid']} after the checkout; run again")
    commits = gh_api_items(f"repos/{args.repo}/pulls/{args.pr}/commits")
    PR_COMMITS = [c["sha"] for c in commits]
    diff = gh("pr", "diff", args.pr, "-R", args.repo)
    lines = commentable_lines(diff)
    earlier, reviewed, new_reply = earlier_reviews(args.repo, args.pr)
    if reviewed == pr["headRefOid"] and not new_reply:
        print(f"nothing new since the review of {reviewed}: no commit and no reply")
        return
    paths = {f["path"] for f in pr["files"]}
    sent = what_to_send(args.repo, reviewed, pr["headRefOid"], paths, diff)
    chunks = file_diffs(sent.diff)
    views, whole, omitted = changed_file_views(chunks, args.guidelines, sent.since is not None)
    prompt = build_prompt(pr, commits, chunks, views, sent, lines, omitted, earlier)
    system = system_blocks(args.prompt, args.guidelines)
    record = sent_record(sent, prompt, system, views, whole, chunks)

    if args.dry_run:
        print(f"model: {args.model}\n{record}\nearlier reviews: {len(earlier)} chars")
        print("whole:", *whole, sep="\n  ")
        print("in excerpts:", *(p for p in views if p not in whole), sep="\n  ")
        print("as diff:", *(p for p in chunks if p not in views), sep="\n  ")
        print("omitted:", *omitted, sep="\n  ")
        print(f"\n# Earlier automated reviews\n\n{earlier}" if earlier else "no earlier review")
        return

    review, usage = request_review(anthropic.Anthropic(), args.model, system, prompt)
    payload, file_comments = review_payload(review, pr["headRefOid"], lines, paths, omitted, f"{usage}; {record}")
    if args.print:
        print(json.dumps({**payload, "file_comments": file_comments}, indent=2, ensure_ascii=False))
        return
    post_review(args.repo, args.pr, payload, file_comments)


if __name__ == "__main__":
    main()
