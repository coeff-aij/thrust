"""Review a pull request with the Claude API and post the result as one PR review.

The review points out places for the developers to check, as inline comments on the changed
lines. The system prompt, with the aspects to look at and what not to report, is a file each
repository keeps.

Usage: claude_review.py --repo OWNER/NAME --pr NUMBER --prompt FILE [--model MODEL]
                        [--dry-run | --print]

--dry-run fetches the pull request and prints what would be sent, without calling the API or
posting anything. --print calls the API and prints the review instead of posting it.
"""

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

import anthropic
from anthropic import beta_tool
from pydantic import BaseModel

GUIDELINE_FILES = ["AGENTS.md", "CLAUDE.md", "README.md"]
MAX_FILE_CHARS = 100_000
MAX_TOOL_CALLS = 20
MAX_TOOL_OUTPUT_CHARS = 20_000
REPO_ROOT = Path.cwd().resolve()

tool_calls = 0


class Comment(BaseModel):
    path: str
    line: int
    aspect: str
    certain: bool
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


def read_changed_files(paths: list[str]) -> tuple[dict[str, str], list[str]]:
    contents: dict[str, str] = {}
    omitted: list[str] = []
    for path in paths:
        file = Path(path)
        if not file.is_file():
            continue
        try:
            text = file.read_text()
        except UnicodeDecodeError:
            omitted.append(path)
            continue
        if len(text) > MAX_FILE_CHARS:
            omitted.append(path)
            continue
        contents[path] = text
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


def numbered_lines(path: str, start_line: int, end_line: int) -> str:
    file = (REPO_ROOT / path).resolve()
    if not file.is_relative_to(REPO_ROOT) or not file.is_file():
        return f"no file {path} in the repository"
    lines = file.read_text(errors="replace").splitlines()[start_line - 1 : end_line]
    return "\n".join(f"{n}: {line}" for n, line in enumerate(lines, start_line))


def build_prompt(pr: dict, diff: str, contents: dict[str, str], omitted: list[str]) -> str:
    parts = [f"# Pull request: {pr['title']}\n\n{pr['body'] or '(no description)'}"]
    for name in GUIDELINE_FILES:
        if Path(name).is_file():
            parts.append(f"# Guidelines: {name}\n\n{Path(name).read_text()}")
    parts.append(f"# Diff\n\n```diff\n{diff}\n```")
    for path, text in contents.items():
        parts.append(f"# File after the change: {path}\n\n```\n{text}\n```")
    if omitted:
        parts.append("# Changed files not included (too large or binary)\n\n" + "\n".join(omitted))
    return "\n\n".join(parts)


def request_review(client: anthropic.Anthropic, model: str, system: str, prompt: str) -> Review:
    runner = client.beta.messages.tool_runner(
        model=model,
        max_tokens=16000,
        system=system,
        messages=[{"role": "user", "content": prompt}],
        tools=[grep, list_files, read_file],
        max_iterations=MAX_TOOL_CALLS + 5,
        output_config={"effort": "high"},
        output_format=Review,
        betas=["server-side-fallback-2026-07-01"],
        fallbacks="default",
    )
    input_tokens = output_tokens = 0
    for message in runner:
        input_tokens += message.usage.input_tokens
        output_tokens += message.usage.output_tokens
    print(f"usage: {tool_calls} tool calls, input {input_tokens}, output {output_tokens} tokens", file=sys.stderr)
    response = runner.until_done()
    if response.stop_reason != "end_turn":
        sys.exit(f"no review: stop_reason {response.stop_reason}")
    return response.parsed_output


def review_payload(review: Review, head_sha: str, lines: dict[str, set[int]], omitted: list[str]) -> dict:
    inline = [c for c in review.comments if c.line in lines.get(c.path, set())]
    outside = [c for c in review.comments if c not in inline]
    body = [f"**Claude review** (automated)\n\n{review.summary}"]
    body += [f"- `{c.path}:{c.line}`: {comment_text(c)}" for c in outside]
    if omitted:
        body.append("Not reviewed (too large or binary): " + ", ".join(f"`{p}`" for p in omitted))
    return {
        "commit_id": head_sha,
        "event": "COMMENT",
        "body": "\n\n".join(body),
        "comments": [{"path": c.path, "line": c.line, "side": "RIGHT", "body": comment_text(c)} for c in inline],
    }


def comment_text(comment: Comment) -> str:
    label = comment.aspect if comment.certain else f"{comment.aspect}, to check"
    return f"[{label}] {comment.body}"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", required=True)
    parser.add_argument("--pr", required=True)
    parser.add_argument("--prompt", required=True, type=Path)
    parser.add_argument("--model", default="claude-opus-5-5")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--dry-run", action="store_true")
    mode.add_argument("--print", action="store_true")
    args = parser.parse_args()

    pr = json.loads(gh("pr", "view", args.pr, "-R", args.repo, "--json", "title,body,headRefOid,files"))
    diff = gh("pr", "diff", args.pr, "-R", args.repo)
    lines = commentable_lines(diff)
    contents, omitted = read_changed_files([f["path"] for f in pr["files"]])
    prompt = build_prompt(pr, diff, contents, omitted)

    if args.dry_run:
        print(f"model: {args.model}\nsystem: {args.prompt}\nprompt: {len(prompt)} chars")
        print("included:", *contents, sep="\n  ")
        print("omitted:", *omitted, sep="\n  ")
        print("commentable lines:", *(f"{p}: {len(n)}" for p, n in lines.items()), sep="\n  ")
        return

    review = request_review(anthropic.Anthropic(), args.model, args.prompt.read_text(), prompt)
    payload = review_payload(review, pr["headRefOid"], lines, omitted)
    if args.print:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
        return
    subprocess.run(
        ["gh", "api", f"repos/{args.repo}/pulls/{args.pr}/reviews", "--method", "POST", "--input", "-"],
        input=json.dumps(payload), check=True, text=True,
    )


if __name__ == "__main__":
    main()
