"""Review a pull request with the Claude API and post the result as one PR review.

The review points out places for the developers to check, on soundness, theory, usability and
maintainability, as inline comments on the changed lines. What not to report follows the
code-review plugin of anthropics/claude-code.

Usage: claude_review.py --repo OWNER/NAME --pr NUMBER [--model MODEL] [--dry-run]

--dry-run fetches the pull request and prints what would be sent, without calling the API or
posting anything.
"""

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Literal

import anthropic
from pydantic import BaseModel

GUIDELINE_FILES = ["AGENTS.md", "CLAUDE.md", "README.md"]
MAX_FILE_CHARS = 100_000

SYSTEM_PROMPT = """\
You review a pull request to Thrust, a refinement-type verifier for Rust built as a rustc
driver that emits CHC constraints. You get the pull request description, the repository's
guidelines and user documentation, the diff, and the full post-change contents of the changed
files.

Point out the places a developer should look at; the developers confirm and fix them. Look at
four aspects:
- soundness: an encoding or a shortcut that could let a wrong program verify, or a case the
  change silently drops;
- theory: a change to the encoding or the type system whose justification is missing or does
  not follow from the known formulations (RustHorn-style prophecies, refinement types, CHC);
- usability: a change in what users write or see (annotations, diagnostics, configuration)
  that is confusing, undocumented in the README, or breaks existing usage;
- maintainability: duplicated logic, a special case that belongs in an existing mechanism,
  or a violation of the repository guidelines (quote the rule).

Do not report pre-existing issues, formatting, things rustfmt, clippy or the compiler catch,
or nitpicks a senior engineer would not raise. Include an issue you are unsure of when it
would matter if real, and say what would confirm it. Reporting nothing is a good outcome.

Each comment names one issue on one changed line of the new version of a file (`path` as in
the diff, `line` as a line number in the new file) and says briefly what may be wrong and why.
The summary is two or three sentences on the overall change and the most important concern.
"""


class Comment(BaseModel):
    path: str
    line: int
    aspect: Literal["soundness", "theory", "usability", "maintainability"]
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


def request_review(client: anthropic.Anthropic, model: str, prompt: str) -> Review:
    response = client.beta.messages.parse(
        model=model,
        max_tokens=16000,
        system=SYSTEM_PROMPT,
        messages=[{"role": "user", "content": prompt}],
        output_config={"effort": "high"},
        output_format=Review,
        betas=["server-side-fallback-2026-07-01"],
        fallbacks="default",
    )
    usage = response.usage
    print(f"usage: input {usage.input_tokens}, output {usage.output_tokens} tokens", file=sys.stderr)
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
    parser.add_argument("--model", default="claude-opus-5-5")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    pr = json.loads(gh("pr", "view", args.pr, "-R", args.repo, "--json", "title,body,headRefOid,files"))
    diff = gh("pr", "diff", args.pr, "-R", args.repo)
    lines = commentable_lines(diff)
    contents, omitted = read_changed_files([f["path"] for f in pr["files"]])
    prompt = build_prompt(pr, diff, contents, omitted)

    if args.dry_run:
        print(f"model: {args.model}\nprompt: {len(prompt)} chars")
        print("included:", *contents, sep="\n  ")
        print("omitted:", *omitted, sep="\n  ")
        print("commentable lines:", *(f"{p}: {len(n)}" for p, n in lines.items()), sep="\n  ")
        return

    review = request_review(anthropic.Anthropic(), args.model, prompt)
    payload = review_payload(review, pr["headRefOid"], lines, omitted)
    subprocess.run(
        ["gh", "api", f"repos/{args.repo}/pulls/{args.pr}/reviews", "--method", "POST", "--input", "-"],
        input=json.dumps(payload), check=True, text=True,
    )


if __name__ == "__main__":
    main()
