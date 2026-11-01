"""Check that the automated review of a pull request is up to date, without the Claude API.

The check fails when the pull request changes a watched file whose content at the head differs from
the commit the latest automated review saw (or when no review saw it), and when a `blocking` or
`check` comment of the automated review has no reply. Contents are compared, not commits, so a
rebase or a force-push counts as a change.

Usage: review_freshness.py --repo OWNER/NAME --pr NUMBER --head SHA --watch PATH [PATH...]

A watched PATH is a file, or a directory when it ends with `/`. The script reads the pull request
through the GitHub API only and runs none of its code.
"""

import argparse
import json
import subprocess
import sys

from review_github import automated_reviews, gh, gh_api_items, is_finding

OPEN_SEVERITIES = ("[blocking", "[check")


def watched(path: str, watch: list[str]) -> bool:
    return any(path.startswith(w) if w.endswith("/") else path == w for w in watch)


def pr_paths(repo: str, pr: str) -> list[str]:
    """The paths the pull request changes, with the old path of a renamed file."""
    paths = []
    for f in gh_api_items(f"repos/{repo}/pulls/{pr}/files"):
        paths.append(f["filename"])
        if f.get("previous_filename"):
            paths.append(f["previous_filename"])
    return paths


def blobs(repo: str, sha: str) -> dict[str, str] | None:
    """The blob of each file in the commit's tree, or None when the commit cannot be read."""
    try:
        tree = json.loads(gh("api", f"repos/{repo}/git/trees/{sha}?recursive=1"))
    except subprocess.CalledProcessError:
        return None
    if tree.get("truncated"):
        sys.exit(f"the tree of {sha} is too large for one API call")
    return {e["path"]: e["sha"] for e in tree["tree"] if e["type"] == "blob"}


def unseen_changes(repo: str, pr: str, head: str, watch: list[str]) -> str | None:
    """Why the latest automated review has not seen the pull request's watched files at head, or
    None when it has."""
    paths = [p for p in pr_paths(repo, pr) if watched(p, watch)]
    if not paths:
        return None
    reviews = automated_reviews(repo, pr)
    if not reviews:
        return "No automated review yet; the pull request changes:\n" + "\n".join(f"  {p}" for p in paths)
    reviewed = reviews[-1]["commit_id"]
    before, after = blobs(repo, reviewed), blobs(repo, head)
    if before is None:
        return f"The commit the latest review saw, {reviewed}, can no longer be read."
    changed = [p for p in paths if before.get(p) != after.get(p)]
    if not changed:
        return None
    lines = "\n".join(f"  {p}" for p in changed)
    return f"Changed since the commit the latest review saw ({reviewed}):\n{lines}"


def unanswered(repo: str, pr: str) -> list[str]:
    """The `blocking` and `check` comments of the automated review that have no reply."""
    comments = gh_api_items(f"repos/{repo}/pulls/{pr}/comments")
    answered = {c["in_reply_to_id"] for c in comments if c.get("in_reply_to_id")}
    return [
        f"  {c['html_url']} ({c['path']}{':' + str(c['line']) if c.get('line') else ''})"
        for c in comments
        if is_finding(c) and c["body"].startswith(OPEN_SEVERITIES) and c["id"] not in answered
    ]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", required=True)
    parser.add_argument("--pr", required=True)
    parser.add_argument("--head", required=True)
    parser.add_argument("--watch", required=True, nargs="+")
    args = parser.parse_args()

    problems = []
    unseen = unseen_changes(args.repo, args.pr, args.head, args.watch)
    if unseen:
        problems.append(
            f"{unseen}\nThe automated review watches {' '.join(args.watch)}. Request a review with"
            f" `gh workflow run claude-review.yml -R {args.repo} -f pr={args.pr}`; this check runs"
            " again when it is posted."
        )
    open_comments = unanswered(args.repo, args.pr)
    if open_comments:
        problems.append(
            "Comments marked blocking or check without a reply:\n" + "\n".join(open_comments) + "\nReply to each"
            " with `Fixed in <pushed sha>: <what changed, path:line>`, `Declined: <reason>` or"
            " `Refuted: <evidence>`; a reply runs this check again."
        )
    if not problems:
        print("The latest automated review saw the watched files at this head, and every blocking or check comment has a reply.")
        return
    for problem in problems:
        print(f"::error::{problem.splitlines()[0]}")
    sys.exit("\n\n".join(problems))


if __name__ == "__main__":
    main()
