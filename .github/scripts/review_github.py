"""The automated reviews of a pull request and their comments, read with the GitHub CLI; shared by
claude_review.py, which writes the reviews, and review_freshness.py, which checks them."""

import json
import subprocess

REVIEW_HEADING = "**Claude review** (automated)"
REVIEW_AUTHOR = "github-actions[bot]"


def gh(*args: str) -> str:
    return subprocess.run(["gh", *args], check=True, capture_output=True, text=True).stdout


def gh_api_items(path: str) -> list[dict]:
    """The items of a paginated GitHub API list."""
    output = gh("api", "--paginate", path, "--jq", ".[]")
    return [json.loads(line) for line in output.splitlines()]


def automated_reviews(repo: str, pr: str) -> list[dict]:
    """The pull request's automated reviews, oldest first."""
    return [
        r
        for r in gh_api_items(f"repos/{repo}/pulls/{pr}/reviews")
        if r["user"]["login"] == REVIEW_AUTHOR and r["body"].startswith(REVIEW_HEADING)
    ]


def is_finding(comment: dict) -> bool:
    """Whether a review comment is a finding of the automated review rather than a reply."""
    return comment["user"]["login"] == REVIEW_AUTHOR and not comment.get("in_reply_to_id")
