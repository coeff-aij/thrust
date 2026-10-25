# AGENTS.md

Everything about the project itself is documented for humans, starting from `README.md`;
read it, the Development section in particular, rather than looking for it here. This file
records only what is easy to get wrong.

## Adding test cases

UI tests live in `tests/ui/`.

Add a test as a pair of files sharing one name: `tests/ui/pass/<name>.rs` headed by
`//@check-pass`, and `tests/ui/fail/<name>.rs` headed by `//@error-in-other-file: Unsat`.
The `fail` file is the `pass` file with the verified property broken as narrowly as
possible, so that the pair pins down both directions of the check.

Do not add tests merely to cover every changed code path or fixed bug. Add a test only
when it protects behavior that could plausibly regress without an obviously incorrect
code change. Similar implementations do not each need separate tests when one
representative case sufficiently exercises the behavior.

## Specifications in `std.rs`

`std.rs` is injected into every crate Thrust verifies, so a specification there must be
general: it states the function's behaviour faithfully and serves every call site.
A weaker contract that only one proof needs goes in that test's own file, as an extern-spec
wrapper or a local trusted helper, not in `std.rs`.

## Comments

Fewer comments are better. A code comment means the code itself isn't self-explanatory
and should be rewritten if possible.

## Panics on unsupported input

Thrust is under active development, and it is fine for an unsupported or unexpected
construct to reach a `panic!`, an `unimplemented!`, or a failing `unwrap`. Reporting one as
a proper diagnostic instead is fine too. What is not wanted is working around an existing
ICE path: validation passes, `Result` plumbing, or extra layers of processing added only to
keep from reaching it.

## Running the tests on claude.ai/code

Neither prerequisite of `cargo test` is set up in the session container. Install Z3 at the
version `.github/actions/setup-z3` pins for CI.

Without Docker the ui tests that name a CoAR wrapper cannot run; set `THRUST_UI_SKIP_COAR=1`,
as CI does, to run the others.

## Automated review

`.github/workflows/claude-review.yml` reviews a pull request with the Claude API (README, CI).
When developing with an agent, use it as a loop at the points where a coherent set of commits
is pushed, not after every commit:

1. Request a review with `gh pr comment <n> --body /claude-review` and wait for the run
   (`gh run list -w claude-review.yml -L 1`, then `gh run watch <id>`).
2. Read the newest review and its inline comments:
   `gh api repos/{owner}/{repo}/pulls/<n>/reviews --jq '.[-1] | {id, body}'` and
   `gh api repos/{owner}/{repo}/pulls/<n>/reviews/<id>/comments --jq '.[] | {id, path, line, body}'`.
3. Fix what holds. Answer a comment you do not act on with the reason, as a reply to it
   (`gh api repos/{owner}/{repo}/pulls/<n>/comments/<id>/replies -f body=...`); the next review
   reads the replies and does not repeat a comment they settle.
4. Request again. Stop when a review raises nothing new, or after three rounds, and leave what
   remains to a person.
