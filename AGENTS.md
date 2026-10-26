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
Each comment is marked `blocking`, `check` or `suggestion`.

The review reads the diff and the code around it and runs nothing. It covers what reading
shows: agreement with the README and this file, design and maintainability, a soundness gap
visible in the code, a test that does not check what it says, at a small fraction of what an
agent's audit costs (each review records its tokens). What needs Thrust or the solver to run
stays with the developer and is not delegated to the review:

- the ui tests the change affects, run locally, including those that name a CoAR wrapper;
- for a change to the analysis or the emitted constraints, an audit by an agent that did not
  write the change: it compares the design with how other verifiers handle the case, writes
  probe programs that try to make Thrust accept a wrong program, and runs them;
- before the merge of such a change, a full `cargo test --test ui` with the CoAR wrappers.

Without Docker (claude.ai/code), the CoAR runs go to the person who merges; say in the pull
request which of them did not run.

When developing with an agent, use the review as a loop at the points where a coherent set of
commits is pushed, not after every commit; a run with no new commit and no new reply stops
before calling the API. An audit runs alongside the loop or after it, and its fixes go through
the next round:

1. Request a review with `gh workflow run claude-review.yml -f pr=<n>` and wait for the run
   (`gh run list -w claude-review.yml -L 1`, then `gh run watch <id>`).
2. Read the reviews and the comments with their replies:
   `gh api repos/{owner}/{repo}/pulls/<n>/reviews --paginate --jq '.[] | {id, commit_id, body}'` and
   `gh api repos/{owner}/{repo}/pulls/<n>/comments --paginate --jq '.[] | {id, in_reply_to_id, user: .user.login, path, line, body}'`.
3. Check each open comment against the code before acting on it; the reviewer can be wrong.
   Fix a `blocking` comment that holds, confirm or refute a `check`, and take a `suggestion`
   only when it is small and inside the change. Do not edit code outside the change only to
   satisfy a comment. With many comments, give each to its own subagent.
4. Reply to every comment, so the next review knows how it was settled:
   `gh api repos/{owner}/{repo}/pulls/<n>/comments/<id>/replies -f body='Fixed in <commit>'`,
   or `Declined: <reason>`, or `Refuted: <evidence>`.
5. Push and request again. Stop when a review raises no open `blocking` or `check` comment, or
   after three rounds, and leave what remains, the CoAR runs that could not run, and the merge,
   to a person.
