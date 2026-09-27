# Reproduction bundles for upstream reports

Each directory is self-contained: symptom, reproduction, and (where one exists) a fix or its
current state, with no reference to anything outside this repository's tracked history.

| directory | topic | relates to |
| --- | --- | --- |
| [`thrust-macros-dylib/`](thrust-macros-dylib/README.md) | the driver can link a stale `thrust-macros` proc-macro dylib when more than one build of it exists under `target/debug/deps` | no open upstream issue; distinct from #255 (multi-crate support) |
| [`ghost-field-contents/`](ghost-field-contents/README.md) | a `Ghost<T>` struct field could not be used as its contents in `ensures`/`ghost!`, only a `Ghost<T>` parameter could (fixed on this fork) | no open upstream issue |
| [`unsigned-nonneg/`](unsigned-nonneg/README.md) | unsigned integer types carry no non-negativity fact, so a `usize` can be proved negative (this fork carries a provisional, narrower fix) | upstream #277 (unsigned constants only) and the unmerged `claude/vibrant-brown-tjmb6h-*` branches (a general range/wrapping fix in progress) |

Two other topics have their own pushed branches rather than a directory here, because each
predates this branch and already carries its own commit history:

- `itermut-alias-repro` -- a `&mut` prophecy aliased across a drop point verifies a false claim;
  checked against upstream #250, #207, #215 and #210 (none match; see that branch's
  `repro/itermut-alias/README.md`).
- `kemkem-frontend-repro` -- frontend constructs (from an ML-KEM implementation) that stop the
  driver before analysis; see that branch's `repro/kemkem-frontend/README.md`.
