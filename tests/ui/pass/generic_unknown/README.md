# Generic unknowns read at instances

Under `THRUST_GENERIC_UNKNOWN_PREDS=1` (a prototype; see the README's Configuration), a derived
predicate read at type parameters is one unknown verified once over them, and each concrete
instance is tied to it (`src/chc/instance_tie.rs`). Fail twins are in
`../../fail/generic_unknown/`.

| file | what it shows | state |
| --- | --- | --- |
| `take.rs` | `creusot/take` with `Take<I>::produces` left out, verified once over `I`, read at `Take<Range>` | verifies; the fail twin (an item `Range` never yields first) is refuted |
| `count.rs` | the running example with `count`'s contract written through two derived generic predicates without bodies | verifies, `count` analyzed once; the fail twin (a closure rejecting the range's first item) is refuted |
