# Frontend gaps found in an ML-KEM implementation

Minimal inputs for the Rust constructs that stop Thrust on
[kemkem](https://github.com/conorpo/kemkem) (fe13ec5), before its external crates
(`bitvec`, `rand`, `sha3`) come into play. Each file reduces one construct the crate uses throughout.

Run each file with:

```sh
thrust-rustc -Adead_code -Aunused -C debug-assertions=false <file>.rs
```

The results below were observed on 74f503f with the default solver (z3).

| File | kemkem construct | Result |
|---|---|---|
| `u16_model.rs` | `u16` coefficients, `u8` bytes | panic: `unrefined_ty: u16` (no `Model` for `u8`/`u16`) |
| `int_cast.rs` | `x as u32` around every reduction | panic: `rvalue=copy _1 as u64 (IntToInt)` |
| `rem.rs` | `% Q` | panic: `ty=int, op=Rem` (#144) |
| `shl.rs` | `<<`, `>>`, `&`, `\|` | panic: `ty=int, op=Shl` |
| `for_range.rs` | `for i in 0..256` | panic: `unknown def (resolved): ..::into_iter`, `Range<i32>` |
| `array_index_local.rs` | `a[i]` on `[T; N]` | panic: `place.projection.last() == Some(&Deref)` |
| `array_index_field.rs` | `self.data[i]` on a `[u16; 256]` field | same panic |
| `array_repeat.rs` | `[0; 256]` | panic: `rvalue=[const 0_i32; 4]` |
| `static_ref.rs` | `static` tables | panic: `const ptr alloc: Static(..)` |
| `partialeq_non_structural.rs` | `impl PartialEq for Ring` that compares `data` and ignores the representation tag | `Unsat`, although the assertion holds (#225) |
| `partialeq_non_structural_unused.rs` | the same impl, never called | `Unsat` (#225) |
| `const_generic_method.rs` | `impl<const K: usize> Vector<K>` | verifies here; on `forall-sort` it hits the `unimplemented!()` for const parameters in `placeholder_generic_args` |

`array_index_field.rs` and both `partialeq_*` files declare `impl Model for Ring`. Without it,
they stop earlier on #266. `const_generic_method.rs` avoids array indexing so that the const
parameter is the only construct under test.
