# 調査メモ: Thrust の ICE 2 件（原因と修正案）

対象ブランチ rustc-coroutine（iterator-adapters + forall-sort）。読み取りのみの調査結果。
再現ファイルと検証用パッチはスクラッチ領域に置いたので、修正ブランチ側で再作成する。

## ICE 1: `unknown type param idx`（src/refine/template.rs:145, `TypeBuilder::param_local_idx`）

再現（いずれも exit 101）:

```rust
#[derive(Clone, Copy)] enum Tag<V> { A(V), B }
#[derive(Clone)] enum Var<F, V> { X(F), Y { t: Tag<V>, items: Vec<F> } }
```

- 呼び出し側が impl でなくても再現: `fn dup<F, V: Copy>(_f: F, t: Tag<V>) -> Tag<V> { t.clone() }`
- Tag の Clone が手書きでも再現。derive は無関係。
- 再現しない: 呼び出し側の型パラメタが 1 個だけ（`fn dup<V>(t: Tag<V>)`）、または
  トレイトメソッドに仕様が無い場合。

経路（backtrace と debug ログで確認）:

1. basic_block.rs:961 の 2 回目の `def_ty_with_args(resolved_def_id, resolved_args, caller)`。
   resolved は `{impl#0}::clone`（Tag の impl）、args は `[V/#1]`（呼び出し側 `{impl#2}::clone` の
   パラメタ）。1 回目（trait method `Clone::clone`）は成功する。
2. analyze.rs:593-596 → local_def.rs:461 `expected_ty` → `trait_item_ty`（impl 側に仕様が無いため）。
3. **local_def.rs:298-302 `trait_item_ty` が `caller_def_id` に `self.local_def_id`（= impl メソッド）を
   渡している**が、`trait_item_args`（`[Tag<V/#1>]`）は本来の owner（`{impl#2}::clone`）のパラメタで
   表現されている。
4. 結果、`TypeBuilder` が impl メソッド用（`param_idx_mapping {0: T0}`）に作り直され、`V/#1` の
   変換で index 1 が見つからず panic。

原因: `trait_item_ty` だけが owner ではなくメソッドを caller として使っている。同じ
`trait_item_args` を扱う local_def.rs:437-440 は `self.owner_fn_id` を使っており、ここが不整合。
`git log -L` では ca53188（2026-08-31「Use the method as caller_def_id for trait item types」、
理由の記述なし）で impl からメソッドに変えられている。

修正案（スクラッチで検証済み、再現 5 件すべて exit 0）: local_def.rs:298-302 で
`self.local_def_id.to_def_id()` の代わりに `self.owner_fn_id` を渡す。直接 `refine_fn_def` から
来る場合は `owner_fn_id == local_def_id` なので挙動は変わらない。InstantiationKey が owner ごとに
分かれるためキャッシュ項目は増える。

## ICE 2: `unbound var $0`（src/chc/clause_builder.rs:113, `mapped_var`）

再現（いずれも exit 101）:

```rust
#[derive(PartialEq)] struct S<T> { n: i64, m: PhantomData<T> }   // a == b
#[derive(Clone)]     struct S<T> { n: i64, m: PhantomData<T> }   // a.clone()
#[derive(PartialEq)] struct U;  struct W { u: U }                 // ジェネリック・PhantomData 不要
```

経路:

1. annot_fn.rs:230-247 `build_env_from_params`: formula_fn の引数 `$0` の HIR 型は
   `<PhantomData<T> as Model>::Ty`。PhantomData（やユーザ ZST）に Model impl が無いので
   template.rs:190-221 `translate_alias_type` が正規化できず forall sort を発行する。
   `Sort::Forall` は singleton でないので `$0` は変数として式に残る。
2. local_def.rs:414-489 `expected_ty` は MIR シグネチャから同じ引数を `&immut ()`（singleton）と
   して構築する。
3. basic_block.rs:301-305 `relate_fn_sub_type` は singleton の引数を `add_mapped_var` しない。
   その後 :225-228 で ensures の式を `add_body` すると rty/clause_builder.rs:69 の
   `mapped_var($0)` が失敗する。

原因: singleton sort の変数は節変数にしない規約（rty/subtyping.rs:128-133, :205-210、
crate_.rs:246、refine/env.rs:988-995）に対し、annot_fn 側の singleton 判定は Model::Ty の射影で
行うため、射影が正規化できない場合にシグネチャ側の sort と食い違う。

修正案（スクラッチで検証済み、再現 3 件すべて exit 0、traits/ テスト 27 件の結果は不変）:
`FunctionTemplateTypeBuilder::build`（template.rs:1047）で FunctionType を組んだ後、
param sort が singleton の `Free(idx)` を `chc::Term::default_for(&sort)` で置換する
（`RefinedType::subst_var`、rty.rs:1769）。約 35 行。

代替案:
- A: `chc::ClauseBuilder` に変数→項の対応（`add_mapped_term`）を持たせ、4 箇所の
  `add_mapped_var` と `RefinementClauseBuilder::add_body/head` で使う。annot_fn の特別扱いを
  無くせるが変更範囲が広い（annot_fn.rs:243-244 の FIXME の方向）。
- B: std.rs に `impl<T: ?Sized> Model for PhantomData<T> { type Ty = (); }`。PhantomData だけ直る。
