# 外部トレイト impl のメソッドに仕様を書く (調査メモ)

対象: `/home/suuji-1024/Remotes/thrust/.claude/worktrees/rustc-coroutine`（read-only 調査）

## 1. なぜ companion が impl の中に入るのか / 外に出せるか

### 展開の形
`#[thrust_macros::ensures(..)]` は最終的に `spec::ExpandedTokens::expand()`
(`thrust-macros/src/spec.rs:382-425`) で **4 つの item を 1 つの TokenStream** として返す:

```
#func  #requires_fn  #ensures_fn  #[thrust::extern_spec_fn] fn _thrust_extern_spec_<name>(..)
```

attribute macro はメソッド（= impl item）位置に貼られているので、出力もその位置に
そのまま差し込まれる → 4 つ全部が impl item になる。`impl Trait for Ty` では全 fn が
トレイトのメンバでなければならないため E0407。実測（probe E,
`scratchpad/probe_e.rs`）: E0407 × 3（`_thrust_requires_next` /
`_thrust_ensures_next` / `_thrust_extern_spec_next`）+ E0599 × 2
（`Self::_thrust_requires_next` が見つからない）。

### companion が「同じ self 型の impl」を必要とする理由（自由関数では不足）
- companion の引数型は `Self` / `Self::Item` を **テキストのまま**残す
  (`thrust-macros/src/formula_fn_type_lowering.rs:100-165`, `receiver_type()`
  `thrust-macros/src/lib.rs:170-186`。`&mut self` → `Mut<<Self as Model>::Ty>` 相当)。
- マーカーのパスは `path_prefix()` = `Self::`（`spec.rs:377-380`）。
- `def_generics` はメソッド自身のジェネリクスのみ（`spec.rs:265-266`）で、impl の
  `<'a, T>` は「impl の中にいること」で継承している。

→ つまり **inherent impl（同じ self 型・同じジェネリクス）なら成立する**。自由関数に
出すなら `<'a, T>` の再宣言と `Self` の置換が必要。

### アナライザ側の要求（重要）
アナライザは「同じ impl の兄弟」や「名前」で companion を探していない。
`Analyzer::extract_path_with_attr` (`src/analyze.rs:803-847`) が
**ラッパ本体の先頭にある path 文** を読み、`typeck.qpath_res` で解決するだけ。
条件は 2 つだけ:
- 解決先が local def であること（`src/analyze.rs:856-870` は非 local で panic）
- その def に `#[thrust::formula_fn]` が付き `register_formula_fn` 済み
  (`src/analyze/crate_.rs:95-98`)

よって `Self::_thrust_ensures_next` でも自由関数でも inherent impl のメソッドでも
そのまま通る。**アナライザ変更は不要**（probe D/F/G が実証）。

## 2. `#[thrust::extern_spec_fn]` はローカルの外部トレイト impl を狙えるか → **狙える**

- ターゲット解決 `extern_spec_fn_target_def_id_impl`
  (`src/analyze/local_def.rs:50-105`): HIR の tail 式が `Call` + `Path` であることだけを
  要求し、`typeck.qpath_res` → `Instance::try_resolve`。`<BitIter<'a> as Iterator>::next(it)`
  のような qualified path はローカル impl メソッドの DefId に解決される。ラッパ自身は
  `Node::Item` / `ImplItem` / `TraitItem` のいずれでもよい（同 56-77 行）。
- 登録: `refine_local_defs` (`src/analyze/crate_.rs:73-82`) はターゲットが local なら
  そのキーを `keys` から外し（＝ターゲット自身のシグネチャ由来の型は作らない）、
  ラッパ側が `owner_fn_id = target_def_id` として登録する
  (`local_def.rs:1272-1275`, `crate_.rs:137-152`)。ターゲットが AssocFn の場合は
  ラッパを先に refine する（`trait_method_spec_keys`）。
- 呼び出し側: `resolve_callable` / `callable_ty` (`src/analyze/basic_block.rs:903-988`)。
  `r.next()` は `Instance::try_resolve` で impl メソッドの DefId になり、
  `def_ty_with_args` が `defs[target_def_id]` = extern spec の契約を引く。
- **本体は置き換えではなく検査される**: `skip_analysis` に入るのはラッパだけ
  (`crate_.rs:119-122`)。`analyze_local_defs` (`crate_.rs:156-`) は残りの mir_keys を
  全部回すので、impl の `next` 本体は登録された契約に対して検証される。

### 実験（実行済み。`cargo run --quiet -- -Adead_code -C debug-assertions=off`,
`THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest`）

| probe | 内容 | 結果 |
|---|---|---|
| A `scratchpad/probe_a.rs` | 自由 fn の extern spec が `<R as Iterator>::next` を tail call、`main` で `r.next()` 後に `r.n == 1` を assert | **pass**（呼び出し側で仕様が使われる） |
| B `probe_b.rs` | 同じだが ensures を `+2` に改悪、assert も `== 2` | **Unsat** |
| C `probe_c.rs` | ensures `+2`、呼び出し無し（main 空） | **Unsat**（＝ 本体が契約に対して検査されている、trusted ではない） |
| D `probe_d.rs` | 仕様を **兄弟の inherent impl** に置く: `#[thrust_macros::context] impl R { #[thrust::extern_spec_fn] #[requires/ensures] fn _thrust_extern_spec_next(&mut self) -> Option<i64> { <R as Iterator>::next(self) } }` | **pass** |
| F `probe_f.rs` | D をライフタイム付き `BitIter<'a>` に | **pass** |
| G `probe_g.rs` | D を型パラメタ付き `BitIter<T>` に（`where <T as Model>::Ty: PartialEq` が必要。無いと E0277） | **pass** |

制約: 静的ディスパッチ限定。`I: Iterator` 越しの呼び出しは `Instance::try_resolve` が
解決できず `abstract_callable_ty` (`basic_block.rs:994-`) に落ちる。
また仕様式に `Option` のペイロードを書くとモデル型が `Option<Int>` になり
`Some((*it).n)`（`i64`）は E0308。`Self::Item` 系の式を書くときは要注意。

## 3. 最小の変更案

**アナライザは触らない。`context` マクロだけを直す。**
`context::expand_outer` (`thrust-macros/src/context.rs:60-88`) は既に impl ヘッダ
（self 型・ジェネリクス・where・関連型）を持ち、items を書き換えている。ここで
`FnOuterItem::ItemImpl` かつ `trait_.is_some()` の場合に限り:

1. 各メソッドから `requires`/`ensures`（と `_requires_ensures`）属性を剥がす
2. impl の兄弟として `impl <generics> <self_ty> <where>` を 1 つ生成し、その中に
   メソッドごとに
   ```rust
   #[thrust::extern_spec_fn]
   #[thrust_macros::requires(..)] #[thrust_macros::ensures(..)]
   fn _thrust_extern_spec_<name>(<元のシグネチャ>) -> R { <SelfTy as Trait>::<name>(args) }
   ```
   を置く（`Self::Item` は impl の `type Item = ..` の右辺に置換。inherent impl には
   関連型を書けないため、この置換が唯一の面倒な点。`into_header_only` が関連型を
   保持しているので情報は揃っている）

生成物が再び `thrust_macros::requires/ensures` 付きなので、既存の
`expand_extern_spec_fn` (`spec.rs:427-470`) が `Self::` 前置きの companion を
inherent impl 内に作る ＝ probe D/F/G の手書き形に一致し、そのまま検証が通る。
規模は context.rs に ~40 行程度。

代替（コード 0 行）: probe D の書き方を `docs/annotations/14-extern-spec-fn.md` に
「外部トレイト impl の仕様はこう書く」として明記する。上の変更前でも今日使える。

### 追加するテスト 2 組
1. `tests/ui/pass/traits/std_iterator_impl_spec.rs`（`//@check-pass`）
   probe D 相当: `impl Iterator for R` に対し、`context` 付き `impl Iterator for R` に
   直接 `requires`/`ensures` を書き、`main` で `r.next()` 後の状態を assert。
   fail 双子 `tests/ui/fail/std_iterator_impl_spec.rs`（`//@error-in-other-file: Unsat`）
   は ensures を `(!self).n == (*self).n + 2` に（本体が仕様を満たさない側を突く）。
2. `tests/ui/pass/traits/std_add_impl_spec.rs`（`//@check-pass`）
   `impl std::ops::Add for Size { fn add }` に `ensures(result.0 == self.0 + rhs.0)`。
   fail 双子は呼び出し側の assert を 1 ずらす（仕様が呼び出し側に届いていることを固定）。

いずれも `//@compile-flags: -C debug-assertions=off` と
`//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest` が必要。
