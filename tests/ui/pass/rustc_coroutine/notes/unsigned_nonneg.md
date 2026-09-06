# 符号なし型への `>= 0` 篩 導入調査メモ

worktree: `.claude/worktrees/rustc-coroutine`。read-only 調査、~30分タイムボックス。

先行メモ(事実): `tests/ui/pass/rustc_coroutine/notes/cast_design.md` に同じ問題意識が既にある。
「Thrust は符号なし型に `>= 0` の篩を付けていない (`src/refine/template.rs:319,708` は無条件に
`rty::Type::int()` を返す)」「`assert!(idx <= u32::MAX as usize)` の後で `idx as u32 == idx` は
`0 <= idx` が無いと証明できない」とあり、テスト案 `cast_bound_check.rs` も構想済み。本調査はこの
前提の裏取りと設計具体化。

## 1. 導入箇所の候補

### (a) `build()` で MIR 型を見る — 不可
`src/refine/template.rs` の `build()`(347行, 735行)は1行目で
`let ty = self.resolve_model_ty(ty);`(348行/736行)により引数 `ty` を shadow する。
`resolve_model_ty`(279行、`<T as Model>::Ty` を正規化)は `usize`/`u32` 等を即座に
`model::Int`(`std.rs:12` の `#[thrust::def::int_model] struct Int`)へ解決し、以後の
`match ty.kind()` は解決後の型しか見ない。`model_adt`(318行, 707行)は `int_model()` の
DefId 一致だけで無条件 `rty::Type::int()` を返し、符号・幅の情報はここで完全に失われる。
`TyKind::Int`/`Uint` の match arm 自体が `build()` に無く、素の整数型が来ると
`kind => unimplemented!(...)`(432行/824行)に落ちる(通常は `std.rs:307-318` の
`int_model!` で `Model` 実装済みなのでここには来ない)。→ `build()` 内部では符号情報は既に失われており不可。

### (b) `FunctionTemplateTypeBuilder` でパラメータに付ける — 有望
`src/refine/template.rs:899-981`。`param_tys: Vec<mir_ty::TypeAndMut<'tcx>>`(902行)は
**生の MIR 型のまま**保持される(`build_basic_block_with_precondition` 834行、
`tys.push(mir_ty::TypeAndMut{ty: decl.ty,..})` 853行、および `for_function_template` 485行以降の
シグネチャ経由)。パラメータ毎のテンプレート生成は `build()`(982行)の無 refinement 分岐:
`989: for (idx, param_ty) in self.param_tys.iter().enumerate() { ... 1003: .build_refined(param_ty.ty) }`。
`param_ty.ty` はまだ生の MIR 型 → ここで `TyKind::Uint(_)` 判定が可能な**唯一の実用地点**。

**混ぜ方(機構は既存)**: `Template::into_refined_type`(`src/rty/template.rs:26-35`)は現状
`chc::Atom::new(pred_var, atom_args).into()` で `Body` を作るが、`Body`(`src/chc.rs:1883`)は
`pub struct Body<V> { pub atoms: Vec<Atom<V>>, pub formula: Formula<V> }` であり、
未知の predicate 変数(`atoms`)と既知述語(`formula`)を独立に持てる。よって
`Body::new(vec![pred_atom], Formula::Atom(value>=0))` で `P(x1..xn) ∧ (x>=0)` を表現でき、
CHC 生成側の変更は不要と見込む(コードは読んだが実行未検証)。影響: そのパラメータ位置の
全 clause に `x>=0` の連言が常に乗るが `P` 自体は未知のままなので推論を妨げず、探索空間を絞るだけ。

### (c) place 読み出し時の side-condition — 非推奨
局所変数は basic block 間で使い回され SSA 的でないため、「fresh な束縛からの読み出しか算術結果か」を
都度判定するデータフロー解析が要る。現状 `basic_block.rs` にそのような追跡は無い
(`overflow`/`wrapping` で grep 該当なし)。(b)・std.rs 側の明示 spec で足りる範囲では複雑さに見合わない(hypothesis)。

## 2. 健全性の分析(核心)

**事実**: `src/analyze/basic_block.rs:509-536` で `mir::BinOp::Sub` は `rty::Type::Int` に対し
そのまま数学的減算に落ち、ラップアラウンドは一切モデル化されない。`README.md:34` も
「オーバーフロー debug assertion を切る必要があり非対応」と明記。`cast_design.md` §2 も同旨。

- **束縛点(パラメータ・定数・length)での `>=0` は健全**: 符号なし値が外からモデルへ入る地点であり、
  実行時の値は型の定義上常に `>=0`。ここに付けても実際に到達可能などんな状態も排除しない
  (モデルだけが持つ、現実には起こり得ない負値のみを削る) — 抽象の引き締めで健全性を壊さない。
- **算術結果に事後で `>=0` を付けるのは不健全**: `x-1`(`x:usize`)はモデル上ただの整数減算なので
  `x=0` のとき結果 `-1` はモデル内で正当に到達可能。ここへ `>=0` を既知の事実として注入すると
  実際に到達可能な状態を偽って除外し、CHC は「到達不能」という誤った前提から任意の性質を
  導ける(ex falso)。既存の「オーバーフロー未追跡」という穴(モデルが実値と一致しないだけで
  虚偽公理は注入しない)とは異なる**新規の不健全性**。
  → **結論: 束縛点限定なら健全。算術結果への適用は不健全**(問題文の予想と一致)。

## 3. std.rs の既存 length 系仕様

`grep -n ">= 0\|0 <=" std.rs` の結果、`length`/`len()` への `>=0` は**一度も明示されていない**。
`std.rs:193` `Seq{ length: Int }` 定義に篩なし。`std.rs:230` `Seq::len`(`seq_len`)も篩なし。
`std.rs:777` `_extern_spec_vec_len` は `ensures(result==(*vec).length)` のみ。`std.rs:879`
`_extern_spec_slice_len` も同様。唯一の `>=0` 系 ensures は `std.rs:716` の
`_extern_spec_i32_abs_diff`(`ensures(result>=0 && ...)`)— これは人間が書いた個別の数学的事実
(abs_diff は定義上常に非負)で、自動注入とは性質が異なり §2 の「事後注入は不健全」に抵触しない。

## 4. 影響を受けるテスト

`tests/ui/fail/usize_checked_sub.rs`/`std.rs:755` `_extern_spec_usize_checked_sub`
(`ensures((x>=y && result==Some(x-y)) || (x<y && result==None))`)は x,y が負でも成立する
if-then-else なのでパラメータに `>=0` を付けても壊れない。`tests/ui/fail/annot_struct_impl.rs`,
`traits/withdraw_deposit.rs`, `traits/try_withdraw.rs` は `u32` 引数で減算 `ensures` を持つが、
いずれも `requires` の `exists(x >= amount)` で事前ガード済みで負の可能性に依存していない
(壊さない見込み、未実行)。`cast_design.md` 予告の `cast_bound_check.rs` は逆に「`>=0` が無いと
通らない」ケースで、(b) を実装して初めて書ける・通るテスト。既存 pass を壊すケースは見当たらない
(fail 側を見た限りで網羅的実行確認はしていない — hypothesis)。

## 5. 推奨設計(最小・健全)

1. `FunctionTemplateTypeBuilder::build()`(`src/refine/template.rs:989-1003`付近)の無 refinement
   分岐で `param_ty.ty.kind()` が `TyKind::Uint(_)` のとき、`build_refined` の返す `RefinedType`
   の `refinement.body` に `Formula::Atom(GE(Value, Term::int(0)))` を `atoms` は保持したまま
   追加する。対象は**関数パラメータのみ**(戻り値・局所変数は対象外)。
2. std.rs の length 系 extern spec(`std.rs:777` vec_len, `std.rs:879` slice_len, `std.rs:230`
   Seq::len)に `ensures(result >= 0)` を明示追加。人間が書く個別事実として安全。std.rs 変更は
   CLAUDE.md の「Thrust 本体変更は事前承認・別PR」に該当し要相談。
3. 算術結果(`Sub`/`Add`/`Mul` の出力型)には一切 `>=0` を注入しない。

### テスト案
- pass/fail: `unsigned_param_nonneg.rs`(usize引数で`assert!(x>=0)`、現状Unsat→導入後Sat)/
  fail は `i32` 版で同じ assert が Unsat のまま、のペア。
- pass/fail: `vec_len_nonneg.rs`(`assert!(v.len()>=0)`)/ fail は `v.len()>=1` のような
  length spec だけでは導けない性質にして Unsat を保つ。
- 回帰確認 fail: `usize_sub_no_false_nonneg.rs` — `let y = x-1; assert!(y>=0)` は導入後も
  **Unsat のまま**(束縛点限定なので `y` には付かない)であることを確認。
- `cast_design.md` 予告の `cast_bound_check.rs`(`x<=u32::MAX as usize` かつ `x>=0` で `x as u32==x`)。

## 未確認事項(hypothesis)
- `Body.formula` への追加が既存 CHC 節生成(`analyze/basic_block.rs`等)や smtlib2 出力
  (`chc/smtlib2.rs`)で無変更に通るかは未実行検証。
- 既存 pass 全体の再実行による回帰確認は未実施(read-only調査のため cargo test 未実行)。
