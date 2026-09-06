# 検証結果を読むときに注意する既知の問題

## forall-sort 系ブランチ: ジェネリック非トレイト関数の戻り値述語が未定義

（別セッションからの報告、未修正。ユーザーの fix/generic-fn-return-tracking が同じ問題を扱う）

単相な文脈からジェネリックな非トレイト関数を呼ぶと、実体化された戻り値の述語
（例: fail/fn_poly.rs の p8）に定義節が付かず、ソルバがそれを false に取れる。その結果、呼び出し
以降の assert が空虚に成立し、fail/ の約 25 件（fn_poly*、closure_param*、trait_param、
loop_invariant_trait、adt_poly_fn_poly）が「通ってしまう」。

rustc_coroutine の段階ファイルは Idx などのジェネリック補助関数を具体型から呼ぶので、
pass 結果が空虚でないかを fail 側の対で必ず確認すること（fail が Unsat にならなければ疑う）。

## main: 最上位ビットが立った符号なし定数が符号拡張される

`const_value_ty` が符号に関係なく `to_int` を使うため、u32 の 4294967295 がモデル上 -1 になる。
`fn id(x: u32) -> u32 { x }` で `assert!(id(4294967295) > 0)` が Unsat。
修正ブランチ fix/unsigned-const-sign を作成中。

## main: 符号なし型に `>= 0` の refinement が無い

`idx <= u32::MAX ==> 0 <= idx` が導けない。関数引数に限って `>= 0` を付ける修正を
feat/unsigned-param-nonneg で作成中（notes/unsigned_nonneg.md）。

## 対象ファイルで残る未対応構文

先頭コメントの一覧を参照。ブランチ側の状況: `as` は feat/int-casts、newtype 定数は
feat/newtype-scalar-consts、負の判別子は作成中、ICE 2 件は fix/trait-item-ty-owner と
fix/singleton-spec-params（forall-sort base）。
