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

## probe で見つかった追加の制限（rustc_coroutine/probe_*.rs 作成時）

- `vec![1, 2, 3]`（要素列挙形）で作った Vec を添字アクセスや仕様付き関数に渡すと
  `template.rs:442: not implemented: unrefined_ty: *mut u8`（`<[_]>::into_vec(Box<[T]>)` 経由）。
  `Vec::new()` + `push` なら問題なし。`vec![e; n]` は std.rs の from_elem 仕様で対応済み。
- `&Vec<T>` 引数の仕様で `v.length` と書くと `annot_fn.rs:846: named field access on a non-ADT type`。
  `(*v).length` と書く必要がある（std.rs の慣習どおり）。
- `&self` 受け手のトレイトメソッドで `requires(Self::pred(*self))` と書くと
  `template.rs:145: unknown type param idx`（非ジェネリック impl でも）。`&mut self` なら通る。
  fix/trait-item-ty-owner の修正で直るか要確認。
- 存在量化された配列事実の否定方向（assert を反転した fail 側）は pcsat が Unknown を返すことがある。
  fail 側は「requires を 1 つ落とす」形にするのが安定。
- forall/exists のクロージャ引数型: 具体フィールド（i64）と比較するときは Rust 型、
  `Option<usize>` 引数と比較するときは `thrust_models::model::Int` を明示する必要がある。

## std トレイトの impl メソッドには仕様が付けられない

`impl Iterator for BitIter { #[thrust_macros::ensures(..)] fn next(..) }` は
`error[E0407]: method '_thrust_requires_next' is not a member of trait 'Iterator'` になる
（companion 関数がトレイトのメンバである必要がある）。自前イテレータの next の仕様は、
自前トレイトに載せるか、extern spec で impl を指すか、マクロ側の対応が要る。段階 3 では
BitIter::next の列挙仕様、段階 4 では IdxRange/WordIter/SliceIter の next 仕様がこれで書けない。

## 述語の本体と bool 値の混在

`result == Self::mem(..)` は annot_fn.rs:739 で unwrap panic、`result ==> ..` は `expected a formula`。
`(result == true) ==> pred` と `pred ==> (result == true)` の 2 本に分ける。

## 未ガードの forall 仮定は反証側を壊す

`ensures(forall(|i| !mem(result, i)))` のような無条件の全称仮定があると fail 側が Unknown/Timeout
になる。const 配列との等式（`(as const (Array Int Int)) 0`）や store 等式で書き直すと決定的になる。
また本体無しの述語（declare-forall-fun）は解の自由度になり、fail 側が空虚に SAT になり得る。

## 段階 1（values.rs）で見つかった制限

- `#[thrust_macros::predicate]` の本体は SMT 文字列のみ（thrust-macros/src/spec.rs:18-21、
  local_def.rs:152）。docs/annotations の「Rust 論理式でも書ける」は誤り。requires/ensures の式は
  Rust 構文で書けるので、述語は requires にインライン展開した。
- struct モデル内の Vec フィールド（`dl.address_space_info`）は仕様式で Rust の `Vec` 型のままになり
  `.length` / `.array` が使えない（E0609）。トップレベル引数の `&Vec<T>` だけが Seq として見える。
- トレイトレベルの `ensures(*result == *self)` は `<Self as Model>::Ty` と具体型の不一致で型エラー。
  述語 `dl_of(&self, dl)` に逃がすと pcsat が Unknown を返す（本体を "true" にしても同じ）。
  そのため Primitive::size/align が trusted のまま。
- 18 フィールドの struct（TargetDataLayout）の derive(PartialEq) は `&&` 連鎖が長く、それだけで
  ソルバが 60 秒タイムアウトする。
- 外部トレイトの impl メソッド（`impl Add for Size`）にも仕様が付けられない（Iterator と同じ）。
- 関連定数（`Align::EIGHT`）は newtype 定数の ICE（feat/newtype-scalar-consts で修正）。
- values.rs では AbiAlign::min/max を一時的にコメントアウトしている（Align の Ord が無いため）。
  fix/enum-discriminants が入ったら derive を戻して復元する。
