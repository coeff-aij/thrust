# Spec Gaps 調査メモ

検証環境: `cargo run --quiet -- -Adead_code -C debug-assertions=off <file>`、
`THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest`（および素の z3）。
スクラッチファイルは `scratchpad/gaps/` 以下。リポジトリは未変更（read-only）。

## Gap A: struct フィールドの Vec は `type Ty = Self` だと配列として使えない

### 事実・原因

- `gapA_self.rs`: `impl Model for Layout { type Ty = Self; }` で `dl.info.length`
  (`dl: &Layout`, `info: Vec<i64>`) は `error[E0609]: no field 'length' on type
  'std::vec::Vec<i64>'` で失敗（再現確認済み）。
- 原因は **rustc フロントエンド typeck** レベル。`thrust-macros/src/formula_fn_type_lowering.rs:56-64`
  (`lower_params`) が引数型を `<T as Model>::Ty` に書き換える。`&Layout` は
  `std.rs:363-365` の `impl<'a,T> Model for &'a T { type Ty = &'a <T as Model>::Ty; }` で
  `&<Layout as Model>::Ty` になり、`Ty = Self` なら単に `&Layout` になる。companion 内で
  `dl.info` は実体の `Vec<i64>` のままで `model::Vec`（`Seq`、`std.rs:186-193` の
  `array`/`length` を持つ struct）に変換されない。
- Thrust の `build()`（`src/refine/template.rs:348-420`）は struct を
  「各フィールドを `build()` したタプル」として構造化する経路（`is_struct()` 分岐、
  同 409-419）を持つが、これは **rustc typeck 通過後**の後段処理であり、今回のように
  frontend typeck が先に失敗するケースには無関係。「`Ty=Self` で Vec フィールドが
  使えない」のは Thrust の意味解析の限界ではなく、マクロ展開で `Ty` が実際の Rust
  型のまま出てくることの帰結。

### `type Ty = (tuple, ...)` 形式は動く（`ghost_field.rs` と同型）

- `gapA_tuple.rs`: `type Ty = (Int, Seq<Int>, bool)` として `dl.1.length`/`dl.0` を
  書くと check-pass（フィールド名でなくタプル添字。`tests/ui/pass/ghost_field.rs` の
  `type Ty = (Int, Seq<Int>)` + `(*c).1.len()` と同型）。
- `gapA_tuple_body.rs`: 実体 `info: Vec<i64>` に対し実際に `dl.info.push(x)` する本体で
  `ensures((!dl).1.length == (*dl).1.length + 1)` が check-pass、
  `gapA_tuple_body_fail.rs`（誤った ensures）は正しく `Unsat`。実フィールドへの
  std メソッド呼び出しの効果が、タプル添字で参照した宣言済み `Ty` と矛盾なく結びつく
  ことを確認。
- 仕組み（仮説、コード裏付けあり）: struct 型を `build()` すると先頭の
  `resolve_model_ty`（`template.rs:279-306`）が `<Layout as Model>::Ty` を正規化し、
  `Ty` がタプルなら `is_struct()` 分岐は通らず正規化結果がそのまま使われる。実 MIR の
  フィールド射影 (`PlaceElem::Field`) は `src/refine/env.rs:1032`
  (`FlowBinding::Tuple(xs) => xs[idx.as_usize()]`) や同 1067 のように**位置（宣言順の
  添字）でタプルを直接引く**。実フィールド型は別途 `build()` され `std.rs:372`
  (`impl<T> Model for Vec<T> { type Ty = model::Seq<<T as Model>::Ty>; }`) に従い
  `Seq<Int>` になるため、ユーザが宣言する `Ty` の各タプル要素をちょうど
  `<実フィールド型 as Model>::Ty` と書けば自動的に整合する。ただし**名前や型による
  突き合わせは行われず、添字と順序の一致はユーザ責任**（順序がずれても検出されない
  可能性＝未確認の仮説）。

### 結論

- `type Ty = Self` は struct を透過的な Rust 値として使う場合のみ有効で、`Vec`/`Seq`
  のモデル操作（`.length` 等）はできない。
- `type Ty = (F0, F1, ..)` タプル形式ならフィールド順の添字アクセスで動く。Vec
  フィールドは対応位置に `model::Seq<..>` を書けばよく、`.length` は `.N.length` になる。

## Gap B: trait レベル `ensures(*result == *self)` の型検査失敗

### 事実・原因

- `gapB_base.rs` で完全再現: `error[E0308]`、`expected 'TargetDataLayout', found
  associated type '<Self as thrust_models::Model>::Ty'`。
- 原因: `receiver_type`（`thrust-macros/src/lib.rs:158-172`）は trait メソッドの
  `&self` を常に抽象 `Self` として扱う。`formula_fn_type_lowering.rs:44-64`
  (`lower_params`) がこれを `self_: <Self as Model>::Ty` に、`lower_return_type`
  (同 66-73) が戻り値 `&TargetDataLayout` を `<&TargetDataLayout as Model>::Ty`
  (= `&TargetDataLayout`、`Ty=Self` なので) に落とす。戻り値の型がトレイト
  シグネチャ上 `Self` を経由しない具体型のため、`self`（抽象）と `result`（具体）が
  別の型になり `==` が型検査できない。`Self: Model<Ty = TargetDataLayout>` の
  追加 bound がない限り解消しない。

### 代替案(1): by-value 述語 `dl_of(self, dl: TargetDataLayout) -> bool`

- `gapB_predicate.rs`: 述語の各引数は自分自身の型で lowering されるため
  (`self_: <Self as Model>::Ty`, `dl: TargetDataLayout`)、
  `Self::dl_of(*self, *result)` は型が一致し型検査を通過。SMT 生body
  `"(= self_ dl)"; true` を与え、呼び出し元で `dl.x` を assert する
  requires/ensures 込みで **check-pass**（COAR・z3 とも exit 0）。
- `gapB_predicate_ref.rs`: `&self` 版の述語も同シナリオで **COAR・z3 とも
  check-pass**した。「以前 `&self` で solver unknown」は今回の最小構成では
  再現せず（実際の多フィールド/`Vec` を持つ `TargetDataLayout` など、より複雑な
  述語本体・比較対象で起きた可能性が高い＝未確認の仮説）。→ by-value化自体が
  本質的解決ではなく、まず述語本体の複雑さ（`Vec`/`Seq` 比較）を疑うべき。

### 代替案(2): impl 側だけに `ensures`

- `gapB_impl_only.rs`: trait 側無注釈で `#[context] impl` 側だけに
  `ensures`/`requires` を付けると **`error[E0407]`**
  (`method '_thrust_requires_data_layout' is not a member of trait
  'HasDataLayout'`) + 関連 `E0599` で失敗。companion 関数を impl の
  trait メンバとして展開するため、トレイト側に対応宣言が要る。
  **companion はトレイトメンバ必須で、impl のみへの後付けは不可**。

### `impl HasDataLayout for &TargetDataLayout` の共有可否

- 型は共有できる: `std.rs:363-365` の blanket `impl<'a,T> Model for &'a T` により
  `&TargetDataLayout` は自動的に `Model` 実装済み。`#[context] impl HasDataLayout
  for &TargetDataLayout` として別途 `dl_of`/`data_layout` を実装するだけなら
  コンパイル成功 (`gapB_ref_impl.rs`)。
- ただし呼び出し側で二重参照 (`a: &&TargetDataLayout`, `(*a).x`) を介すと **ICE**:
  `panicked at src/analyze/annot_fn.rs:846:30: named field access on a non-ADT
  type`。スタックは `extract_require_annot`（`src/analyze.rs:863`）経由で
  `requires((*a).x == 3)` の翻訳中に発生。`gapB_doubleref_isolate.rs` で
  トレイト無関係の最小構成 (`a: &&TargetDataLayout`, `(*a).x`) でも同じ panic を再現。
- 原因: `annot_fn.rs:832-848` の `ExprKind::Field` は数字でないフィールド名の場合
  `self.expr_ty(expr).ty_adt_def()`（同 842-844）で **`expr` の静的型がそのまま
  ADT であることを要求**する。rustc の autoderef と異なり、Thrust の formula
  translator はこの autoderef を畳み込まないため、`*a` が `&TargetDataLayout`
  （参照が一段残る）だと `ty_adt_def()` が `None` になり panic する。
  CLAUDE.md の方針通り既知の ICE パスとして記録するに留める。
- 結論: `&TargetDataLayout` へのimplは書けるが、**多重参照越しのフィールドアクセスは
  フィールド射影コードが未対応**。単一参照からの直接アクセスは他の全テストで問題なし。

## 参照ファイル
`thrust-macros/src/formula_fn_type_lowering.rs:44-73`（lower_params/lower_return_type）、
`thrust-macros/src/lib.rs:158-172`（receiver_type）、
`src/refine/template.rs:279-306, 348-420`（resolve_model_ty/build/struct 構造化）、
`src/refine/env.rs:1032, 1067`（PlaceElem::Field の位置ベースタプル添字）、
`std.rs:186-193, 363-372`（Seq 定義、&T/Vec<T> の Model impl）、
`src/analyze/annot_fn.rs:832-848`（named field access, ICE の発生源）、
`tests/ui/pass/ghost_field.rs`, `tests/ui/pass/annot_preds_trait.rs`
