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

## `vec![e; n]` の forall 仕様が入った関数では反証が Unknown になることがある

fail/vec_from_elem.rs は環境によって pcsat が Unknown を返す（同じ関数に `vec![e; n]` の呼び出しが
あるだけで、無関係な `assert!(1 == 2)` すら反証できない）。`Vec::new()` + push で作ると即 Unsat。
述語本体側に全称量化子を埋め込む形が pcsat の反証を阻害している。std.rs の from_elem 仕様を
const 配列等式（`(as const (Array Int T)) elem`）で書き直せるか、または量化子無しに弱めるか検討。

## forall-sort: impl のジェネリック引数と呼び出し先の `Self` が別のソート記号になる

idx.rs で自前 Iterator トレイト経由に `IdxRange<I>::next` の仕様を書くと、本体の `I::new(n)` が
要求する `I::can_new(n)` が `q_can_new_<hash><a1>`（Idx::new 側の Self）として現れ、requires で
仮定した `q_can_new_<hash><a0>`（IdxRange<I> の I）と結び付かず、述語本体が "true" でも Unsat になる。
呼び出し側のジェネリック引数と呼び出し先トレイトの Self を同一視する処理が欠けている可能性。
ICE 1（trait_item_ty の owner 不整合）と同根かもしれないので fix/trait-item-ty-owner 後に再確認。

## `Option<&'a u64>` を含む仕様の型付け

`<&'a u64 as Model>::Ty` 同士の `==` が E0277（PartialEq 不成立）。`&T` の blanket PartialEq と
`model::Int` の `PartialEq<T: Model<Ty = Self>>` 実装が噛み合わない。WordIter::next の仕様が書けない原因。

## forall-sort: ジェネリック関数の本体が実質検査されていない（別セッションが CHC で確認、重大）

fix/trait-item-ty-owner の作業中の観察（ベースライン ce6bcae でも同じ）:
`fn g<V>(_t: V) -> i64 { let n = 3i64; assert!(n == 4); 1 }` が verify を通り、意図的に偽の
ensures を付けたジェネリック関数も通る。ジェネリック関数の戻り値 refinement が呼び出し側に
伝わらない点は別セッションの報告（戻り値述語に定義節が無い）と一致する。rustc_coroutine の
ジェネリック関数（layout、eligibility、Idx の default method など）の pass 結果は、この問題が
直るまで信用できない。

根本原因（iterator-adapters 先端で確認）: ジェネリック関数 g の呼び出し箇所は Int ソートの新しい述語
（前提 p8、戻り値 p9）を生成するが、g 本体側の forall ソート述語 p0/p1 と結ぶ節が無い。p0 に定義節が
無いのでソルバが p0 = false と取り、本体の assert のゴール節が空虚に満たされる。単相な同型関数では
呼び出し側が `p6 ∧ v1 = 0 => p0(v1)` を出すので正しく Unsat になる。呼ばれない場合も両者同じ挙動なので、
問題は「ジェネリック関数の forall ソート述語変数が呼び出し箇所で実体化されない（入口・戻り値とも）」
点に限定される。ユーザーの fix/generic-fn-return-tracking が同じ問題を扱う。

候補修正（別セッションからの情報）: ローカルブランチ experiment/skip-placeholder-analysis の
9769fbe「fix: track generic fn call results by re-analyzing bodies at concrete args」が、具体的な
実体化ごとに単相化した本体を再解析する（DefTy::Generic -> DeferredDefMode::Analyze、AnalysisKey ごとの
基本ブロック型）。コミットメッセージによれば黙って通っていた fail テスト 18 件が Unsat になる。現在の
forall-sort 先端に cherry-pick が衝突なしで当たる（dry run）。後続の 16e9c17 は placeholder 解析を
飛ばす別実験で traits/map を退行させるため候補外。適用はユーザーの判断待ち。

## def_ty_with_args のキャッシュ

generic_spec_in_generic_caller.rs で、ジェネリックな呼び出し側の解析の後に同じ impl メソッドを
具体的に呼ぶと、トレイトから継承した ensures が落ちる（main 内の順序で fail 側の結果が変わる）。
最初の（ジェネリック owner での）実体化がキャッシュされて再利用されている疑い。

## 段階 5〜7 の下書きで見つかった制限

- `impl Trait` 型の引数（layout() の `calc: &LayoutCalculator<impl HasDataLayout>`、
  `tag_to_layout: impl Fn(Scalar) -> F`）があると、その関数には requires/ensures が付けられない。
  formula_fn の引数型を `<T as Model>::Ty` に埋め込む際に `error[E0562]: impl Trait is not allowed in paths`。
  式が当該引数に触れなくても起きる。シグネチャを変えられないので、マクロ側で impl Trait 引数を
  名前付き型パラメタに脱糖する対応が要る。
- `is_fully_annotated()` assert（crate_.rs:116, 121）は `#[thrust::trusted]` または `#[thrust::extern_spec_fn]`
  の関数に requires/ensures（または callable）が無いときに落ちる。layout.rs の下書きでは impl Trait 引数の
  せいで仕様を付けられない trusted 関数が残ったのが原因。impl Trait の脱糖は feat/spec-with-impl-trait-args
  で対応（companion にのみ `__ThrustApitN` を追加し末尾に並べるので analyzer 側の変更は不要）。
- `#[thrust_macros::invariant_context]` は存在しない（docs/annotations/11 が古い）。自由関数には
  `#[thrust_macros::context]` を直接付ける。
- unsized な IndexSlice（`raw: [T]`）は `type Ty = Self` が書けない（Ty に暗黙の Sized 境界）。
  下書きでは `type Ty = <[T] as Model>::Ty` で代用しているが、`[T]` の解析自体が未対応。
- 述語の引数は Model::Ty（Int）に下がるので、実 Vec の添字（usize）と述語呼び出しを 1 つの式で混ぜる
  には `exists(|li: Int| li == l && ..)` の橋渡しが要る。
- `IndexVec::from_elem_n` の要素ごとの ensures は `T: PartialEq<<T as Model>::Ty>` 相当の境界が
  ジェネリックには満たせず書けない。

## next() 仕様の適用（idx.rs / bitset.rs）で見つかった制限

- extern_spec ラッパを付けた対象は本体が解析される。trusted のままにはできず、BitIter::next は
  `#[thrust::ignored]` に置き換えた（spec.rs のマクロが行う書き換えと同じ）。
- 仕様式では struct フィールドのスライス/Vec に `.length`/`.array` が無く、`.len()` も
  `annot_fn.rs:915 unsupported method call in formula`。生 SMT の述語で代用。
- 名前付き const（WORD_BITS）は仕様式で使えない（`annot_fn.rs:809 unsupported path in formula`）。
- 実行コードの `assert!(d == Some(0))` は `basic_block.rs:381 const bytes ty: Option<usize>` で落ちる。
  `d.unwrap() == 0` / `d.is_none()` にする。
- 事後条件の `exists` は fail 側を Unknown にしやすい。payload を全称量化する形に書き換えると決定的。
- `Option<&u64>` の payload は `exists(|x: Int| result == Some(&x))` の形で書ける。
- CI 固定の coar イメージ（ghcr.io/hiroshi-unno/coar:main と同一）は `declare-forall-sort` を
  パースできない。このブランチのテストはローカルビルドの coar:latest（a21d2d712532）が必要。

## 環境要因（別セッションからの注意、2026-09-09）

- coar:latest イメージは再ビルドされた（旧 c887fbe8b726 は 2025-12 ビルドで upstream より 9 か月古い）。
  以前のソルバ判定（Unsat/Unknown/Timeout）は暫定扱いで、再ビルド後に再測定する。
- ワークツリーごとの target/debug/deps に古い libthrust_macros-<hash>.so が複数残ると、ドライバが
  最初に見つけたものを読み込み、偽の E0433/E0401 や偽の Unsat が出る。ローカルの失敗を信じる前に
  `ls target/debug/deps/libthrust_macros-*.so` で 1 個だけか確認し、複数なら削除して再ビルド。
- 手書き `invariant!` の注意: 囲む関数に `#[thrust_macros::context]` が要る、`&mut` 引数は
  `let a = x;` で再束縛して `a: &mut T` と `x: FnParam<&mut T>` を `!a == !x.at_entry()` で結ぶ、
  invariant は推論述語を置き換えるのでループ後に必要な事実をすべて書き直す。
- 再ビルド後の coar:latest（e8a1748680a3）で rustc_coroutine の段階ファイルを再測定: probe 7 組は変化なし、
  values/idx/bitset の pass 側 3 件は 30 秒でタイムアウトし、150 秒では verify。旧ローカルイメージ
  （a21d2d712532）では 1〜3 秒だったので新イメージは遅い。3 組のヘッダを THRUST_SOLVER_TIMEOUT_SECS=120 にした。
