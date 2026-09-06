# layout()/coroutine_saved_local_eligibility のイテレータアダプタ連鎖: パニック安全性ギャップ分析

対象: `tests/ui/pass/traits/rustc-coroutine.rs`。目的は `layout()` のパニック安全性のみ
(rustc-coroutine-scope memory)。`univariant`/`univariant_biased`/`scalar_pair`/`count_ones` 等は
既に `#[thrust::trusted]`(755-763行付近, 1020-1393行, 260-275行)でスコープ外。以下は
`coroutine_saved_local_eligibility`(674-763行)と `layout`(765-945行)本体にある**未trusted**の
チェーンのみを対象とする。

## 対象チェーン一覧 (grep で確認、行番号は当該ファイル)
- 755: `ineligible_locals.iter().enumerate()`
- 796/798: `ineligible_locals.iter().map(|local| local_layouts[local])` → `prefix_layouts.extend(..)`
- 848-863: `variant_fields.iter_enumerated().map(|(index, variant_fields)| { variant_fields.iter().filter(|local| ..).map(|local| ..).collect::<IndexVec<_,_>>() ... })`
- 884: `iter::zip(offsets, memory_index)`、891: `offsets_and_memory_index.next().unwrap()`
- 886-905: `variant_fields.iter_enumerated().map(|(i, local)| {...}).collect()`
- 909: `combined_in_memory_order.raw.retain(|&i| ..)`
- 920: `.collect::<Result<IndexVec<VariantIdx,_>,_>>()?`
- 924: `variants.iter().all(|v| v.is_uninhabited())`
- 483-484/495-496 (`invert_bijective_mapping`, 480-502行): `.sum::<u128>()` (debug_assert_eq! 内)

## 各アダプタ/コンシューマ

### map (796, 849, 859, 887)
- (a) 各要素でクロージャがパニックしない = 要素ごとの `pre!` obligation。
- (b) `map.rs`/`map_fn.rs`/`map_no_closure.rs` は自作 `Map<I,F>` の `step` 述語内に
  `q_pre_next_...(mut(self.func, f), i)` の存在量化を埋め込み、クロージャ呼び出し前提条件を
  イテレータの一歩ごとの遷移に結び付ける枠組みを持つ(map.rs 122-151行)。
- (c) ただし map.rs/map_fn.rs/map_no_closure.rs はいずれも `//@check-pass` が無い(他の
  traits/*.rs との見出し比較で確認)。probe テスト群のコミット `ebfa167` の説明文は「delegation・
  Option 返却・カウンタは全て verify するので、id.rs(最も単純なラッパ)の Unsat は
  `Iterator::next` 仕様自体に起因する」と述べている。つまり自作 Iterator モデルの根幹が
  まだ通っておらず、map の土台自体が未完成。

### filter (852-858)
- (a) map と同様、述語クロージャがパニックしないこと。
- (b)(c) traits/*.rs に filter 用アダプタは無い(Map/Take/Fuse/Id のみ)。仕様は0から要設計。

### collect::<IndexVec<_,_>>() 経由の FromIterator (863, 905, IndexVec::from_iter 616-624)
- (a) 生成された `IndexVec` の長さ = 元イテレータが yield した要素数(と、途中の push が
  パニックしないこと)。
- (b)(c) `std.rs` に `FromIterator`/`Vec::from_iter`/`Extend` の `extern_spec_fn` は一件も無い
  (`grep -n 'extend\|retain\|zip\|enumerate\|fn sum\|fn all\b\|FromIterator\|fn fold\|IntoIterator\|::iter(' std.rs` はゼロ件)。
  `Vec::push` には長さの等式スペックがある(`std.rs` 766-771行)ので、それを土台に
  `FromIterator`/`Extend` を「push を要素数だけ繰り返す」as 仕様化する余地はあるが、現状は無い。

### collect::<Result<IndexVec<_,_>,_>>()?  (920)
- Item が `Result<_, Err>` のイテレータを、最初の `Err` で打ち切って `Result<IndexVec,_>` に
  集約する `core` の `FromIterator<Result<A,E>> for Result<V,E>` に依存。
- (a) 「途中で Err に当たったら残りの要素は評価されない」という早期終了込みの契約が要る。
- (b) fold.rs/fold_fn.rs の仕様(全要素を最後まで消費する前提の history-array 仕様、後述)は
  この早期終了セマンティクスを表現していない。
- (c) fold 系より一段リッチな「短絡 collect」の専用仕様が要る。現状は無い。

### iter::zip + .next().unwrap() (884, 891, combined_offsets の map 内 887-904)
- (a) `unwrap()` がパニックしない条件は zip の残り長さが呼び出し回数以上であること。
  この不変条件は、`variant_fields.iter_enumerated().map(...)` クロージャの**外側**にある
  `offsets_and_memory_index`(`&mut` でキャプチャされた別のイテレータ)の残り消費量に依存する。
- (b) fuse.rs は `Option<I>` 1本の完了状態しか扱わず、2本を同時消費する zip 相当のアダプタは
  無い。さらにここのクロージャは外側の可変イテレータ状態を書き換える `FnMut` であり、
  `iterator-fold-spec-plan` memo および `ebfa167` の FIXME は「FnMut の pre!/post! はこの
  ブランチで一般に Unsat」(`closure_postcondition_fnmut.rs` 等)と既知の制約として記録している。
- (c) 「map クロージャが外部の別イテレータを可変キャプチャして進める」パターン自体に
  対応するモデルが無く、かつ土台の FnMut pre!/post! が未解決。この3チェーン中最難。

### enumerate (755, IterEnumerated は 405-423 行で別物)
- (a) パニック安全性自体は薄い(`FieldIdx::new(idx)` の前提を満たす必要がある程度、
  Idx::new の前提は trait predicate として定義済み — rustc-coroutine-scope memo)。
- (b)(c) `IterEnumerated`(405-423行)は `IndexSlice::iter_enumerated` 専用の自作型で、
  755行の `ineligible_locals.iter().enumerate()` は `DenseBitSet::iter()`(131-134行、
  中身は自作 `BitIter`)に対する std の `Enumerate` であり別物。std `Enumerate` のモデルは無い。

### extend (798, IndexVec::extend 609-614 は `self.raw.extend(iter)` に委譲)
- (a) push をイテレータの要素数だけ繰り返すだけなのでパニックしないことが言えれば十分。
- (b)(c) `Extend<T> for Vec<T>` の extern spec が無い(前述の grep でゼロ件)。

### retain (909)
- (a) `|&i| i.index() != invalid_field_idx` はパニックしない単純な比較のみ。
- (b)(c) `Vec::retain` の extern spec が無い。他より要求が軽い(要素ごとの pre! のみで
  合成の複雑さが無い)ので実装コストは相対的に低いと見られる(推測)。

### all (924)
- (a) `is_uninhabited()` がパニックしなければ全体もパニックしない(短絡評価のみ)。
- (b)(c) std `Iterator::all` のモデルは無いが、要素ごとの pre! だけで済み、fold/zip より単純
  (推測)。

### sum::<u128>() (483-484, 495-496, `invert_bijective_mapping` 内の `debug_assert_eq!`)
- (a) u128 へのオーバーフローが無いこと。
- (b)(c) それ以前に、クロージャ `|x| x.index() as u128` の `as` キャストがファイル冒頭コメントの
  「未対応構文」一覧(22行目)に載っており、sum の仕様以前にここで Thrust が止まる。
  なお `debug_assert_eq!` はこのファイルには `compile-flags: -C debug-assertions=off` の指定が
  無く(`grep -n '^//@'` で確認、`//@ignore-on-host` と `//@edition: 2024` のみ)、他の
  traits/*.rs の運用(fold.rs 等は debug-assertions=off 指定あり)と食い違う可能性がある。

## 構造的問題: 自作 Iterator トレイト vs core の Iterator
map.rs/take.rs/fuse.rs/id.rs/fold.rs 等が定義する `Iterator`(`invariant`/`completed`/`step`
述語つき、`#[thrust_macros::context] trait Iterator`)はテストファイルローカルの**別トレイト**で
あり、`Map<I,F>`/`Take<I>`/`Fuse<I>`/`Id<I>` はそれを実装する**自作ラッパ型**。一方
rustc-coroutine.rs の `layout()`/`coroutine_saved_local_eligibility` が実際に呼んでいるのは
`core::slice::Iter` 相当(ここでは自作 `SliceIter`/`IterEnumerated`/`WordIter`/`IdxRange` に
置換済み、380-423行のコメント参照)、`core::iter::Map`/`Filter`/`Zip`/`Enumerate`、
`std::vec::IntoIter`、`core::iter::Sum`/`FromIterator` といった **std/core 本体の具体型と
トレイト実装**である。名前が同じ `Iterator` というだけで型システム上は無関係であり、
map.rs 等で確立した「step 述語の中に pre!/post! を埋め込む」パターンは、rustc-coroutine.rs の
ような core 由来の具体型を相手にする限りそのままでは適用できない。

## 選択肢
1. **`extern_spec_fn` で core の Iterator 系メソッドに直接スペックを付ける**
   既に `Vec::push`/`Option::map`/`std::mem::take` 等で機能している実績がある
   (`std.rs` 各所、`tests/ui/pass/extern_spec_take.rs`)。ただし既存例は全て「1回の呼び出し」
   に対する pre/post であり、`next()` を繰り返し呼んで `None` まで消費する反復契約(ループ
   不変条件相当)を `extern_spec_fn` がどう表現するかの前例は無い(推測: trait メソッドごと、
   かつ「呼ぶたびに状態遷移する」ものへの拡張が要る)。
2. **std のアダプタ構造体(`std::iter::Map`/`Filter`/`Zip`/`Enumerate`、`std::vec::IntoIter`)を
   Thrust 側でモデル化する** — rustc-coroutine.rs 冒頭コメント(19-20行目)が
   「std iterator types with raw pointers (vec::IntoIter, slice::IterMut)」を明示的に未対応と
   述べており、slice::Iter の代替として自作 SliceIter 等を用意した経緯そのものがこの制約への
   回避策。core 内部の adapter 構造体はほぼ確実に生ポインタを持つため、同じ壁にぶつかる
   (推測)。
3. **現行の自作 `Iterator` トレイトを rustc-coroutine.rs の具体型に適用する** — オーファン
   ルール上不可能、かつ rustc-coroutine.rs は既に core の具体型を直接使っているため経路として
   成立しない。

## 結論
- map/filter/collect(→IndexVec)/collect(→Result)/zip+unwrap/enumerate/extend/retain/all/sum の
  9系統について、`std.rs` の extern_spec_fn にも traits/*.rs の自作 Iterator モデルにも対応が
  一件も無いことを確認した(grep 調査)。
- 加えて自作 Iterator モデル自体、map.rs/take.rs/fuse.rs/id.rs に `//@check-pass` が付いておらず
  (commit `ebfa167` の記述と符合)、最も単純な `Id` ラッパですら現状 Unsat と見られるため、
  仮に同じ枠組みを rustc-coroutine.rs の具体型向けに転用しようとしても土台が未完成。
- 有力なのは選択肢1(extern_spec_fn の反復契約への拡張)だが、これは新規の Thrust 機能拡張に
  当たり得るため `feedback-ask-before-changing-thrust` に従い着手前に承認が必要。
- 難度が特に高いのは (i) collect::<Result<_,_>>? の短絡セマンティクス、(ii) filter、
  (iii) zip + 外部可変イテレータキャプチャ(既知の FnMut pre!/post! Unsat に直結)。
  retain/all/enumerate は要素ごとの pre! のみで合成が単純なため、相対的に着手しやすいと
  見られる(推測)。

## 読んだファイル
- `tests/ui/pass/traits/rustc-coroutine.rs`(全体, 特に480-502, 663-945行)
- `tests/ui/pass/traits/{map,map_fn,map_no_closure,fold,fold_fn,fold_noloop,take,fuse,id,option_map}.rs`
- `std.rs`(1-1109行、extern_spec_fn 一覧)
- `docs/annotations/18-loop-and-quantifier.md`
- memory: `iterator-fold-spec-plan.md`, `rustc-coroutine-scope.md`, `rustc-coroutine-progress.md`,
  `feedback-keep-iterator-chains.md`
- `git log`/`git show ebfa167`(probe テストのコミットメッセージ)
- 注: `tests/ui/pass/traits/probe_*.rs` は存在せず、実体は `tests/ui/fail/traits/probe_*.rs`。
