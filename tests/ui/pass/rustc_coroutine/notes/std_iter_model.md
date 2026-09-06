# std イテレータ（slice::Iter / slice::IterMut / vec::IntoIter）のモデル設計メモ

生ポインタ（`NonNull<T>` / `*const T`）を持つため、現状は `template.rs` の struct フィールド走査
（`src/refine/template.rs:410-419`, `:790-799`）に落ちて壊れる。以下 `std.rs` = リポジトリ直下の `std.rs`。

## 1. Model impl とテンプレートビルダ
`TypeBuilder::build` は先頭で `resolve_model_ty` を通す（`template.rs:346-348`, `:735-736`）。
`resolve_model_ty`（`:279-309`）は `<Ty as Model>::Ty` を正規化し、**結果に `Model::Ty` alias が
残っていたら正規化結果を捨てて元の型を返す**（`:296-307`, `contains_model_ty_alias`）。よって:

- **要素型が具体型**（`slice::Iter<'_, i64>` 等）なら正規化が `model::Seq<model::Int>` まで潰れるので
  **Model impl を書くだけで足りる**（生ポインタフィールドは走査前に消える）。`model::Seq` は
  `model_adt`（`:317-341`）に分岐が無いが `is_struct()` 走査で `(own(Array<Int,T>), own(Int))` になり
  `def_ids.vec()` 特例（`:390-402`）の手作り tuple と一致する。
- **要素型がジェネリック `T`** だと `Seq<<T as Model>::Ty>` に alias が残り元の型へ巻き戻る。
  `Vec<T>` に `vec()` 特例が要るのはこれが理由。三イテレータでも同じ手当てが必要。

選択肢: (a) `did_cache.rs` に 3 つの DefId を足し `template.rs:390` / `:773` に `vec()` 同型の分岐を追加。
(b) `contains_model_ty_alias` を緩め、残る alias の引数が全て型パラメータなら正規化結果を採る。`build` の
Alias 分岐（`:420-436`, `:805-821`）が `<T as Model>::Ty` を `translate_param_type` に落とせるので
原理的に通り、既存の `vec()` / `[T]` 特例も不要になる。共有コードなので**要事前承認**＋probe。
→ まず具体要素型で Model impl 単独を確認し、generic は (b) を提案、却下なら (a)。

## 2. モデル型: 「残り列」より「(基底列, カーソル)」
Creusot 忠実版は `type Ty = model::Seq<&'a <T as Model>::Ty>` だが二点で不利:

1. formula_fn 本体は**実 Rust として型検査される**。`Seq` の `PartialEq` は `U: Model<Ty = Self>` を
   要求する（`std.rs:196-201`）ので `Seq<&T::Ty> == Seq<T::Ty>`（＝ `result == *slice`）は通らない。
   CHC 側では `unbox` が Box/immut を消す（`src/chc/unbox.rs:12-41`）ので `&` は情報を持たない。→ 落とすべき。
2. 「残り列」は `next` ごとに列全体をずらすので
   `forall i. (!it).array[i] == (*it).array[i+1]` が毎回入り、それが不変条件に載る。
   pcsat には重い（`std.rs:1039-1041` の split_off が同じ理由で要素記述を諦めている）。

**推奨**（既存 `tests/ui/pass/iterators/range.rs` の start/end と同じ発想）:

```rust
// いずれも std.rs に置く。model = thrust_models::model, Model = thrust_models::Model。
impl<'a, T: Model> Model for core::slice::Iter<'a, T> {                 // (基底列, 次に返す位置)
    type Ty = (model::Seq<<T as Model>::Ty>, model::Int); }
impl<T: Model> Model for alloc::vec::IntoIter<T> {
    type Ty = (model::Seq<<T as Model>::Ty>, model::Int); }
impl<'a, T: Model> Model for core::slice::IterMut<'a, T> {              // 4 節
    type Ty = (model::Mut<model::Seq<<T as Model>::Ty>>, model::Int); }
```

Creusot の `produces(self, visited, o)` ≡ `self@ == visited.concat(o@)` はこの表現では
`o.0 == self.0 && o.1 == self.1 + visited.length && forall j. visited[j] == self.0[self.1+j]` という
**導出述語**になり、量化子は `produces` を明示的に使うときだけ払う。`completed` は
`self.1 == self.0.length && !self == *self`。concat 版も原理的には可能で
`select(seq_concat(s,t), i)` は `ite(i < len s, ..)` へインライン展開される（`src/chc.rs:950-968`）ため
帰納法は不要だが、`Seq` に tail/部分列が無い（`std.rs:212-246`）ので残り列を作れない。

## 3. std.rs に足す extern spec
キーイング: 対象 DefId は末尾呼び出しを `Instance::try_resolve` で解決したもの（`local_def.rs:95-108`）。
`<Iter<'a,T> as Iterator>::next` 等は impl が具体なので **per-impl DefId に解決される**はずで三つの `next`
は衝突せず、`std.rs:1051-1052` の blanket impl 問題にも該当しない（要確認: `T` が残った状態で `try_resolve`
が `Some` を返すか）。

```rust
// 生成側。where 句と本体は既存の slice 仕様（std.rs:879-1023）と同形。requires は true。
// <[T]>::iter(slice: &[T])                 ensures(result.0 == *slice && result.1 == 0)
// <[T]>::iter_mut(slice: &mut [T])         ensures(result.0 == slice  && result.1 == 0)  // Mut をそのまま
// <Vec<T> as IntoIterator>(vec: Vec<T>)    ensures(result.0 == vec    && result.1 == 0)
// <&Vec<T> as IntoIterator>(vec: &Vec<T>)  ensures(result.0 == *vec   && result.1 == 0)  // -> slice::Iter
// <&mut Vec<T> as IntoIterator>(vec)       ensures(result.0 == vec    && result.1 == 0)  // -> slice::IterMut
#[thrust::extern_spec_fn] #[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.0 == *slice && result.1 == 0)]
fn _extern_spec_slice_iter<T>(slice: &[T]) -> core::slice::Iter<'_, T>
    where T: thrust_models::Model, T::Ty: PartialEq { <[T]>::iter(slice) }

// Iterator::next for slice::Iter   （量化子なし）
#[thrust_macros::requires(0 <= (*it).1 && (*it).1 <= (*it).0.length)]
#[thrust_macros::ensures(
    ((*it).1 < (*it).0.length
        && result == Some(&(*it).0.array[(*it).1])
        && (!it).0 == (*it).0 && (!it).1 == (*it).1 + 1)
    || ((*it).1 == (*it).0.length && result == None && !it == *it)
)]
fn _extern_spec_slice_iter_next<'a, T>(it: &mut core::slice::Iter<'a, T>) -> Option<&'a T>
    where T: thrust_models::Model, T::Ty: PartialEq
{ <core::slice::Iter<'a, T> as Iterator>::next(it) }

// vec::IntoIter の next は上の `&` を外すだけ: result == Some((*it).0.array[(*it).1])
// slice::IterMut の next
#[thrust_macros::ensures(
    ((*it).1 < (*(*it).0).length
        && result == Some(thrust_models::model::Mut::new(
               (*(*it).0).array[(*it).1], (!(*it).0).array[(*it).1]))
        && (!it).0 == (*it).0 && (!it).1 == (*it).1 + 1)
    || ((*it).1 == (*(*it).0).length && result == None && !it == *it)
)]
```

対比: 残り列版の `next` は `(!it).length == (*it).length - 1 &&
forall(|i| 0 <= i && i < (!it).length ==> (!it).array[i] == (*it).array[i+1])`。
ずらしの全称量化子がループ不変条件を跨いで運ばれるため、拡張ソルバでもコストが高い。**カーソル版を推奨**。

## 4. IterMut と prophecy
第 1 成分は `iter_mut` が受け取った `&mut [T]` の prophecy ペアそのもので、**生成時に最終列が確定**する。
`next` は位置 `p` の要素を `Mut::new(cur.array[p], fin.array[p])` として切り出し `p += 1` するだけ。これは
Creusot の `Seq<&'a mut T>` ＋「最終値を結ぶ不変条件」を `Seq<Mut<T>> ≅ Mut<Seq<T>>`（長さが等しい前提）で
再結合したもので意味は同じだが、**`Array<Int, Mut<T>>` というソートを避けられる**のが利点（`Sort::Mut` は
unbox で消えず、配列要素にした前例が無い）。前例は `_extern_spec_slice_get_mut`（`std.rs:906-926`）/
`_extern_spec_slice_index_mut`（`:1008-1023`）の「要素の Mut を切り出し残りを store で書き戻す」形で、
IterMut ではその store が要らないぶん軽い。リスク:

- **途中 drop の不完全性**: 未消費の末尾 `fin.array[i]`（i >= p）に制約が付かず、呼び出し側は
  「触っていない要素は不変」を示せない。不健全ではない（prophecy が未制約になるだけ）が途中 `break` は
  通らない。当面は完全消費に限定し、将来 drop/resolve フックで `forall i >= p. fin[i] == cur[i]` を課す。
- `(*it).0` が `Mut` なので `*(*it).0` / `!(*it).0` と二重になる。`annot.rs` の `*` / `!` が
  タプル射影の上でこの形を受けるか要確認。
- `iter_mut` 直後は元の `&mut [T]` が借用中。`result.0 == slice` の prophecy 同一視が reborrow 解析と
  整合するか要確認。

## 5. `for` ループと、trait メソッドへの仕様の付け方
`for x in e` は MIR 上 `IntoIterator::into_iter(e)` ＋ ループ内 `Iterator::next(&mut it)` に脱糖されるので
3 節が揃えば原理的にそのまま動く。ループヘッダは支配辺から求まり（`local_def.rs:875` `loop_header_of`）、
`invariant!` はどこに置いても囲むループヘッダに付く（`:834-871`）ので本体先頭に書けばよい**はず**。ただし
`for` を通す ui テストは**存在しない**（`traits/rustc-coroutine.rs` は手で while let に脱糖済み・
`//@ignore-on-host`、`std.rs` に `Range::next` の仕様も無い）。probe で先に確かめること。
既存テストは**自前 `Iterator` trait**（`invariant`/`completed`/`step` の 3 述語、本体は生 SMT-LIB2）方式
（`iterators/annot_range_next.rs`, `traits/take.rs`, `traits/map.rs`）で、adapter の合成には要るが
具体イテレータには過剰（抽象述語のせいで pcsat が具体的な列の値を見失う）。
**推奨（二層）**: (i) 具体イテレータ三種は core の trait メソッドに直接 extern spec を貼り述語を挟まない。
(ii) adapter は既存の自前 trait 方式を維持。接続は将来課題とし、まず (i) 単独でループが通ることを目標にする。

## 6. 追加する ui テスト（pass/fail の対、`tests/ui/pass/iterators/`）
| 名前 | pass の内容 | fail 側の壊し方 |
|---|---|---|
| `slice_iter_len.rs` | `iter()` で回して `count == len` | `count == len + 1` |
| `slice_iter_sum.rs` | `while let Some(x)` で総和、不変条件はカーソルと部分和 | 不変条件を off-by-one |
| `slice_iter_elem.rs` | `next()` が `Some(&a[0])` を返す（量化子なし） | `Some(&a[1])` を主張 |
| `slice_iter_generic.rs` | 要素型が型パラメータ `T` で `iter()` が通る（1 節 (a)/(b) の回帰） | 長さの主張を壊す |
| `vec_into_iter.rs` | `Vec<i64>` を `into_iter()` で消費して総和 | 総和をずらす |
| `vec_ref_into_iter.rs` | `(&v).into_iter()` が `slice::Iter` になり `v` は不変 | `v.len()` が変わると主張 |
| `slice_iter_mut_set.rs` | `iter_mut()` で全要素 `*x = 0`、事後 `forall i. v[i] == 0` | `v[0] == 1` を主張 |
| `slice_iter_mut_incr.rs` | `*x += 1`、`(!v).array[i] == (*v).array[i] + 1` | `+ 2` を主張 |
| `for_slice_iter.rs` | 同内容を `for` 構文で書き脱糖経路を固定 | 同上 |

probe（pass のみ、`pass/rustc_coroutine/probe_*.rs` と同じ位置づけ）: Model impl 単独で
`slice::Iter<'_, i64>` が通るか／`(Mut<Seq<Int>>, Int)` で `*(*it).0` `!(*it).0` が書けるか／
`for` 本体の `invariant!` がループヘッダに付くか。

## 参照
`std.rs:190-246`, `:250-252`, `:348-390`, `:759-877`, `:879-1023`, `:1039-1052`;
`src/refine/template.rs:279-309`, `:317-341`, `:346-436`, `:702-821`;
`src/analyze/local_def.rs:46-108`, `:834-880`; `src/analyze/annot_fn.rs:857-912`; `src/chc.rs:950-968`;
`src/chc/unbox.rs:12-41`; `tests/ui/pass/iterators/{range.rs,annot_range_next.rs}`,
`tests/ui/pass/traits/{take.rs,map.rs}`, `tests/ui/pass/rustc_coroutine/README.md`（段階 4）。
