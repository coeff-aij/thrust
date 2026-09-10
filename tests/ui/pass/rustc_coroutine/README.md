# rustc_coroutine: layout() の panic safety 検証の段階計画

対象は `tests/ui/pass/traits/rustc-coroutine.rs`（rustc の `rustc_abi::layout::coroutine`
とその依存）。最終目標は `layout()` が panic しないことの証明で、他の関数はその証明に
必要な最小限の仕様だけを持つ。このディレクトリの各ファイルは対象から該当部分を
**そのまま抜き出し**、注釈（requires/ensures/predicate/trusted/Model 宣言）だけを足した
もの。`tests/ui/fail/rustc_coroutine/` に同名の fail 側を置く。

対象ファイル本体は書き換えない（許すのは for の脱糖、`?` の match 化、外部クレート定義の
展開、自前イテレータへの差し替え、panic メッセージの削除のみ）。Thrust が扱えない構文は
書き換えず、trusted を付けて未対応として記録する。

## 段階と状態

| 段階 | 内容 | ファイル | 状態 |
|---|---|---|---|
| 1 | 値型（Size/Align/Integer/Primitive/Scalar/Niche/TargetDataLayout） | values.rs | **緑**（pass/fail）。obj_size_bound・pointer_size_in に dl_wf の requires、data_layout に述語 dl_of の ensures。Primitive::size/align は trusted のまま（forall 経由の前提で pcsat が Unknown） |
| 2 | Idx トレイト、IndexSlice/IndexVec | idx.rs | **Idx は緑**（can_new/index_is、plus/increment_by 検証）。IndexSlice/IndexVec はジェネリック `[T]` 待ちで未着手 |
| 3 | DenseBitSet/BitMatrix/BitIter の集合抽象（trusted） | bitset.rs | **緑**（pass/fail）。mem/inserted/no_mem で insert/contains/insert_all、BitIter::next に添字上界 |
| 4 | 自前イテレータの仕様 | idx.rs（IdxRange/WordIter） | **緑**。next の仕様は隣接 inherent impl の extern_spec ラッパで記述。SliceIter/IterEnumerated は `[T]` 待ち |
| 5 | coroutine_saved_local_eligibility | eligibility.rs | **下書き**（ignore-on-host）。requires/ensures と各ループの invariant! を転記。IndexSlice の `[T]` で解析が止まる |
| 6 | univariant の trusted 仕様 | univariant.rs | **下書き**（ignore-on-host）。置換の契約は IndexSlice の要素アクセスが書けず requires/ensures(true)。`[T]` で止まる |
| 7 | layout() 統合 | layout.rs | **下書き**（ignore-on-host）。各 panic 箇所に TODO(proof)。impl Trait 引数のため仕様が付けられない（feat/spec-with-impl-trait-args で解消予定） |

verify 済みの数値は coar:latest = e8a1748680a3 で測定（values/idx/bitset は 120 秒の solver timeout が必要）。
coar:latest はその後 dfad2b27d12e（develop 933d14b48）に付け替わっており、新イメージでは未再測定。
見つけた制限は notes/known_issues.md に、調査メモは notes/ の各ファイルにある。

### 残り 3 段階が止まっている場所

- **ジェネリックなスライス `[T]`**（IndexSlice の `raw: [T]` と `IntoSliceIdx<I, [T]>`）: 段階 2 の
  IndexSlice/IndexVec、段階 5〜6 の解析がここで止まる。スライス対応は別作業。
- **std のイテレータ adapter 連鎖**（map/filter/collect/zip/enumerate/extend/retain/all）と
  `vec::IntoIter` / `slice::IterMut`: 段階 7 の本体。Vec/slice イテレータの定義は別作業に差し替え。
- **forall-sort のジェネリック関数の未検査問題**: 直るまで、ジェネリック関数を含む pass は fail 側の
  Unsat で裏取りする（notes/known_issues.md）。
- **Thrust 側の修正ブランチ**（main ベース: feat/int-casts、fix/enum-discriminants、
  feat/newtype-scalar-consts、fix/unsigned-const-sign、feat/unsigned-param-nonneg、
  feat/spec-on-trait-impl-methods、feat/spec-with-impl-trait-args、feat/int-model-all-widths、
  feat/std-specs-clone-vec-checked-sub、fix/datatype-decl-order、統合 integration/thrust-fixes、
  forall-sort ベース: fix/trait-item-ty-owner、fix/singleton-spec-params）はレビュー待ちで未マージ。
  values.rs でコメントアウトした derive と AbiAlign::min/max は fix/enum-discriminants が入れば戻せる。

## Thrust 側の前提（未対応）

- ジェネリックなスライス `[T]`（IndexSlice の `raw: [T]`、`IntoSliceIdx<I, [T]>`）
- `as` キャスト（Idx for u32、layout() の `as u128` / `as u32`）: 設計メモを別途作成
- std のイテレータ型（vec::IntoIter、slice::IterMut）と adapter 連鎖
  （map/filter/collect/zip/enumerate/extend/retain/all）: Vec/slice の別作業の定義に差し替え
- ジェネリック型の derive（Hash/Clone）、cmp::Ordering の負の判別子、PhantomData の
  eq/clone、Debug、const generic 配列、i64 を超える整数定数

## 段階 5: coroutine_saved_local_eligibility の仕様案

前提（requires）:

- `forall v < variant_fields.len(), f < variant_fields[v].len(): variant_fields[v][f].index() < nb_locals`
- `storage_conflicts.num_rows == nb_locals && storage_conflicts.num_columns == nb_locals`
- `forall n <= nb_locals: FieldIdx::can_new(n)`、`forall v < variant_fields.len(): VariantIdx::can_new(v)`

保証（ensures。`a = result.1`、`inel = result.0` とする）:

1. `forall l < nb_locals: a[l] == Unassigned ==> forall v, f: variant_fields[v][f] != l`
2. `forall l: a[l] == Assigned(v) ==> v < variant_fields.len() && (exists f: variant_fields[v][f] == l) && (forall v' != v, f: variant_fields[v'][f] != l)`
3. `forall l: a[l] == Ineligible(x) ==> exists k: x == Some(k) && k < card(inel)`（k は inel の列挙位置）
4. `forall l: mem(inel, l) <==> (exists x: a[l] == Ineligible(x))`

ループ不変条件:

- 第 1 ループ（variant ごと、処理済み variant を `0..k` とする）: 処理済み variant に現れる
  local は Unassigned でない。Assigned(v) なら v < k かつその local は v 以外の処理済み variant
  に現れない。Ineligible なら inel に属する。処理済みでない variant の local への言及なし。
- conflict ループ: Assigned → Ineligible の遷移だけが起きる。性質 1, 2 の「現れない」側と 4 を保存。
- used_variants ブロック: どちらの分岐でも 1, 2, 4 を保存（count() の値は panic safety に無関係）。
- 最終ループ（`ineligible_locals.iter().enumerate()`）: `idx` は列挙位置、`local` は inel の要素
  （bitset 仕様の elems から）。Some(idx) の idx が card 未満であることを与える。

必要な下位仕様: IndexVec::from_elem_n（全要素 Unassigned、長さ nb_locals）、IndexVec の
添字（index_is 経由で `< len`）、bitset の new_empty/insert/contains/insert_all/iter、
IterEnumerated と SliceIter の next。

## 段階 6: univariant の trusted 仕様案

```
requires: forall i < fields.len(): niche_wf(fields[i].largest_niche, dl)   // Niche::available の前提
ensures:  result == Ok(l) ==>
            l.fields == FieldsShape::Arbitrary { offsets, in_memory_order }
            && offsets.len() == fields.len()
            && in_memory_order.len() == fields.len()
            && forall k < fields.len(): in_memory_order[k].index() < fields.len()
            && exists inv: forall k < fields.len():
                 inv[in_memory_order[k].index()] == k && in_memory_order[inv[k]].index() == k
```

scalar_pair と univariant_biased は univariant からしか呼ばれないので触らない。
`F: Deref<Target = &LayoutData>` は univariant の中でしか deref されないので、layout() 側では
F に仕様は要らない。

## 段階 7: layout() の証明で必要になる事実

- prefix 構築後: `prefix_layouts.len() == 元の長さ + 1 + card(ineligible_locals)`
  （extend は ineligible_locals.iter() の列挙個数だけ push する）。
- `prefix.fields` は Arbitrary（段階 6）。`split_off(b_start)` は `b_start <= offsets.len()`
  （`tag_index + 1 <= len`）。`offsets_b.len() == card(ineligible_locals)`。
- a/b 分割: in_memory_order が 0..n の置換なら、b 側に来る要素はちょうど n - b_start 個で、
  値は 0..n-b_start の置換。これは数え上げの補題で、SMT では自動では出ないので trusted な
  補題関数として与える（`lemma_permutation_split`）。invert_bijective_mapping の requires
  は「全要素が len 未満」で足りる。
- variant ループ: `Unassigned => unreachable!()` と `Assigned(_) => unreachable!()` は段階 5
  の 1, 2 から。`offsets_and_memory_index.next().unwrap()` は Assigned の個数が
  `variant_only_tys` の長さ（filter で残った個数）と一致することから。
  `combined_in_memory_order[memory_index]` の添字は `promoted_memory_index.len() + memory_index
  < invalid_field_idx`（memory_index は置換の逆写像なので len 未満）と
  `promoted_memory_index[field_idx]` の値が len 未満であることから。
  `field_idx.unwrap()` は段階 5 の 3 から。`promoted_offsets[field_idx]` は
  `field_idx < card(ineligible_locals) == offsets_b.len()` から。
- VariantLayout::from_layout の panic は `variant.fields` を Arbitrary に置き直した直後なので到達しない。
- 残る前提: variant_fields が空でない（`len() - 1` は overflow でスコープ外だが、
  tag の valid_range に影響）、TargetDataLayout の dl_wf、入力 layout の niche_wf。
