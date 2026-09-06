# 設計メモ: 整数→整数 `as` キャストの追加

対象: worktree `.claude/worktrees/rustc-coroutine` (branch `rustc-coroutine`)。現状
`Rvalue::Cast(CastKind::IntToInt, ..)` は `src/analyze/basic_block.rs:684` の総括アーム
`_ => unimplemented!("rvalue={:?} ...")` に落ちて ICE する。過去の「全 IntToInt を恒等」案は
truncation と符号再解釈を黙って落とすため却下済み。

## 1. Rust の `as` セマンティクスと Int モデルでの符号化

Rust の整数間 `as` は「下位 N ビットを取り目標型の符号性で読む」ことに尽きる (N は目標型の幅)。
- 拡大 (目標型の表現範囲 ⊇ 元の型の範囲): 値は保存される。
- 縮小: 2^N を法とする切り捨て。
- 同幅の符号違い: ビット列の再解釈。

Thrust は全整数幅を単一の `rty::Type::Int` (数学的整数, `src/rty.rs:1018`, `src/chc.rs:294`) で表す。
そこでの正確な符号化 (SMT-LIB `mod` は Euclidean で、正の除数に対し常に非負):

- `x as uN` = `x mod 2^N`
- `x as iN` = `((x + 2^(N-1)) mod 2^N) - 2^(N-1)`
- 恒等となるのは目標型の範囲が元の型の範囲を含むとき:
  - `uM -> uN` (M <= N)
  - `iM -> iN` (M <= N)
  - `uM -> iN` (M < N、真に狭いときのみ。`u32 -> i32` は恒等でない)
  - `iM -> uN` は常に非恒等 (負値が回り込む)

ポインタ幅は 64 と仮定する (`usize = u64`, `isize = i64`)。実装では仮定を焼き込まず、
`int_size_and_signed` 経由で MIR から取る (§4)。

## 2. 未追跡のオーバーフローとの関係

`+ - *` は `src/analyze/basic_block.rs:509-520` で `Term::add/sub/mul` にそのまま落ち、ラップは
一切モデル化されていない (テストは `-C debug-assertions=false`)。よってキャスト直前の Int 値は型の
範囲外でありうる。`mod` 符号化が実プログラムの値と一致するのは「キャスト前の値が実際の値と等しい」
ときだけで、**健全性は既存の no-overflow 仮定に対して相対的**。既存の穴を持ち越すだけで新規の穴ではない。

選択肢:
- (A) 正確 (mod) 符号化。全域関数のまま、新しい証明義務を作らない。切り捨て・符号再解釈を明示する。
- (B) 恒等 + 範囲チェック (目標型に収まることを証明義務にする)。線形算術のままで解きやすいが、
  ガードのない縮小キャストが即 Unsat になる (実例: rustc-coroutine.rs:892)。

**推奨は (A)**、ただし恒等ケース (§1) では `mod` 項を作らず素通しにする。理由: (B) は「範囲外なら
検証失敗」という新しい意味論を持ち込み、オーバーフローを無視している現状と整合しない。(A) は
恒等ケースで既存の精度を 1 ミリも落とさず、非恒等ケースでのみ `mod` を導入する。
`mod` が CHC ソルバの解けやすさを落とすなら、(B) を「非恒等キャストにのみ課すオプション」として
後から足せる。

## 3. 定数の問題 (2^64, 2^128)

`chc::Term::Int` は `i64` (`src/chc.rs:568`, `Term::int` は `src/chc.rs:795`)。よって
`2^63`, `2^64`, `2^127`, `2^128` はリテラルとして作れない。影響するのは i64/u64/usize/isize/i128/u128
を**目標**とする非恒等キャストのみ。

対処案 (推奨は a):
- (a) `Term::Int` に触らず、法を積で組む: `pow2(64) = Term::int(1<<32).mul(Term::int(1<<32))`。
  SMT-LIB では `(* 4294967296 4294967296)` となり、ソルバ側で畳まれる。Thrust に定数畳み込みパスは
  ないが不要。ヘルパ `fn pow2(bits: u32) -> chc::Term` 一つで済む。
- (b) `Term::Int(i64)` を `i128`/BigInt に広げる。i128 でも `2^128` は入らず u128 目標には (a) が要る。
  `src/analyze/basic_block.rs:350-356,394` 等に波及する割に得が少ない。
- (c) 当面 64/128 bit 目標の非恒等キャストは `unimplemented!()` のまま残す (CLAUDE.md 的に許容)。
  最小実装として妥当。

`x as u128` (x: usize) は §1 の `uM -> uN`, M<=N に当たり**恒等**なので、定数は一切要らない。
rustc-coroutine.rs の u128 キャスト 5 箇所は全てこれ。

## 4. 実装スケッチ

**basic_block.rs**: `src/analyze/basic_block.rs:645`/`:659` の `Rvalue::Cast` 群の隣に
`Rvalue::Cast(mir::CastKind::IntToInt, operand, ty)` アームを追加。
注意: rustc の `IntToInt` は `bool as i32` / `char as u32` も含む。元・先の `TyKind` が両方
`Int`/`Uint` のときだけ処理し、それ以外は既存どおり `unimplemented!()` に落とす。
- 元の MIR 型: `operand.ty(&self.local_decls, self.tcx)` (`:860` の `discr.ty(...)` と同型)。
- 幅と符号: `ty.int_size_and_signed(self.tcx)` -> `(Size, bool)`、`size.bits()`
  (`:868` で既に使用)。ここから §1 の恒等判定と法を決める。
- 項の構築: `UnaryOp` (`:486-499`) と同じく `PlaceTypeBuilder::default()` -> `subsume` ->
  `builder.build(rty::Type::Int, cast_term)`。

**chc.rs**: `mod`/`div` の関数記号は現状**存在しない** (`Function` 定数一覧は `src/chc.rs:500-514`、
`ADD/SUB/MUL/EQ/GE/GT/LE/LT/AND/OR/NOT/NEG/STORE/SELECT/ITE` のみ)。追加が必要:
- `pub const MOD: Function = Function::infix("mod");` (`src/chc.rs:514` の隣)
- `Function::sort` (`src/chc.rs:476`) に `Self::MOD => Sort::int()` のアーム
- `Term::mod_` ヘルパ (`add/sub/mul` が並ぶ `src/chc.rs:864-874` の隣)
出力側は追加不要: smtlib2 は `Term::App` を記号名で一般に出す (`src/chc/smtlib2.rs:157`)、
`unbox.rs:25` も透過。ただし拡張ソルバ (COAR/pcsat, AGENTS.md 参照) が `mod` を読めるかは未確認。

**annot_fn.rs**: 仕様中の `as` は現状 `ExprKind::Cast` のアームが無く落ちる
(`to_formula_or_term` の分岐は `src/analyze/annot_fn.rs:698-` )。仕様は Int モデル上で書くので
`as` は本来不要。当面は非対応のままとし、必要になったら `cast_term(src_ty, dst_ty, term)` を
共有ヘルパに切り出して両側で使う (`BinOpKind::Add` が `src/analyze/annot_fn.rs:710` で
`Term::add` を直に呼ぶのと同じ粒度)。

**注意点 (実装前に潰すべき前提)**: Thrust は符号なし型に `>= 0` の篩を**付けていない**
(`src/refine/template.rs:319,708` は無条件に `rty::Type::int()` を返す)。そのため
「`assert!(idx <= u32::MAX as usize)` の後で `idx as u32 == idx`」は `0 <= idx` が無いと
証明できない。下記 `cast_bound_check` テストはこの前提を要求する。

**追加する ui テスト** (CLAUDE.md の pass/fail ペア。`pass` は `//@check-pass`、
`fail` は `//@error-in-other-file: Unsat`):
- `cast_widen.rs`: `u32 -> usize`, `i32 -> i64` が値を保つ / fail は等式を崩す。
- `cast_narrow_wrap.rs`: `x: u32` (>= 2^16) の `x as u16 == x - 65536` / fail は `== x`。
- `cast_sign_reinterpret.rs`: `x: i32` (負) の `x as u32 == x + 4294967296` / fail は `== x`。
- `cast_bound_check.rs`: `x <= u32::MAX as usize` かつ `x >= 0` のとき `x as u32 == x` (rustc-coroutine.rs:313-314 と同形)。

## 5. `tests/ui/pass/traits/rustc-coroutine.rs` の `as` 使用箇所

| 行 | 式 | 型 | 分類 |
|---|---|---|---|
| 194 | `self.word.trailing_zeros() as usize` | u32 -> usize | 拡大 (恒等) |
| 274 | `word.count_ones() as usize` | u32 -> usize | 拡大 (恒等)。関数は `#[thrust::trusted]` なので現状は解析されない |
| 313 | `u32::MAX as usize` | u32 -> usize | 拡大 (恒等) |
| 314 | `idx as u32` | usize -> u32 | **縮小** (法 2^32)。313 の assert でガード済み |
| 318 | `self as usize` | u32 -> usize | 拡大 (恒等) |
| 483, 495 | `x.index() as u128` | usize -> u128 | 拡大 (恒等) |
| 484, 496 | `self.len() as u128` | usize -> u128 | 拡大 (恒等) |
| 786 | `(variant_fields.len() - 1) as u128` | usize -> u128 | 拡大 (恒等)。ただし `- 1` はオーバーフロー未追跡 |
| 892 | `promoted_memory_index.len() as u32` | usize -> u32 | **縮小** (法 2^32)。ガード無し |
| 1175 | `size_as_align as u64` | u32 -> u64 | 拡大 (恒等) |

11 箇所中 9 箇所が恒等ケース。目標に必要なのはまず **恒等ケースの実装だけ** で、314 と 892 の
2 箇所が法 2^32 (i64 に収まる定数) を要求する。64/128 bit を法とする縮小は 1 箇所も無い。
したがって §3(c) の最小実装 (恒等 + 幅 <= 32 の縮小) でこのファイルは通る見込み。
