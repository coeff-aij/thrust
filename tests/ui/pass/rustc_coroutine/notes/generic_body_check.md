# ジェネリック関数の本体検証: 調査メモ

## 結論(要約)

コーディネータから、他セッションが CHC レベルで原因を確認済みとの連絡があったため、本探索はここで打ち切り。
確認できた事実と、他セッションの説明を突き合わせた結果を1段落にまとめる:
`src/analyze/crate_.rs::refine_fn_def` (140-149行目) は、シグネチャが型パラメータを含む
(`sig.has_param()`) かつ所有者関数がローカルで解析対象になっている場合、
`ctx.register_generic_def(owner_fn_id, local_def_id, Some(expected))` (`src/analyze.rs` 456-471行目) を
呼んで `DefTy::Generic { rty: Some(expected), .. }` を登録する。`concrete_def_ty` (`src/analyze.rs` 477-483行目)
はこれを `Some` として返すため、`crate_.rs::analyze_local_defs` (156-181行目) は
`placeholder_generic_args` (183-229行目、型パラメータをほぼ恒等のまま残す) で本体解析を1回だけ実行する
—— つまり「本体がまったく解析されない」わけではなく、型変数を抽象(uninterpreted sort, forall-sort)
として扱う形で1回だけ抽象的に解析される。ただし他セッションの報告によれば、その抽象解析で生成される
CHC は、呼び出し側 (`def_ty_with_args`, `src/analyze.rs` 560-616行目、call-site ごとに
`InstantiationKey{generic_args, caller_def_id}` でキャッシュされる具体型の節) とは別系統の
Int ソート述語を新規発行し、ジェネニック本体側の forall-sort 述語との間に定義節(defining clause)が
存在しない。そのため事前条件述語 (precondition predicate) が「空こそ真」の状態になり、
`assert!` に対応するゴール節が充足不可能にならず vacuously verified になる、との説明であった。
これは今回読んだ `register_generic_def` / `concrete_def_ty` / `analyze_local_defs` の呼び出し関係と
矛盾しない(本体解析自体は起動されるが、生成される制約が呼び出し側と接続されないため無意味化する、
という筋は自然)。

## 実測状況(打ち切り時点)

- 環境: `THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest`(`coar:latest` は
  CI ピン `ghcr.io/hiroshi-unno/coar@sha256:7314...f011` と同一タグ済みイメージ)。
- ケース4 (`fn h(_t: i64) -> i64 { assert!(3 == 4); 1 }`、単相制御群): **Unsat**(期待通り、pcsat)。
- ケース1・2・3・5(ジェネリック本体を含む4ケース: assert付き呼び出しあり/なし、false ensures、
  requires違反の呼び出し)は、いずれも pcsat 実行が **ICE ではなく COAR 側パースエラー**で失敗した:
  `main.exe` が `(declare-forall-sort a0)` を含む smt2 を読めず
  `Failure("parse error : ...")` を吐いて落ちる。これは今回使った `coar:latest` イメージの
  `pcsat_tbq_ar.json` 設定が forall-sort 宣言をサポートしていないという、ソルバー/環境側の制約であり、
  Thrust 側の生成する CHC の妥当性(vacuous かどうか)自体を直接は確認できなかった。
  時間の都合で z3 バックエンドでの再実行は行っていない。

## コード上の追加の観察

- `register_deferred_def`(Analyze モード、`src/analyze.rs` 423-425行目)は定義されているが、
  リポジトリ内のどこからも呼ばれていない(`register_deferred_def_without_analysis` のみが
  `crate_.rs:144` から呼ばれる)。したがって `def_ty_with_args` 内の
  `deferred_ty_mode.is_some_and(|mode| mode.should_analyze())` (`src/analyze.rs:602`) は
  実行時に常に `false` であり、呼び出しサイトごとの具体型インスタンス化に伴う本体再解析
  (call-site analyze) の分岐は事実上デッドコードになっている。これは今回の主たる論点
  (ジェネリック本体の抽象1回解析が vacuous になる件)とは別の観察点だが、
  「ジェネリック本体がいつどのモードで解析されるか」を追う際の副次的な事実として記録する。

## ファイル/行

- `src/analyze/crate_.rs:110-154`(`refine_fn_def`、`register_generic_def` / `register_deferred_def_without_analysis` の分岐)
- `src/analyze/crate_.rs:156-181`(`analyze_local_defs`、`concrete_def_ty` が `Some` のものだけ `placeholder_generic_args` で解析)
- `src/analyze/crate_.rs:183-229`(`placeholder_generic_args`)
- `src/analyze.rs:418-471`(`register_def` / `register_deferred_def` / `register_deferred_def_without_analysis` / `register_generic_def`)
- `src/analyze.rs:477-483`(`concrete_def_ty`)
- `src/analyze.rs:560-616`(`def_ty_with_args`、call-site ごとのインスタンス化とキャッシュ、未使用の Analyze モード分岐)

## 未検証(打ち切りのため)

- ケース1・2・3・5 の z3 バックエンドでの結果。
- pcsat 側で forall-sort 対応の COAR イメージ/設定を使った場合の結果。
- 「本体解析が呼ばれる」ことと「生成される制約が呼び出し側と非接続で vacuous になる」ことの
  両立を、実際の CHC ダンプ(本メモの pcsat 出力に含まれる smt2 相当)で裏付ける追加確認。
  上記の pcsat 出力はパースエラー前のログに smt2 全文を含んでいるため、次に着手する場合は
  そのログ(本エージェントの実行結果)から forall-sort 述語と呼び出し側述語の接続有無を
  直接読むのが早い。
