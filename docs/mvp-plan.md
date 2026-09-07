# MVP 実装プラン

提案書 (`docs/proposal.html`) の 05 / MVP セクションを完遂するための計画。

## ゴール

| Phase | 内容 | 状態 |
| --- | --- | --- |
| 1. COMPILE | 最小言語の定義と ESM 出力（基本型・ADT・純粋関数、`index.js` / `index.d.ts`、Node での差分テスト） | 完了 |
| 2. VERIFY | 変換の保証（small-step semantics、compiler correctness、proof manifest） | 一部 |
| 3. SHIP | npm 開発体験（source maps、tree shaking、CI / package publishing） | 進行中 |

### Phase 2 の到達点

- proof manifest — 完了。`Claim` が証明項を持つので、定理を消すと `lake build` が落ちる
- JS の意味論の模型（`JsSem.lean`）と、出荷する成果物がリファレンス意味論と一致することの実行時検査
  （`Agree.lean`）— 完了
- compiler correctness — リテラル・変数・条件式の断片について証明済み（`Correct.lean`）。
  算術・関数呼び出し・`match`・配列は未証明で、`Agree` の実行時検査が受け持っている
- small-step semantics — 継続を明示した抽象機械として実装（`Step.lean`）。big-step との一致は
  成果物のベクタ全件について実行時に確かめている。短絡評価を壊すと 210 件の食い違いとして落ちる

## Approach

**Core 言語を Lean に deep embedding する。** 通常の Lean `def` を `Lean.Expr` / LCNF 経由で読む
frontend は採らない。

理由は Phase 2 にある。compiler correctness は「ソース言語の意味論」と「ターゲット言語の意味論」が
両方とも自分の手にあって初めて述べられる。`Lean.Expr` を入力に取ると、ソース側の意味論は Lean 本体の
elaborator と compiler に委ねられ、証明すべき命題そのものが書けない。加えて `brecOn` / `casesOn` /
`OfNat` インスタンスの展開といった、サブセットの本質と無関係なノイズが Phase 1 を重くする。

したがってサブセットは Lean の中の独立した AST として定義し、その上に `eval` を置く。この `eval` が
リファレンス意味論であり、Phase 2 の定理はすべてこれと JS 側の評価との一致として述べられる。

```
LeanTs/Core.lean     Ty / Expr / Decl / Program  … サブセットの構文（deep embedding）
LeanTs/Eval.lean     eval : Program → ... → Except Err Value  … リファレンス意味論（fuel 付き big-step）
LeanTs/Js.lean       JS AST + ESM printer + .d.ts printer
LeanTs/Compile.lean  Program → Js.Module  … Phase 2 で正しさを証明する対象
LeanTs/Syntax.lean   制限 Lean 風に書くための macro 層（Core AST を生む）
Main.lean            leants 実行ファイル: index.js / index.d.ts / proof-manifest.json / vectors.json を出力
```

「Restricted Lean」は Lean に埋め込まれた DSL として満たす。定理は `eval` 上で述べる。

通常の `def` を読む frontend は将来の課題として明示的に後回しにする。

## JS 意味論との対応（この設計の中身そのもの）

サブセットの価値は「JS の意味論に合わせる」ことにあるので、差分テストが最初の乱数で踏む箇所を先に決める。

| 論点 | 決定 |
| --- | --- |
| ゼロ除算 | Lean は `/ 0 = 0`、JS は `Infinity` / `NaN`。両方 trap させる（`eval` は `Except` エラー、JS は throw） |
| Int53 溢れ | JS は 2^53−1 を超えると精度が落ちる。wrap せず trap する |
| 整数除算の丸め | JS は truncation。Lean 側も truncating 除算に固定し、`/` `%` をそのまま使わない |
| UInt32 | 加減算後に `>>> 0`、乗算は `Math.imul`、除算は truncation + ゼロ検査 |
| String 長 | Lean はコードポイント、JS の `.length` は UTF-16 単位。`Array.from(s).length` を出力する |
| 構造的等価 | Lean の `==` と JS の `===` は一致しない。型ごとに `eq` 関数を生成する |
| 負のゼロ | JS では `0 - 0` も `-4 % 2` も `-0` になる。Int53 は数学的な整数なので `+0` に正規化する |
| inductive 表現 | 一律にタグ付きオブジェクト `{ tag, ... }`。`Option` を `T \| null` に特殊化しない（入れ子で壊れる） |

## 前提: 宣言した型を満たす引数

`eval` と生成した JS が一致することは、**宣言した型を満たす引数について**主張する。`.d.ts` が
TypeScript の呼び出し側に対してこれを担保する。

型を破った呼び出し（`Int53` に 2^60 を渡す、`String` に数値を渡す）では両者は割れうる。`eval` は
入口で引数の型を検査して `typeError` を返すが、生成した JS は検査していないため。公開関数の入口で
実行時に引数を検証するのは follow-up とする。

## 進め方

幅優先で Core を作らない。まず縦に一本通す。

1. `add : Int53 → Int53 → Int53`（溢れ trap つき）だけを Core → `eval` → `Compile` → ディスク上の
   `index.js` / `index.d.ts` まで通し、Vitest が生成物を import して差分テストする
2. そこから横に広げる: Bool / if → inductive / match → structure → Array → 構造的再帰 →
   String / UInt32 / BigInt

停止性はまだ検査していない。非停止な定義はサブセットから外す方針だが、現状は `eval` の fuel が
尽きるだけで、コンパイラは通してしまう。構造的再帰の検査は Phase 2 の課題。

差分テストの形: `leants` が `vectors.json`（`[{fn, args, expected}]`、`expected` は `eval` の結果で
trap も符号化する）を出力し、Vitest が生成された ESM を実行して突き合わせる。

出力先は実際の npm パッケージの形にする（`packages/verified-example/`）。提案書の配布ノードそのもので
あり、差分がレビューできる。
