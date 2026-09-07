# MVP 実装プラン

提案書 (`docs/proposal.html`) の 05 / MVP セクションを完遂するための計画。

## ゴール

| Phase | 内容 | 状態 |
| --- | --- | --- |
| 1. COMPILE | 最小言語の定義と ESM 出力（基本型・ADT・純粋関数、`index.js` / `index.d.ts`、Node での差分テスト） | 完了 |
| 2. VERIFY | 変換の保証（small-step semantics、type soundness、compiler correctness、proof manifest） | 一部 |
| 3. SHIP | npm 開発体験（source maps、tree shaking、CI）と、処理系そのものの配布（利用者のパッケージの雛形） | 完了 |

### Phase 2 の到達点

- proof manifest — 完了。`Claim` が証明項を持つので、定理を消すと `lake build` が落ちる
- JS の意味論の模型（`JsSem.lean`）と、出荷する成果物がリファレンス意味論と一致することの実行時検査
  （`Agree.lean`）— 完了
- type soundness — 証明済み（`Sound.lean`）。リテラル・変数・条件式・`let` 束縛・単項演算・二項演算に
  ついて、コンパイラが型 `T` と判断した式を `eval` が評価して値が返るなら、その値は `T` を満たす。
  生成コードは被演算子の型で分岐するので、これが無いと `+` が連結か加算かを決められなかった
- compiler correctness — リテラル・変数・条件式・`let` 束縛・単項演算、および二項演算のうち
  `+` / `-` / `*` / `/` / `%` / `min` / `max` / `<` / `<=` / `>` / `>=` / `&&` / `||` / `++` について
  証明済み（`Correct.lean`）。算術は `Int53` / `UInt32` / `BigInt` の 3 つの被演算子型すべてを覆って
  いて、`UInt32` の巻き戻しも `>>> 0` / `Math.imul` の模型と突き合わせてある。比較は順序を持つ 4 つの
  型すべてで、`String` は生成コードの `__strcmp` がコードポイント順に並べるところまで含む。断片の外は
  `Agree` の実行時検査が受け持っている。残っているのは等値
- small-step semantics — 継続を明示した抽象機械として実装（`Step.lean`）。big-step との一致は
  成果物のベクタ全件について実行時に確かめている。短絡評価を壊すと 125 件の食い違いとして落ちる

### Phase 3 の到達点

- source map / tree shaking / CI — 完了
- 配布 — 完了。`emit` はライブラリ側にあり、利用者は自分の Lean パッケージで `LeanTs` に依存し、自分の
  manifest を `emit` に渡す小さな実行ファイルを持つ。**npm に出るのは利用者の成果物のほう**で、
  `packages/verified-example` はその形の見本にとどまる。雛形は `templates/verified-package/` にあり、
  空のディレクトリから通ることを `scripts/check-template.sh` が CI で確かめている
- 定理は証明項であってデータではないので、プログラムをファイルで受け取る CLI では運べない。だから
  配布物は「CLI」ではなく「利用者側のパッケージの雛形」になっている

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
LeanTs/Syntax.lean   表層構文: type% / decl% / expr% を Core 項へ展開する
LeanTs/Builder.lean  Core 項を直接組み立てるための記法（Tests が使う）
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

## 境界: 宣言した型を満たす引数

`eval` と生成した JS が一致することは、**宣言した型を満たす引数について**主張する。公開関数は本体に
入る前に引数を宣言した型と構造的に照合し、破っていれば `eval` と同じ `typeError` を投げるので、この
前提は呼び出し側が何を渡しても成り立つ。`.d.ts` は同じことを TypeScript の呼び出し側に静的に伝える。

検査は `eval` の `Value.hasTy` を写したもので、フィールドは順序と個数まで一致を要求する。欠けた
フィールド・余分なフィールド・並べ替えは、どれも型エラーになる。

- `Int53` と `UInt32` の取り違えだけは検査できない。JS ではどちらもただの数で、区別は Lean 側の値の
  表現にしかない。ベクタ生成器も、この 2 つの取り違えを型エラーとして期待しない
- 自分自身を含む型は、境界に出るかどうかに関わらず宣言の時点で拒否する。型を展開して回る処理は入口の
  検査の記述子だけではなくベクタ生成にもあり、自分に戻る型ではそのどれもが終わらない
- 辞書は `Map` であって素のオブジェクトではない。文字列キーの素のオブジェクトは `__proto__` や
  `constructor` をキーとして受けてしまう。1 つのキーを 2 度持つ辞書は `Map` に写せないので、境界で
  型エラーになる

## 進め方

幅優先で Core を作らない。まず縦に一本通す。

1. `add : Int53 → Int53 → Int53`（溢れ trap つき）だけを Core → `eval` → `Compile` → ディスク上の
   `index.js` / `index.d.ts` まで通し、Vitest が生成物を import して差分テストする
2. そこから横に広げる: Bool / if → inductive / match → structure → Array → 高階コンビネータ →
   String / UInt32 / BigInt

停止性はコンパイラが担保している。各宣言は自分より前の宣言だけを見てコンパイルされるので、自己再帰も
相互再帰も書けず、走査は `map` / `filter` / `reduce` が受け持つ。`eval` の fuel は証明を閉じるための
装置であって、サブセットの意味論ではない。

差分テストの形: `leants` が `vectors.json`（`[{fn, args, expected}]`、`expected` は `eval` の結果で
trap も符号化する）を出力し、Vitest が生成された ESM を実行して突き合わせる。

出力先は実際の npm パッケージの形にする（`packages/verified-example/`）。提案書の配布ノードそのもので
あり、差分がレビューできる。
