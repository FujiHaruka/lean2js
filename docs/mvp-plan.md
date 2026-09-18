# MVP 実装プラン

提案書 (`docs/proposal.html`) の 05 / MVP セクションを完遂するための計画。

## ゴール

| Phase | 内容 | 状態 |
| --- | --- | --- |
| 1. COMPILE | 最小言語の定義と ESM 出力（基本型・ADT・純粋関数、`index.js` / `index.d.ts`、Node での差分テスト） | 完了 |
| 2. VERIFY | 変換の保証（small-step semantics、type soundness、compiler correctness、proof manifest） | 完了 |
| 3. SHIP | npm 開発体験（source maps、tree shaking、CI）と、処理系そのものの配布（利用者のパッケージの雛形） | 完了 |

### Phase 2 の到達点

到達した内容そのものは [保証の組み立て](guarantees.md)に、定理の主張・仮定・
証明の構成は [Lean のリファレンス](https://fujiharuka.github.io/lean2js/)にある。ここに残すのは、
どの項目がどのモジュールで片付いたかだけ。

- proof manifest — 完了（`Manifest.lean`）。定理の一覧も文言も `lean2js` が名前空間から集め、
  公理集合も書き出す前に検査する
- JS の意味論の模型（`JsSem.lean`）と、出荷する成果物がリファレンス意味論と一致することの実行時検査
  （`Agree.lean`）— 完了
- 出荷するファイルのテキストが、コンパイラが作った AST に読み戻せること — 証明済み
  （`Roundtrip.lean` が往復を、`Renderable.lean` が「コンパイラはその範囲の木しか作らない」を）。
  主張に但し書きは無い。`emit` は書き出す前に、出荷するテキストそのものでも同じことを確かめる
  （`Parse.lean`）
- type soundness — 証明済み（`Sound.lean`）。`Core.Expr` の 35 形すべて
- compiler correctness — 証明済み（`Correct.lean`）。35 形すべて、二項演算は 16 演算子すべて
- 宣言単位の正しさ・陰性方向 — 証明済み（`Decl.lean`）。公開関数 68 本すべてについて、返す側
  （`decl_correct`）・落ちる側（`decl_traps`）・入口で弾く側（`decl_refuses`）の 3 方向
- 網羅性 — 証明済み（`Exhaustive.lean`）。Maranget の usefulness 検査を `partial` から全域に
  書き直して健全性を示したもの
- 燃料 — 証明済み（`Cost.lean`）。`eval` を全域にしている燃料は、この処理系が受け付けるプログラムでは
  尽きない
- small-step semantics — 継続を明示した抽象機械として実装（`Step.lean`）。big-step との一致は証明済み
  （`StepAgree.lean`）

### Phase 3 の到達点

- source map / tree shaking / CI — 完了
- 配布 — 完了。利用者は自分の Lean パッケージで `Lean2Js` に依存し、`lake exe lean2js <Module>` を呼ぶ。
  実行ファイルは書かない —— `lean2js` がモジュールの `manifest` を実行時に読む。
  **npm に出るのは利用者の成果物のほう**で、
  `packages/verified-example` はその形の見本にとどまる。雛形は `templates/verified-package/` にあり、
  空のディレクトリから通ることを `scripts/check-template.sh` が CI で確かめている
- Node での検査 — 完了。`lean2js` は組み立てたパッケージを一時ディレクトリで Node に読み込ませ、全ベクタを
  本物の JavaScript で呼んで `eval` と一致したときだけ書き出す。検査は処理系の中にあるので、利用者が別に
  回す npm の道具は無く、ベクタも成果物に残らない
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
Lean2Js/Core.lean     Ty / Expr / Decl / Program  … サブセットの構文（deep embedding）
Lean2Js/Eval.lean     eval : Program → ... → Except Err Value  … リファレンス意味論（fuel 付き big-step）
Lean2Js/Js.lean       JS AST + ESM printer + .d.ts printer
Lean2Js/Compile.lean  Program → Js.Module  … Phase 2 で正しさを証明する対象
Lean2Js/Denotes.lean  Denotes: ある Core.Expr がある Lean の項を表すこと。形ごとに 1 本の補題
Lean2Js/Reify.lean    利用者の def を歩いて Core 項と証明項を同時に組み立てる
Lean2Js/Verified.lean ship_package: @[ship] な def から宣言と証明書を書く
Lean2Js/Builder.lean  Core 項を直接組み立てるための記法（Tests が使う）
Main.lean            lean2js 実行ファイル: 渡されたモジュールの manifest を読み、Node で全ベクタを当ててから index.js / index.d.ts / proof-manifest.json を出力
```

**入力は普通の Lean の `def`。** deep embedding は動かさず、その手前に「歩いて読む」層を置く ——
`Lean.Expr` から `Core.Expr` を作るときに、同時に「この Lean 関数はこの AST の解釈と一致する」の
証明項を組み立て、Lean がそれを検査する。ソース言語の意味論を形式化する必要が無いのはこのためで、
変換器は信頼しない。組み立ては [Lean frontend 計画](lean-frontend-plan.md)にある。

## JS 意味論との対応（この設計の中身そのもの）

サブセットの価値は「JS の意味論に合わせる」ことにあるので、差分テストが最初の乱数で踏む箇所を先に決める。

| 論点 | 決定 |
| --- | --- |
| ゼロ除算 | Lean は `/ 0 = 0`、JS は `Infinity` / `NaN`。両方 trap させる（`eval` は `Except` エラー、JS は throw） |
| Int53 溢れ | JS は 2^53−1 を超えると精度が落ちる。wrap せず trap する |
| 整数除算の丸め | JS は truncation。Lean 側も truncating 除算に固定し、`/` `%` をそのまま使わない |
| UInt32 | 加減算後に `>>> 0`、乗算は `Math.imul`、除算は truncation + ゼロ検査 |
| String 長 | Lean はコードポイント、JS の `.length` は UTF-16 単位。`Array.from(s).length` を出力する |
| 長さの Int53 溢れ | 配列・文字列・辞書の長さは `__i53` を通す。実在の JS エンジンでは溢れないが、模型にはリストの長さに上限がなく、リファレンス意味論はそこで trap する |
| 構造的等価 | Lean の `==` と JS の `===` は一致しない。型ごとに `eq` 関数を生成する |
| 負のゼロ | JS では `0 - 0` も `-4 % 2` も `-0` になる。Int53 は数学的な整数なので `+0` に正規化する |
| inductive 表現 | 一律にタグ付きオブジェクト `{ tag, ... }`。`Option` を `T \| null` に特殊化しない（入れ子で壊れる） |

## 境界: 宣言した型を満たす引数

`eval` が落ちるときに生成した JS が同じコードで落ちることは、**宣言した型を満たす引数について**主張する
（`eval` が値を返す側は、型が合っていることが `eval` の答えから出るので但し書きが要らない）。公開関数は
本体に入る前に引数を宣言した型と構造的に照合し、破っていれば `eval` と同じ `typeError` を投げる
（`decl_refuses`）。`.d.ts` は同じことを TypeScript の呼び出し側に静的に伝える。

検査は `eval` の `Value.hasTy` を写したものだが、オブジェクトのフィールドは**名前で**読む。並びは
縛らず、宣言に無いキーは通したうえで本体に届く前に落とす。欠けたフィールドと型を破ったフィールドは
型エラーになる。逆向き —— `.d.ts` の型を満たす引数は入口検査を通る —— も証明されており、残る但し書きは
`Int53` / `UInt32` の範囲だけ（`dts_fits_entry_check`）。返る値まで同じであることも、同じキーを 2 度
持つ辞書を除いて、入口検査が通す綴りすべてについて証明する（`ArgsDecode`）—— キーの並びも宣言に無い
キーも、正規の綴りと同じ定理が受け持つ。除いたその 1 形は模型が辞書を連想リストで持つから書けるだけで、
実行時に渡ってくる `Map` には作れない。

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

停止性はコンパイラが担保している。宣言の本体が名指しできるのは自分より前の宣言だけなので、自己再帰も
相互再帰も書けず、走査は `map` / `filter` / `reduce` が受け持つ。`eval` の fuel は証明を閉じるための
装置であって、サブセットの意味論ではない。

差分テストの形: `lean2js` が `vectors.json`（`[{fn, args, shapes?, expected}]`、`expected` は `eval` の
結果で trap も符号化し、`shapes` は引数を `.d.ts` が許すもう一つの綴り —— 並べ替え、宣言に無いキー ——
で書けと言う）を、組み立てたパッケージと一緒に一時ディレクトリへ書き、Node で生成された ESM を実行して
突き合わせる。全件が一致したときだけ出力先に書き、ベクタは出力先に残さない。

出力先は実際の npm パッケージの形にする（`packages/verified-example/`）。提案書の配布ノードそのもので
あり、差分がレビューできる。
