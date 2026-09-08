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
- 出荷するファイルのテキストが、コンパイラが作った AST に読み戻せること — 証明済み
  （`Roundtrip.lean` が往復を、`Renderable.lean` が「コンパイラはその範囲の木しか作らない」を）。
  主張に但し書きは無い。`emit` は書き出す前に、出荷するテキストそのものでも同じことを確かめる
  （`Parse.lean`）
- type soundness — 証明済み（`Sound.lean`）。`Core.Expr` の **35 形すべて**について、コンパイラが型
  `T` と判断した式を `eval` が評価して値が返るなら、その値は `T` を満たす。生成コードは被演算子の型で
  分岐するので、これが無いと `+` が連結か加算かを決められなかった。呼び出しは呼ばれる宣言の本体へ行くので、
  `compileProgram` が成功したプログラムの全宣言について「本体は宣言した返り値型でコンパイルされる」
  （`ProgramTyped`）を仮定に置く。仮定は成果物から取り出せるので、利用者の主張には現れない
- compiler correctness — **35 形すべて**について証明済み（`Correct.lean`）。二項演算は 16 演算子すべて。算術は
  `Int53` / `UInt32` / `BigInt` の 3 つの被演算子型すべてを覆っていて、`UInt32` の巻き戻しも
  `>>> 0` / `Math.imul` の模型と突き合わせてある。比較は順序を持つ 4 つの型すべてで、`String` は生成
  コードの `__strcmp` がコードポイント順に並べるところまで含む。等値は「符号化しても等値が保たれる」を
  型を付けて証明したうえで、スカラーの `===` とそれ以外の `__eq` の両方を覆う。値を組み立てるだけの形
  —— `Option` / `Result` の構成、構造体の構成と射影、配列と辞書のリテラルと読み書き、文字列操作 ——
  もすべて入っている。束縛を変えて部分式を評価する形 —— `match` と配列走査 5 つ —— も入っていて、
  `match` は腕の選択そのもの（一致した腕のテストが真、一致しなかった腕のテストが偽）を突き合わせている。
  呼び出しと関数参照も入っている —— 呼び出しは呼ばれた宣言の本体を 1 段少ない燃料で走らせるので、
  帰納は式の形についてではなく燃料についてで、宣言単位の主張と同時に立つ（`Decl.levels`）
- 宣言単位の正しさ — 証明済み（`Decl.lean`）。公開関数 67 本すべてについて、`evalCall` が値を返すなら
  生成モジュールの同名関数の呼び出しが同じ値を返す。入口の `checkTy` が
  `Value.hasTy` を満たす引数を必ず通すこと、`__pN` の上に積まれた検査つき `const` が `bindParams` と同じ
  束縛を返すこと、`compileBody` が開いた `const` 文の列が `evalExpr` と対応することを繋いだもの。主張は
  「十分な燃料で」の形で、`callFunctionAt` がその燃料を取る
- 宣言単位の陰性方向 — 証明済み（`Decl.lean`）。公開関数 67 本すべてについて、生成関数の入口を通る引数は
  `eval` も通す引数の符号化である（`decl_refuses`）。裏を返せば `eval` が受け取らない呼び出しは
  `typeError` で落ちる。入口は本体を見ないので、公開でない宣言にも同じ形で立つ。主張は
  JS の値について述べる —— `encodeValue` が `Int53` と `UInt32` を同じ `.num` に潰すので、Lean の値に
  ついての素直な逆は偽になる。外れるのは関数型の引数を取る宣言（検査が出ない。それがちょうど `isPublic`
  の線）で、辞書については実行時に渡るのが `Map` であることを仮定に置く
- 本体の陰性方向 — 証明済み（`Correct.lean` / `Decl.lean`）。公開関数 67 本すべてについて、
  入口が受け取った引数で `eval` が落ちるなら、生成モジュールの同名関数が**同じコード**で落ちる
  （`fragment_traps_in`、`decl_traps`）。`Agree` が失敗どうしを `Err.code` で比べているので、主張も
  コードの一致にしてある。断片が届く落ち方はゼロ除算・`Int53` 溢れ・範囲外アクセスの 3 つで、型エラーには
  `typeSound` が届かせない。`EnvTyped` は「ctx にある名前が env にもある」を言わないので `EnvCovers` を足した。
  呼び出しが届く落ち方には、呼ばれた宣言の本体が落ちる場合も入る。
  写す相手がいない落ち方は `Correct.Mirrorable` が名指ししている 1 つだけ —— `eval` 側の燃料切れ
  （生成コード側の主張が「十分な燃料で」の形をしている）
- 網羅性 — 証明済み（`Exhaustive.lean`）。コンパイラが受け入れた `match` は走査値の型のすべての値に腕を
  持つ。Maranget の usefulness 検査を `partial` から全域（降りる深さに上限を持つ形）に書き直し、
  「useful でない行列はその型の値をすべて覆う」を示したもの。上限を使い切ったときは「useful」と答える
  ので、通す側には倒れない。これで生成した連鎖が最後の腕をテストなしで取ることが正当化され、
  `noMatchingAlternative` は写せない落ち方ではなくなった
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
| 長さの Int53 溢れ | 配列・文字列・辞書の長さは `__i53` を通す。実在の JS エンジンでは溢れないが、模型にはリストの長さに上限がなく、リファレンス意味論はそこで trap する |
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

停止性はコンパイラが担保している。宣言の本体が名指しできるのは自分より前の宣言だけなので、自己再帰も
相互再帰も書けず、走査は `map` / `filter` / `reduce` が受け持つ。`eval` の fuel は証明を閉じるための
装置であって、サブセットの意味論ではない。

差分テストの形: `leants` が `vectors.json`（`[{fn, args, expected}]`、`expected` は `eval` の結果で
trap も符号化する）を出力し、Vitest が生成された ESM を実行して突き合わせる。

出力先は実際の npm パッケージの形にする（`packages/verified-example/`）。提案書の配布ノードそのもので
あり、差分がレビューできる。
