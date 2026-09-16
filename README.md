# lean2js

Lean 4 で証明した業務ロジックを、普通の npm パッケージとして JavaScript / TypeScript の世界へ届けるための処理系。

形式検証を導入するために、フロントエンドの技術スタックを入れ替える必要はない。追加するのは、ひとつのパッケージだけ。

```
Restricted Lean  →  verified compiler  →  npm package  →  React / Next / Node
implementation       semantics              index.js         ordinary import
+ theorem            preservation           index.d.ts       ordinary values
                                            proof-manifest.json
```

売るのは「仕様を証明した」ことではなく、「証明した実装が動いている」こと。

書くのは Lean のファイルの中の、こういう構文。

```lean
def Money : TypeDef := type% Money := Money(amount : Int53, currency : String)

def addMoney : Decl := decl%
  addMoney(a : Money, b : Money) : Result<Money, String> :=
    if a.currency != b.currency then error<Money>("currency mismatch")
    else ok<String>(Money::Money(a.amount + b.amount, a.currency))
```

## 設計方針

- **JS の意味論に合わせる** — Int53、UInt32、BigInt など、数値表現を曖昧にしない
- **境界を型で固定する** — 公開 API は JS 互換の値に限定し、ESM と `.d.ts` を同時生成する
- **生成器より検査器を信頼する** — translation validation により、生成結果の証明書を小さな checker で検査する
- **証明を成果物に残す** — 定理・ビルド・コンパイラ版を proof manifest として追跡可能にする

### 対象サブセット

Lean 全体ではなく、JS との対応が明快な領域に絞ることで、コンパイラの正しさと小さな TCB を現実的に狙う。
**`decl%` / `type%` の中に書くのは Lean の式ではない** —— Lean のパーサだけ借りた別の文法で、Lean の
`Array` / `String` の API もラムダも再帰もそこには無い。全部の形は
[`templates/verified-package/SYNTAX.md`](templates/verified-package/SYNTAX.md) にある。

| 含める | 外す |
| --- | --- |
| `Bool` / `Int53` / `UInt32` / `String` / `BigInt` | `IO` / ambient state |
| `type%` の直和・直積（`Money(amount : Int53, ...)`、`guest \| member \| admin`）、型パラメータ、`Option<T>` / `Result<A, E>` | `unsafe` / arbitrary FFI / pointer |
| 配列の走査（`xs.map(fun x => ...)` / `filter` / `reduce` / `find` / `all` / `any` / `slice` / `reverse` / `++`）と `match`（入れ子・ワイルドカード・リテラル） | metaprogramming |
| 算術（`+` / `-` / `*` / `/` / `%` / `abs()` / `min()` / `max()`、溢れとゼロ除算は trap） | Float / IEEE 754 |
| 純粋関数（`decl% f(x : T) : U := ...`） | 再帰 / 非停止 / DOM access |
| 宣言済み関数を `@name` で渡す引数（内部の宣言どうしに限る） | 関数を値にすること（走査の外のラムダ・クロージャ・公開境界の関数型） |
| 文字列（`trim()` / `toUpper()` / `toLower()` / `startsWith()` / `endsWith()` / `includes()` / `split()` / `substring()`） | 正規表現 |
| `Dict<V>`（文字列キー、`Map` として出力。`get` / `set` / `has` / `delete` / `keys` / `values`） | 素のオブジェクトを辞書として使うこと |

## ロードマップ

| Phase | 内容 | 状態 |
| --- | --- | --- |
| 1. COMPILE | 最小言語の定義と ESM 出力（基本型・ADT・純粋関数、`index.js` / `index.d.ts`、Node での差分テスト） | 完了 |
| 2. VERIFY | 変換の保証（small-step semantics、compiler correctness、proof manifest） | 完了 |
| 3. SHIP | npm 開発体験（source maps、tree shaking、CI）と、処理系そのものの配布（利用者のパッケージの雛形） | 完了 |

詳細は [提案書](docs/proposal.html) と [実装プラン](docs/mvp-plan.md) を参照。Lean のモジュール・定義・定理の
リファレンスは [API ドキュメント](https://fujiharuka.github.io/lean2js/) にある。

## 保証の組み立て

```
Lean のリファレンス意味論  ──証明（式のすべての形・公開関数 67 本すべて）──  生成した JS
        │                                        │
        │                       └──実行時検査（成果物の全ベクタ）──┘
        │
        └──証明（十分なステップを与えたすべての呼び出し）──  small-step 意味論

生成した JS  ──証明（往復）──  出荷する index.js のテキスト

生成した JS の模型  ──実行時検査（Node 上・成果物の全ベクタ）──  本物の JavaScript
```

- **証明が届く範囲** — `Core.Expr` の **35 形すべて**と、公開関数 **67 本すべて**。`eval` が値を返すなら
  生成した同名関数が同じ値を返し（[`decl_correct`]）、`eval` が落ちるなら**同じコード**で落ち
  （[`decl_traps`]）、`eval` が受け取らない引数は本体に入る前に `typeError` になる（[`decl_refuses`]）。
  一致の主張に「宣言した型を満たす引数について」という但し書きは無く、除外も無い ——
  `eval` 側の燃料切れは出荷するプログラムでは起きない（[`cost`] が必要な燃料の上界を構文から計算し、
  [`progOk`] が呼び出しが前へしか進まないことを見る。出荷時の上限 10000 に対してこの例題は 482）
- **その土台** — 生成コードが被演算子の型で分岐できるのは型の健全性（[`typeSound`]）、`match` の最後の腕を
  テストなしで取れるのは網羅性（[`firstMatch_isSome`]、Maranget の usefulness 検査の健全性）による。
  評価順序と短絡評価を継続として明示した small-step 意味論も、公開関数へのすべての呼び出しで `eval` と
  同じ答えに着く（[`stepCall_agrees`]）
- **出荷物そのもの** — 書き出した `index.js` は**そのまま同じ AST に読み戻る**
  （[`parseModule_render_of_compileProgram`]、但し書き無し）。生成コードが呼ぶ `__` 接頭辞の実行時
  ヘルパ 49 本は手で書いてあるが、模型がヘルパについて仮定している表 35 行の**全行**が、印字器の
  書き出すソースの計算と一致する（[`helpers_ship_as_modelled`]）
- **`.d.ts`** — 入口検査を通る引数は `.d.ts` の型を満たし（[`entry_check_fits_dts`]）、`.d.ts` の型を
  満たす引数は入口検査を通る（[`dts_fits_entry_check`]）。返る側も同じ（[`encoded_values_fit_dts`]）。
  `.d.ts` は利用者が実際に読む唯一の型なので、**両方向とも manifest に載っている**
- **証明の外** — 成果物ごとに生成する全ベクタ（この例題で 24466 件）を、`lean2js` が書き出す前に
  2 通りで確かめる。`eval` と JS の模型の一致（[`checkAgreement`]）と、組み立てたパッケージを一時
  ディレクトリで Node に読み込ませた本物の JavaScript との一致。1 件でも食い違えば出力先には何も書かない
- **一覧が証明とずれないこと** — manifest に載る定理は手で書かない。`lean2js` が同じ名前空間の公開定理を
  すべて集め、Lean が印字するシグネチャを文言にする。どの定理も `propext` / `Classical.choice` /
  `Quot.sound` 以外の公理に依らないことも書き出す前に確かめる —— `sorry` で塞いだ証明は `lake build` を
  警告だけで通ってしまうので、止めているのはこちら

**`.d.ts` の型が通れば入口検査も通る。但し書きは 1 点だけ。** `Int53` と `UInt32` はどちらも `number`
に写るので、範囲を外れた数も TS では通り、渡せば `typeError` になる。それ以外は縛らない ——
オブジェクトのフィールドは名前で読むので並びは自由で、宣言に無いキーが載っていても通り、本体に
届く前に落ちる。

定理の主張・仮定・証明の構成は [Lean のリファレンス](https://fujiharuka.github.io/lean2js/)にある。

[`decl_correct`]: https://fujiharuka.github.io/lean2js/Lean2Js/Decl.html#Lean2Js.Decl.decl_correct
[`decl_traps`]: https://fujiharuka.github.io/lean2js/Lean2Js/Decl.html#Lean2Js.Decl.decl_traps
[`decl_refuses`]: https://fujiharuka.github.io/lean2js/Lean2Js/Decl.html#Lean2Js.Decl.decl_refuses
[`cost`]: https://fujiharuka.github.io/lean2js/Lean2Js/Cost.html#Lean2Js.Cost.cost
[`progOk`]: https://fujiharuka.github.io/lean2js/Lean2Js/Cost.html#Lean2Js.Cost.progOk
[`typeSound`]: https://fujiharuka.github.io/lean2js/Lean2Js/Sound.html#Lean2Js.typeSound
[`firstMatch_isSome`]: https://fujiharuka.github.io/lean2js/Lean2Js/Exhaustive.html#Lean2Js.Exhaustive.firstMatch_isSome
[`stepCall_agrees`]: https://fujiharuka.github.io/lean2js/Lean2Js/StepAgree.html#Lean2Js.StepAgree.stepCall_agrees
[`parseModule_render_of_compileProgram`]: https://fujiharuka.github.io/lean2js/Lean2Js/Renderable.html#Lean2Js.Compile.parseModule_render_of_compileProgram
[`helpers_ship_as_modelled`]: https://fujiharuka.github.io/lean2js/Lean2Js/Example.html#Lean2Js.Example.helpers_ship_as_modelled
[`entry_check_fits_dts`]: https://fujiharuka.github.io/lean2js/Lean2Js/Example.html#Lean2Js.Example.entry_check_fits_dts
[`dts_fits_entry_check`]: https://fujiharuka.github.io/lean2js/Lean2Js/Example.html#Lean2Js.Example.dts_fits_entry_check
[`encoded_values_fit_dts`]: https://fujiharuka.github.io/lean2js/Lean2Js/Example.html#Lean2Js.Example.encoded_values_fit_dts
[`checkAgreement`]: https://fujiharuka.github.io/lean2js/Lean2Js/Agree.html#Lean2Js.checkAgreement

## 生成物

```
packages/verified-example/
  index.js                  ESM。実行時ヘルパは __ 接頭辞に閉じてある
  index.js.map              .lean2js への source map（関数単位）
  index.d.ts                .d.ts。ADT は判別可能なユニオンに、型パラメータはジェネリクスになる
  verified-example.lean2js   Core を書き出したソース。名前はパッケージ名の末尾を取る
  proof-manifest.json       定理・証明が依る公理・コンパイラ版・公開 API
  README.md                 公開 API・定理・公理の一覧
  package.json              exports / sideEffects / engines
```

## リポジトリ構成

```
lakefile.toml               Lean2Js パッケージ
Lean2Js/Core.lean           サブセットの構文
Lean2Js/Syntax.lean         Core 項へ展開される表層構文
Lean2Js/Eval.lean           fuel 付き big-step のリファレンス意味論
Lean2Js/Step.lean           継続を明示した small-step 意味論
Lean2Js/StepAgree.lean      small-step 意味論と eval の一致の証明
Lean2Js/Compile.lean        Core → JS（型検査と生成を一本のパスで）
Lean2Js/JsSem.lean          生成した JS の意味論の模型
Lean2Js/Correct.lean        compiler correctness（断片）
Lean2Js/Agree.lean          成果物に対する実行時の一致検査
Lean2Js/NodeCheck.lean      書き出す前に成果物を Node で全ベクタに当てるスクリプト
Lean2Js/Example.lean        出荷するプログラムと、それについての定理
Lean2Js.lean                import Lean2Js が引くもの（利用者のビルドはここまで）
Lean2Js/Checks.lean         証明と #guard と公理固定。CI が建てる、利用者は引かない
Main.lean                   lean2js 実行ファイル: 指定されたモジュールの manifest を読んで書き出す
packages/lean2js/           Node 上のテスト —— 生成物の入口検査・source map・tree shaking と、検査スクリプト
packages/verified-example/  生成された npm パッケージ
templates/verified-package/ 利用者が自分のロジックを書きはじめるためのパッケージの雛形
scripts/                    雛形が空のディレクトリから通ることを確かめる検査
docs/                       提案書と実装プラン
```

## 開発

必要なもの: Node.js 24 / pnpm 10 / elan（Lean 4.33.1）

```sh
pnpm install
pnpm lean:build      # Lean ライブラリと定理をビルドする
pnpm lean:emit       # 検証つき npm パッケージを生成する
pnpm typecheck
pnpm test
pnpm package:check   # publint / attw
pnpm template:check  # 雛形が空のディレクトリから通ることを確かめる
```

### 自分のロジックを書く

出荷するのは処理系であって、`packages/verified-example` ではない。利用者は自分の Lean パッケージで
このライブラリに依存し、業務ロジックと定理を書き、自分の npm パッケージを生成する。

```sh
cp -R templates/verified-package my-logic && cd my-logic
lake build                          # ロジックと定理を検査する
lake exe lean2js MyLogic --out dist  # 検査して、dist/ に npm パッケージを書き出す
```

`lean2js` は `Lean2Js` が持つ実行ファイルで、`lake exe` が依存から解決する。利用者は実行ファイルを
書かない —— モジュール名を渡すと、その `manifest` を実行時に読んで書き出す。

利用者が建てるのは `import Lean2Js` が引く 23 モジュール・57 MB だけで、コンパイラについての証明
98 MB は入らない —— それは CI が建てるもので、利用者が再検査しても何も足されない。

`lean2js` は書き出す前に、生成した全ベクタを Node で成果物に当てる（上記「Node での検査」）ので、
`node` が PATH に要る。ベクタは出力先に残らず、検査を通ったパッケージだけが書き出される。

雛形の中身と書き換えどころは [`templates/verified-package/README.md`](templates/verified-package/README.md)、
`decl%` / `type%` に書ける構文は [`templates/verified-package/SYNTAX.md`](templates/verified-package/SYNTAX.md) にある。
雛形の `#eval program.check` は、`lean2js` が書き出す前に断る条件のうちベクタを要らない分
（再帰、燃料の上限、コンパイルできない宣言）を、利用者の `lake build` の側で落とす。

## ライセンス

Apache License 2.0（[`LICENSE`](LICENSE)）。生成された npm パッケージは利用者のロジックと定理から
できているので、そのライセンスは利用者が決める。
