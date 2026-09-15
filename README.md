# lean.ts

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
| 2. VERIFY | 変換の保証（small-step semantics、compiler correctness、proof manifest） | 一部 |
| 3. SHIP | npm 開発体験（source maps、tree shaking、CI）と、処理系そのものの配布（利用者のパッケージの雛形） | 完了 |

詳細は [提案書](docs/proposal.html) と [実装プラン](docs/mvp-plan.md) を参照。

## 保証の組み立て

```
Lean のリファレンス意味論  ──証明（式のすべての形・公開関数 67 本すべて）──  生成した JS
        │                                        │
        │                       └──実行時検査（成果物の全ベクタ）──┘
        │
        └──実行時検査──  small-step 意味論

生成した JS  ──証明（往復）──  出荷する index.js のテキスト

生成した JS の模型  ──実行時検査（Node 上・成果物の全ベクタ）──  本物の JavaScript
```

- **証明（式）**: `Core.Expr` の **35 形すべて**について、`eval` が値を返すなら生成コードも同じ値を
  返す。リテラル・変数・条件式・`let` 束縛・単項演算・**二項演算のすべて**（算術・比較・等値・論理・
  連結の 16 演算子）、**部分式を評価して値を組み立てるだけの形**すべて —— `Option` と `Result`
  の構成、構造体の構成と射影、配列リテラルと添字・`slice` / `reverse`・長さ、辞書リテラルと
  `get` / `has` / `set` / `keys` / `values` / `delete`、文字列の `trim` / 大文字小文字 /
  `startsWith` / `endsWith` / `includes` / `split` / `substring` ——、**束縛を変えて部分式を
  評価する形** —— `match` と配列走査 5 つ（`map` / `filter` / `find` / `all`・`any` / `reduce`）——、
  そして**他の宣言の本体へ行く形** —— 呼び出しと関数参照。呼び出しは呼ばれた宣言の本体を 1 段少ない
  燃料で走らせるので、証明は式の形についてではなく**燃料についての帰納**で、宣言単位の主張と同時に立つ
- **証明（関数・返す側）**: **公開関数 67 本すべて**について、主張が呼び出しの単位で立つ。
  **どんな引数でも**、`eval` が値を返すなら生成モジュールの同名関数が同じ値を返す。
  入口の型検査、`__pN` から宣言名への引き渡し、先頭の `let` が `const` 文に開かれるところ、そして
  本体が他の宣言を呼ぶところまで含む
- **証明（関数・落ちる側）**: 同じ **67 本**について、`eval` が値を返さずに落ちるなら、生成モジュールの
  同名関数は**同じコード**で落ちる。届く落ち方はゼロ除算・`Int53` 溢れ・範囲外アクセス
  （添字・`slice` / `substring`）で、型エラーには届かないことを型の健全性が示す。**除外は無い** ——
  燃料切れは `eval` の答えに現れない（下記「燃料」）
- **網羅性**: コンパイラが受け入れた `match` は、走査値の型が取りうる**すべての値**について腕を持つ
  （Maranget の usefulness 検査の健全性）。生成した条件の連鎖が最後の腕をテストなしで取るのはこれが
  理由で、`eval` の側も「どの腕にも当たらない」に落ちない。検査は全域関数として書かれていて、降りる
  深さの上限を使い切ったときは「網羅でない」と答える —— 通してしまう側には倒れない
- **型の健全性**: コンパイラが型 `T` と判断した式を `eval` が評価して値が返るなら、その値は `T` を
  満たす。**`Core.Expr` の 35 形すべて**について証明済みで、生成コードが被演算子の型で分岐する箇所を
  閉じているのがこれ。呼び出しまで届くのは、コンパイラが受け取ったプログラムの**すべての宣言**について
  「本体は宣言した返り値型でコンパイルされる」を成果物から取り出せるから
- **証明（関数・弾く側）**: 公開関数は本体に入る前に、引数を宣言した型と構造的に照合する。**公開関数
  67 本すべて**について、この検査を通る引数は `eval` も受け取る引数の符号化であることが証明されている。
  裏を返せば、`eval` が受け取らない呼び出しは —— 本数違いも、型を破ったものも —— 生成コードが `typeError`
  を投げる。一致の主張に「宣言した型を満たす引数について」という但し書きが要らないのはこれによる。落ちること自体は両側で
  揃うが、コードまで揃うとは言っていない —— 本数違いのとき `eval` が返すのは `arity` である。辞書に
  ついては、実行時に渡るのが `Map` である（同じキーを二度持てない）ことを仮定に置く
- **停止性**: 関数は自分より前に宣言された関数しか呼べないので、自己再帰も相互再帰もコンパイルが通らない。
  関数を引数に渡すときも、渡せるのは受け取る宣言より前に宣言された関数だけなので、引数を経由した
  呼び出しも前へしか進まない。非停止は `eval` の fuel が尽きるのを待つのではなく構文として排除され、
  走査は `map` / `filter` / `reduce` が受け持つ
- **燃料**: `eval` を全域にしている燃料は、出荷するプログラムでは尽きない。必要な燃料は**式の入れ子の
  深さと呼び出しの段数**だけで決まる —— 走査はリストの残りを同じ燃料で評価するので、配列が長くても
  増えない —— し、呼び出しは前へしか進まないので段数は宣言の本数で上から押さえられる。`Cost.cost` が
  その上界を構文から計算し、`leants` は書き出す前に、出荷時の 10000 に収まることを**プログラムごとに
  1 回**確かめる（この例題は 482）
- **実行時検査**: 成果物ごとに生成する全ベクタ（この例題で 24466 件）について、`eval` と JS の模型、
  および `eval` と small-step が一致することを `leants` が書き出す前に確かめる。証明が届いたいまも残るのは、
  **模型の燃料**が出荷時の 10000 で足りることを見る役と、small-step との一致を見る役
- **テキスト**: コンパイルが通ったなら、書き出した `index.js` は**そのまま同じ AST に読み戻る**
  （`parseModule_render_of_compileProgram`）。但し書きは無い —— 読み手が木に要求すること
  （名前が識別子であること、呼び先が読み手の振り分ける 10 語でないこと、doc が `/** */` を閉じないこと）
  は、コンパイルが成功したことから取り出せるので、利用者の側には現れない。読み手が受けるのは
  **この処理系が書く部分集合**だけで、JavaScript の字句・構文全体ではない。`leants` は書き出す前に、
  出荷するテキストそのものでも同じことを確かめる
- **実行時ヘルパ**: 生成コードが呼ぶ `__` 接頭辞の JavaScript は手で書いてあるが、**印字器が
  書き出すその 49 本のソースが何を計算するかは証明済み**。JS の模型がヘルパについて仮定している表は
  35 行あり、その**全行**が、書き出されるソースの計算と一致する（`helpers_ship_as_modelled`）。
  呼び出し側に残る仮定は 3 つ —— 商が Int53 に収まること（型が与える）、辞書のキーが相異なること
  （`Map` が保証する）、そして `===` による構造比較が模型の構造等価と割れない形であること
  （比べる 2 つのオブジェクトのフィールドが同じ並びで、辞書のキーが相異なる）
- **`.d.ts`**: 入口検査を通った引数は `.d.ts` が公開している型を満たす値であり
  （`entry_check_fits_dts`）、逆に `.d.ts` の型を満たす引数は、数値が `Int53` / `UInt32` の範囲に
  収まっているかぎり入口検査を通る（`dts_fits_entry_check`）。**両方向とも manifest に載っている。**
  `.d.ts` は利用者が実際に読む唯一の型なので、これが「読んだ型と受け取る値がずれていない」の側。
  範囲の但し書きは下記。返る側は `encoded_values_fit_dts` —— `eval` が宣言した型を与える値は、
  符号化すると `.d.ts` の型を満たす
- **Node での検査**: `leants` は書き出す前に、組み立てたパッケージを一時ディレクトリで Node に読み込ませ、
  全ベクタを本物の JavaScript で呼んで `eval` の答えと突き合わせる。1 件でも食い違えば出力先には何も
  書かない。JS の模型が仮定している振る舞い（`-0`、`Math.trunc` の精度、UTF-16 と コードポイントの違い）
  はここで押さえる
- **公理**: manifest に載る定理が `propext` / `Classical.choice` / `Quot.sound` 以外の公理に依らない
  ことを、`leants` が書き出す前に確かめる（`collectAxioms`）。`sorry` で塞いだ証明は `lake build` を
  警告だけで通ってしまうので、止めているのはこちら —— 許すのは 3 つだけなので、別の公理を持ち込む証明も
  同じく書き出しに届かない。使った公理は `proof-manifest.json` の `axioms` に載る。処理系の側の
  7 本の定理は `LeanTs/Axioms.lean` が `#print axioms` で固定している

関数単位の主張は「模型の燃料が十分にあれば」の形をしている。これは**生成コードの模型**を全域にする
ための装置で、本物の JavaScript には無い。出荷時に使う 10000 で足りていることは、上の実行時検査が
全ベクタについて確かめている。`eval` の側の燃料は主張から消えた（上記「燃料」）。

**`.d.ts` の型が通れば入口検査も通る。但し書きは 1 点だけ。** `Int53` と `UInt32` はどちらも `number`
に写るので、範囲を外れた数も TS では通り、渡せば `typeError` になる。それ以外は縛らない ——
オブジェクトのフィールドは名前で読むので並びは自由で、宣言に無いキーが載っていても通り、本体に
届く前に落ちる。

## 生成物

```
packages/verified-example/
  index.js                  ESM。実行時ヘルパは __ 接頭辞に閉じてある
  index.js.map              .leants への source map（関数単位）
  index.d.ts                .d.ts。ADT は判別可能なユニオンに、型パラメータはジェネリクスになる
  verified-example.leants   Core を書き出したソース。名前はパッケージ名の末尾を取る
  proof-manifest.json       定理・証明が依る公理・コンパイラ版・公開 API
  README.md                 公開 API・定理・公理の一覧
  package.json              exports / sideEffects / engines
```

## リポジトリ構成

```
lakefile.toml               LeanTs パッケージ。ソースは srcDir = "lean"
lean/LeanTs/Core.lean       サブセットの構文
lean/LeanTs/Syntax.lean     Core 項へ展開される表層構文
lean/LeanTs/Eval.lean       fuel 付き big-step のリファレンス意味論
lean/LeanTs/Step.lean       継続を明示した small-step 意味論
lean/LeanTs/Compile.lean    Core → JS（型検査と生成を一本のパスで）
lean/LeanTs/JsSem.lean      生成した JS の意味論の模型
lean/LeanTs/Correct.lean    compiler correctness（断片）
lean/LeanTs/Agree.lean      成果物に対する実行時の一致検査
lean/LeanTs/NodeCheck.lean  書き出す前に成果物を Node で全ベクタに当てるスクリプト
lean/LeanTs/Example.lean    出荷するプログラムと、それについての定理
lean/LeanTs.lean            import LeanTs が引くもの（利用者のビルドはここまで）
lean/LeanTs/Checks.lean     証明と #guard と公理固定。CI が建てる、利用者は引かない
lean/Main.lean              leants 実行ファイル: 指定されたモジュールの manifest を読んで書き出す
packages/lean-ts/           Node 上のテスト —— 生成物の入口検査・source map・tree shaking と、検査スクリプト
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
lake exe leants MyLogic --out dist  # 検査して、dist/ に npm パッケージを書き出す
```

`leants` は `LeanTs` が持つ実行ファイルで、`lake exe` が依存から解決する。利用者は実行ファイルを
書かない —— モジュール名を渡すと、その `manifest` を実行時に読んで書き出す。

利用者が建てるのは `import LeanTs` が引く 23 モジュール・56 MB だけで、コンパイラについての証明
93 MB は入らない —— それは CI が建てるもので、利用者が再検査しても何も足されない。

`leants` は書き出す前に、生成した全ベクタを Node で成果物に当てる（上記「Node での検査」）ので、
`node` が PATH に要る。ベクタは出力先に残らず、検査を通ったパッケージだけが書き出される。

雛形の中身と書き換えどころは [`templates/verified-package/README.md`](templates/verified-package/README.md)、
`decl%` / `type%` に書ける構文は [`templates/verified-package/SYNTAX.md`](templates/verified-package/SYNTAX.md) にある。
雛形の `#eval program.check` は、`leants` が書き出す前に断る条件のうちベクタを要らない分
（再帰、燃料の上限、コンパイルできない宣言）を、利用者の `lake build` の側で落とす。
