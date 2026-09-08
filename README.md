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

| 含める | 外す |
| --- | --- |
| `Bool` / `Int53` / `UInt32` / `String` / `BigInt` | `IO` / ambient state |
| `structure` / `inductive` / 型パラメータ / `Option` / `Result` | `unsafe` / arbitrary FFI / pointer |
| `Array` 操作（`map` / `filter` / `reduce` / `find` / `all` / `any` / `slice` / `reverse` / `++`）と `match`（入れ子・ワイルドカード・リテラル） | metaprogramming |
| 算術（`+` / `-` / `*` / `/` / `%` / `abs` / `min` / `max`、溢れとゼロ除算は trap） | Float / IEEE 754 |
| 純粋関数 | 再帰 / 非停止 / DOM access |
| 宣言済み関数を名前で渡す引数（内部の宣言どうしに限る） | 関数を値にすること（ラムダ・クロージャ・公開境界の関数型） |
| `String` 操作（`trim` / 大文字小文字 / `startsWith` / `endsWith` / `includes` / `split` / `substring`） | 正規表現 |
| `Dict`（文字列キー、`Map` として出力。`get` / `set` / `has` / `delete` / `keys` / `values`） | 素のオブジェクトを辞書として使うこと |

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

生成した JS の模型  ──Node 上の差分テスト──  本物の JavaScript
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
  同名関数は**同じコード**で落ちる。断片が届く落ち方はゼロ除算・`Int53` 溢れ・範囲外アクセス
  （添字・`slice` / `substring`）の 3 つで、型エラーには届かないことを型の健全性が示す。除くのは 2 つ。
  `eval` 側の燃料切れ —— 燃料は `eval` を全域にするための装置で、生成コードについての主張は
  「十分な燃料で」の形をしているから、写す相手がいない。そして `match` がどの腕にも当たらないとき
  （`noMatchingAlternative`）—— 網羅性はコンパイル時に検査済みなので、生成した条件の連鎖は最後の腕を
  テストなしで取る。ここを写すには網羅性検査そのものの正しさが要り、その検査は `partial` である
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
- **実行時検査**: 出荷する成果物の全ベクタ（現在 24431 件）について、`eval` と JS の模型、および
  `eval` と small-step が一致することを `leants` が書き出す前に確かめる。証明が届いたいまも残るのは、
  証明が「十分な燃料で」と言うところを**出荷時の 10000 で**確かめる役と、small-step との一致を見る役
- **差分テスト**: 生成した ESM を Node で実行し、`eval` の答えと突き合わせる。JS の模型が仮定している
  振る舞い（`-0`、`Math.trunc` の精度、UTF-16 と コードポイントの違い）はここで押さえる

関数単位の主張は「模型の燃料が十分にあれば」の形をしている。燃料は `eval` を全域にするための装置で、
本物の JavaScript には無い。出荷時に使う 10000 で足りていることは、上の実行時検査が全ベクタについて
確かめている。

## 生成物

```
packages/verified-example/
  index.js              ESM。実行時ヘルパは __ 接頭辞に閉じてある
  index.js.map          example.leants への source map（関数単位）
  index.d.ts            .d.ts。ADT は判別可能なユニオンに、型パラメータはジェネリクスになる
  example.leants        Core を書き出したソース
  proof-manifest.json   定理・コンパイラ版・公開 API
  package.json          exports / sideEffects / engines
  vectors.json          差分テストの入力と期待値
```

## リポジトリ構成

```
lean/LeanTs/Core.lean       サブセットの構文
lean/LeanTs/Syntax.lean     Core 項へ展開される表層構文
lean/LeanTs/Eval.lean       fuel 付き big-step のリファレンス意味論
lean/LeanTs/Step.lean       継続を明示した small-step 意味論
lean/LeanTs/Compile.lean    Core → JS（型検査と生成を一本のパスで）
lean/LeanTs/JsSem.lean      生成した JS の意味論の模型
lean/LeanTs/Correct.lean    compiler correctness（断片）
lean/LeanTs/Agree.lean      成果物に対する実行時の一致検査
lean/LeanTs/Example.lean    出荷するプログラムと、それについての定理
lean/Main.lean              leants 実行ファイル
packages/lean-ts/           差分テスト・tree shaking・source map の検証
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
lake build           # ロジックと定理を検査する
lake exe emit dist   # dist/ に npm パッケージを書き出す
```

雛形の中身と書き換えどころは [`templates/verified-package/README.md`](templates/verified-package/README.md) にある。
