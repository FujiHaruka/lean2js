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
| `Array` 操作（`map` / `filter` / `reduce` / `slice` / `reverse` / `++`）と `match`（入れ子・ワイルドカード・リテラル） | metaprogramming |
| 算術（`+` / `-` / `*` / `/` / `%` / `abs` / `min` / `max`、溢れとゼロ除算は trap） | Float / IEEE 754 |
| 純粋関数 | 再帰 / 非停止 / DOM access |
| `String` 操作（`trim` / 大文字小文字 / `startsWith` / `endsWith` / `includes` / `split` / `substring`） | 正規表現 |
| `Dict`（文字列キー、`Map` として出力。`get` / `set` / `has` / `delete` / `keys` / `values`） | 素のオブジェクトを辞書として使うこと |

## ロードマップ

| Phase | 内容 | 状態 |
| --- | --- | --- |
| 1. COMPILE | 最小言語の定義と ESM 出力（基本型・ADT・純粋関数、`index.js` / `index.d.ts`、Node での差分テスト） | 完了 |
| 2. VERIFY | 変換の保証（small-step semantics、compiler correctness、proof manifest） | 一部 |
| 3. SHIP | npm 開発体験（source maps、tree shaking、CI / package publishing） | 完了 |

詳細は [提案書](docs/proposal.html) と [実装プラン](docs/mvp-plan.md) を参照。

## 保証の組み立て

```
Lean のリファレンス意味論  ──証明（断片）──  生成した JS
        │                                        │
        │                       └──実行時検査（成果物の全ベクタ）──┘
        │
        └──実行時検査──  small-step 意味論

生成した JS の模型  ──Node 上の差分テスト──  本物の JavaScript
```

- **証明**: リテラル・変数・条件式について、`eval` が値を返すなら生成コードも同じ値を返す
- **境界の検査**: 公開関数は本体に入る前に、引数を宣言した型と構造的に照合する。型を破った呼び出しは
  `eval` と同じ `typeError` で落ちるので、一致の主張に「宣言した型を満たす引数について」という但し書きが要らない
- **停止性**: 関数は自分より前に宣言された関数しか呼べないので、自己再帰も相互再帰もコンパイルが通らない。
  非停止は `eval` の fuel が尽きるのを待つのではなく構文として排除され、走査は `map` / `filter` / `reduce`
  が受け持つ
- **実行時検査**: 出荷する成果物の全ベクタ（現在 22343 件）について、`eval` と JS の模型、および
  `eval` と small-step が一致することを `leants` が書き出す前に確かめる
- **差分テスト**: 生成した ESM を Node で実行し、`eval` の答えと突き合わせる。JS の模型が仮定している
  振る舞い（`-0`、`Math.trunc` の精度、UTF-16 と コードポイントの違い）はここで押さえる

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
docs/                       提案書と実装プラン
```

## 開発

必要なもの: Node.js 24 / pnpm 10 / elan（Lean 4.33.1）

```sh
pnpm install
pnpm lean:build     # Lean ライブラリと定理をビルドする
pnpm lean:emit      # 検証つき npm パッケージを生成する
pnpm typecheck
pnpm test
pnpm package:check  # publint / attw
```
