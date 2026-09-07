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
| `structure` / `inductive` / `Option` / `Result` | `unsafe` / arbitrary FFI / pointer |
| `Array` / `match` | metaprogramming |
| 純粋関数 / 構造的再帰 | 非停止 / DOM access |

## ロードマップ

| Phase | 内容 |
| --- | --- |
| 1. COMPILE | 最小言語の定義と ESM 出力（基本型・ADT・純粋関数、`index.js` / `index.d.ts`、Node での差分テスト） |
| 2. VERIFY | 変換の保証（small-step semantics、compiler correctness、proof manifest） |
| 3. SHIP | npm 開発体験（source maps、tree shaking、CI / package publishing） |

詳細は [提案書](docs/proposal.html) を参照。

## リポジトリ構成

```
lean/          Lean 4 ライブラリ（サブセットの構文・意味論・コンパイラ・証明）
packages/      TypeScript 側のツール群（CLI、差分テスト、パッケージ生成）
docs/          提案書
```

## 開発

必要なもの: Node.js 24 / pnpm 10 / elan（Lean 4.33.1）

```sh
pnpm install
pnpm typecheck
pnpm test
pnpm lean:build
```
