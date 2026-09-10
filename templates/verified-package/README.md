# verified-package テンプレート

Lean で書いた業務ロジックと、それについての定理から、npm パッケージを生成するパッケージの雛形。
**出荷されるのは処理系ではなくあなたの成果物**で、このディレクトリはその出発点になる。

## 使い方

```sh
cp -R templates/verified-package my-logic && cd my-logic
lake build                          # ロジックと定理を検査する
lake exe leants MyLogic --out dist  # dist/ に npm パッケージを書き出す
```

`leants` は `LeanTs` が持つ実行ファイルで、`lake exe` が依存から解決する。渡すのはモジュール名で、
そのモジュールの `manifest` を実行時に読んで書き出す（`--manifest` で別の定数を指せる）。

`lake exe leants` は書き出す前に照合する。公開関数ごとに生成した差分ベクタの全件について、Lean の
リファレンス意味論・生成した JavaScript の模型・small-step 意味論の 3 つが一致しなければ、
パッケージは書き出されずに落ちる。

`claims` に載せた定理の証明も書き出す前に見る。`propext` / `Classical.choice` / `Quot.sound` 以外の
公理に依っていれば落ちる —— `sorry` で塞いだ証明は `lake build` を警告だけで通るので、止まるのはここ。

## 中身

| ファイル | 役割 |
| --- | --- |
| `lakefile.toml` | `LeanTs` への依存。`rev` を固定すると処理系の版が固定される |
| `MyLogic.lean` | 業務ロジック（`decl%` の表層構文）、定理、`leants` が読む manifest |

`dist/` に出るのは `index.js` / `index.js.map` / `index.d.ts` / `<パッケージ名の末尾>.leants` /
`proof-manifest.json` / `README.md` / `package.json` / `vectors.json`。生成される `README.md` は
公開 API と定理と公理の一覧で、npm のページに出るのはこれ。

## 書き換えるところ

- `MyLogic.lean` の `orderTotal` を自分の宣言に置き換え、`program` の `decls` に並べる。
  **宣言は自分より前に宣言された関数しか呼べない**ので、依存の順に並べる
- 定理を書き、`manifest` の `claims` に `proof` ごと載せる。`claims` は証明項を要求するので、
  定理を消すと `lake build` が落ちる
- `manifest` の `package` / `version` が、生成される `package.json` にそのまま入る
- `compiler` / `lean` / `source` は書かない —— `leants` が入れる。手書きだと、成果物が何で
  ビルドされたかについて事実と違うことを言えてしまう
- 公開するなら `isPrivate := false` を書く。既定は `true` で、生成される `package.json` に
  `"private": true` が入る（事故で publish されない側に倒してある）。`license` /
  `repository` も `manifest` に置くと `package.json` に入る

## 定理の書き方

`evalCall` について書く。`evalCall_eq` で公開関数の入口を 1 度で越え、そのあとは
`evalExpr_<形>` の 1 段展開補題で本体を開いていく。`MyLogic.lean` の
`nothing_charged_below_one` がその形をひととおり踏んでいる。

`evalExpr.eq_def` を `simp` に直接渡さないこと。右辺が `evalExpr` を含むので止まらず、再帰深度が
尽きる。
