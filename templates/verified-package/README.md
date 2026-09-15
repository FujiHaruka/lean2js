# verified-package テンプレート

Lean で書いた業務ロジックと、それについての定理から、npm パッケージを生成するパッケージの雛形。
**出荷されるのは処理系ではなくあなたの成果物**で、このディレクトリはその出発点になる。

## 使い方

```sh
cp -R templates/verified-package my-logic && cd my-logic
lake build                          # ロジックと定理を検査する
lake exe leants MyLogic --out dist  # 検査して、dist/ に npm パッケージを書き出す
```

`leants` は `LeanTs` が持つ実行ファイルで、`lake exe` が依存から解決する。渡すのはモジュール名で、
そのモジュールの `manifest` と、同じ名前空間にある `Program` と公開定理を実行時に読んで書き出す
（`--manifest` で別の定数を指せる）。

`lake exe leants` は書き出す前に照合する。公開関数ごとに生成した差分ベクタの全件について、Lean の
リファレンス意味論と生成した JavaScript の模型が一致しなければ、パッケージは書き出されずに落ちる。そのうえで、組み立てたパッケージを Node で読み込み、同じ全件を
本物の JavaScript で呼ぶ。ここで食い違っても書き出されない。だから `node` が PATH に要る。

名前空間の公開定理も、どれも書き出す前に証明を見る。`propext` / `Classical.choice` / `Quot.sound` 以外の
公理に依っていれば落ちる —— `sorry` で塞いだ証明は `lake build` を警告だけで通るので、止まるのはここ。

## 中身

| ファイル | 役割 |
| --- | --- |
| `lakefile.toml` | `LeanTs` への依存。`rev` を固定すると処理系の版が固定される |
| `MyLogic.lean` | 業務ロジック（`decl%` の表層構文）、定理、`leants` が読む manifest |
| [`SYNTAX.md`](SYNTAX.md) | `decl%` / `type%` の中に書ける構文の全部 |

`dist/` に出るのは `index.js` / `index.js.map` / `index.d.ts` / `<パッケージ名の末尾>.leants` /
`proof-manifest.json` / `README.md` / `package.json`。生成される `README.md` は
公開 API と定理と公理の一覧で、npm のページに出るのはこれ。

## 書き換えるところ

- `MyLogic.lean` の `orderTotal` を自分の宣言に置き換える。`program%` が、同じ名前空間でそれより上に
  書いた `Decl` と `TypeDef` を集め、呼び出しが前へ進む順に並べるので、書く順序は問わない。
  **呼び出しは循環できない。** `program%` より下に書いた宣言は集まらず、`leants` が落ちる。
  書ける構文は [`SYNTAX.md`](SYNTAX.md) —— `decl%` の中は Lean の式ではない
- `#eval program.check` はそのまま残す。`leants` がベクタを走らせる前に断る条件
  （燃料の上限、コンパイルできない宣言）を `lake build` の側で先に落とす
- 定理を書く。**名前空間の公開定理はすべて、成果物の定理として載る。** 文言は Lean が定理に対して
  印字するシグネチャで、docstring があれば説明として添えられる。載せたくない補題は `private` にする
- `manifest` の `package` / `version` が、生成される `package.json` にそのまま入る
- `compiler` / `lean` / `source` も、定理の一覧と文言も書かない —— `leants` が入れる。手書きだと、
  成果物が何でビルドされ何が証明されたかについて、事実と違うことを言えてしまう
- 公開するなら `isPrivate := false` を書く。既定は `true` で、生成される `package.json` に
  `"private": true` が入る（事故で publish されない側に倒してある）。`license` /
  `repository` も `manifest` に置くと `package.json` に入る

## 定理の書き方

`evalCall` について書く。`evalCall_eq` で公開関数の入口を 1 度で越え、そのあとは
`evalExpr_<形>` の 1 段展開補題で本体を開いていく。`MyLogic.lean` の
`nothing_charged_below_one` がその形をひととおり踏んでいる。

`evalExpr.eq_def` を `simp` に直接渡さないこと。右辺が `evalExpr` を含むので止まらず、再帰深度が
尽きる。
