# verified-package テンプレート

Lean で書いた業務ロジックと、それについての定理から、npm パッケージを生成するパッケージの雛形。
**出荷されるのは処理系ではなくあなたの成果物**で、このディレクトリはその出発点になる。

## 使い方

```sh
cp -R templates/verified-package my-logic && cd my-logic
lake build                          # ロジックと定理を検査する
lake exe lean2js MyLogic --out dist  # 検査して、dist/ に npm パッケージを書き出す
```

`lean2js` は `Lean2Js` が持つ実行ファイルで、`lake exe` が依存から解決する。渡すのはモジュール名で、
そのモジュールの `manifest` と、同じ名前空間にある `Program` と公開定理を実行時に読んで書き出す
（`--manifest` で別の定数を指せる）。

`lake exe lean2js` は書き出す前に照合する。公開関数ごとに生成した差分ベクタの全件について、Lean の
リファレンス意味論と生成した JavaScript の模型が一致しなければ、パッケージは書き出されずに落ちる。そのうえで、組み立てたパッケージを Node で読み込み、同じ全件を
本物の JavaScript で呼ぶ。ここで食い違っても書き出されない。だから `node` が PATH に要る。

名前空間の公開定理も、どれも書き出す前に証明を見る。`propext` / `Classical.choice` / `Quot.sound` 以外の
公理に依っていれば落ちる —— `sorry` で塞いだ証明は `lake build` を警告だけで通るので、止まるのはここ。

## 中身

| ファイル | 役割 |
| --- | --- |
| `lakefile.toml` | `Lean2Js` への依存。`rev` を固定すると処理系の版が固定される |
| `MyLogic.lean` | 業務ロジック（普通の Lean の `def`）、定理、`lean2js` が読む manifest |
| [`SYNTAX.md`](SYNTAX.md) | `@[ship]` を付けた `def` の中に書ける Lean の全部 |

`dist/` に出るのは `index.js` / `index.js.map` / `index.d.ts` / `<パッケージ名の末尾>.lean2js` /
`proof-manifest.json` / `README.md` / `package.json`。生成される `README.md` は
公開 API と定理と公理の一覧で、npm のページに出るのはこれ。

## 書き換えるところ

- `MyLogic.lean` の `def`（`invoiceFor` と、それが呼ぶ `invoiceLines` / `discountOn` …）を自分のものに
  置き換える。出荷するものには `@[ship]` を付ける —— 印を付けた時点で宣言が読み出され、
  `ship_package` がそれを集めて呼び出しが前へ進む順に並べ、宣言ごとの証明書を書く。
  この行より下に書いた `def` は集まらず、`lean2js` が落ちる。
  書ける Lean は [`SYNTAX.md`](SYNTAX.md) —— **受け付けるのは Lean の狭い部分集合**で、
  読めない形は `def` を名指しして断られる
- `ship_package` はそのまま残す。`lean2js` がベクタを走らせる前に断る条件（燃料の上限、
  コンパイルできない宣言）を `lake build` の側で先に落とすのも、この行
- 定理を書く。**名前空間の公開定理はすべて、成果物の定理として載る。** 文言は Lean が定理に対して
  印字するシグネチャで、docstring があれば説明として添えられる。載せたくない補題は `private` にする
- `manifest` の `package` / `version` が、生成される `package.json` にそのまま入る
- `compiler` / `lean` / `source` も、定理の一覧と文言も書かない —— `lean2js` が入れる。手書きだと、
  成果物が何でビルドされ何が証明されたかについて、事実と違うことを言えてしまう
- 公開するなら `isPrivate := false` を書く。既定は `true` で、生成される `package.json` に
  `"private": true` が入る（事故で publish されない側に倒してある）。`license` /
  `repository` も `manifest` に置くと `package.json` に入る

## 定理の書き方

**自分の `def` についての普通の Lean の等式を書く。** 解釈器も AST も出てこない。`@[ship]` が宣言を
読み出したときに `ship_package` が書く証明書が「パッケージが export する関数はこの `def` を計算する」
と言うので、`def` についての等式がそのまま出荷物についての主張になる。

`MyLogic.lean` の 4 本が、よく要る形をひととおり踏んでいる —— 引数が具体値で計算だけで閉じるもの
（`enterprise_includes_its_seats`、`decide`）、`match` の腕が定数のもの（`no_discount_takes_nothing`、
`rfl`）、`def` を展開して閉じるもの（`free_plan_is_never_charged`、`simp [seatCharge, seatPrice]`）、
入口の `if` を仮説で倒すもの（`negative_seats_are_refused`、`simp [invoiceFor, hneg]`）。

生成した JavaScript がリファレンス意味論と同じ値を返すこと・同じコードで落ちること・入口で弾くことは、
`Lean2Js` の側で一度だけ、すべてのプログラムについて証明してある。ここで書く必要は無い。
