Lean 4 で証明した業務ロジックを、普通の npm パッケージとして JavaScript / TypeScript へ届けるための処理系。
このサイトは `Lean2Js` のモジュールと、そこに書かれた定理・定義のリファレンスで、ソースは
[GitHub のリポジトリ](https://github.com/FujiHaruka/lean2js)にある。

読みはじめる場所:

- **`Lean2Js.Core`** — JS へ運ぶ Lean のサブセットの構文
- **`Lean2Js.Reify`** — 利用者の `def` を歩いて、Core 項と「この AST はこの関数を表す」の証明項を同時に組み立てる。`Lean2Js.Denotes` が形ごとの補題
- **`Lean2Js.Eval`** — サブセットのリファレンス意味論。すべての保証はこことの一致として述べられる
- **`Lean2Js.Compile`** — Core から JS への変換。型検査と生成を一本のパスで行う
- **`Lean2Js.Correct`** / **`Lean2Js.Sound`** / **`Lean2Js.Decl`** — コンパイラ正当性・型の健全性・公開関数単位の主張
- **`Lean2Js.Example`** — 出荷するプログラムと、それについての定理

証明が届く範囲と、その外を受け持つ実行時検査・Node 上の差分テストの組み立ては
[保証の組み立て](https://github.com/FujiHaruka/lean2js/blob/main/docs/guarantees.md)にある。
