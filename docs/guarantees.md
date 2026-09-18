# 保証の組み立て

`lean2js` が出荷するパッケージについて、証明が届く範囲と、その外を受け持つ実行時検査の全体。
README の What is guaranteed はこのページの要約で、定理の主張・仮定・証明の構成は
[Lean のリファレンス](https://fujiharuka.github.io/lean2js/)にある。

```
利用者の Lean の def  ──証明書（宣言ごと 1 本・出荷する 67 本すべて）──  リファレンス意味論
        │
        └──利用者の定理は、この def についての普通の Lean の等式

Lean のリファレンス意味論  ──証明（式のすべての形・公開関数 67 本すべて）──  生成した JS
        │                                        │
        │                       └──実行時検査（成果物の全ベクタ）──┘
        │
        └──証明（十分なステップを与えたすべての呼び出し）──  small-step 意味論

生成した JS  ──証明（往復）──  出荷する index.js のテキスト

生成した JS の模型  ──実行時検査（Node 上・成果物の全ベクタ）──  本物の JavaScript
```

- **利用者の関数と出荷する宣言** — 宣言は利用者の `def` から**歩いて読み出され**、同じ歩きが
  「この宣言はこの `def` を計算する」の証明項を組み立てる（`Denotes`）。変換器は信頼していない ——
  証明が通らなければ宣言は存在しない。`lean2js` は**証明書の無い宣言を出荷しない**ので、
  AST を手で渡して迂回する道は無い。だから利用者の定理は `seatCharge .free seats = 0` のような
  自分の関数についての等式でよく、それがそのまま出荷物についての主張になる
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
  すべて集め、Lean が印字するシグネチャを文言にする。宣言ごとの証明書は 1 本ずつは載らない ——
  出荷する宣言と 1 対 1 で、1 本でも欠ければ書き出さないので、載せるのは「あること」であって
  67 通りの言い換えではない。どの定理も `propext` / `Classical.choice` /
  `Quot.sound` 以外の公理に依らないことも書き出す前に確かめる —— `sorry` で塞いだ証明は `lake build` を
  警告だけで通ってしまうので、止めているのはこちら

**`.d.ts` の型が通れば入口検査も通る。但し書きは 1 点だけ。** `Int53` と `UInt32` はどちらも `number`
に写るので、範囲を外れた数も TS では通り、渡せば `typeError` になる。それ以外は縛らない ——
オブジェクトのフィールドは名前で読むので並びは自由で、宣言に無いキーが載っていても通り、本体に
届く前に落ちる。

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
