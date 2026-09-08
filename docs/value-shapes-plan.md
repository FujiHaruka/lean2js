# 値を組み立てる形

`docs/body-refusal-plan.md` までで、断片についての主張は三方向そろった —— 値が返るとき、入口が弾く
とき、本体が落ちるとき。動かしていないのは**分母のほう**である。断片は `Core.Expr` の 35 形のうち
6 形しかなく、公開関数 67 本のうち 23 本にしか届かない。この文書は断片を 27 形へ広げ、届く関数を
43 本にする。

## 文脈

`decl_correct` と `decl_traps` は `InFragment` を仮定に取るだけで、証明の中身は `fragment_correct_in`
と `fragment_traps_in` にある。したがって**断片を広げると陽性方向と陰性方向が同時に広がる**。
`decl_refuses` は本体を見ないので今も公開関数 67 本すべてに立っていて、ここは動かない。

いま断片に入っているのはリテラル・変数・条件式・`let` 束縛・単項演算・二項演算の 6 形。残り 29 形は
`Agree` の全件検査（24431 件）が受けている。

## 引く線

入れるのは、**部分式を評価して値を組み立てるだけの形**。外れるのは 8 形で、どれも「どの式をどの環境で
何回評価するか」が実行時に決まるものである。

| 外れる形 | 理由 |
| --- | --- |
| `call` / `fnRef` | 評価するのは部分式ではなく他の宣言の本体。覆うにはプログラム全体の整合性を帰納法に載せる必要があり、`Sound.lean` が `call` を外している理由と同じ |
| `matchE` | どの腕を、どの名前を束縛した環境で評価するかが、走査対象の値で決まる |
| `mapE` / `filterE` / `findE` / `quantE` / `reduceE` | 本体を要素ごとに違う環境で評価する。fuel の帰納の内側にリストの帰納が入る |

`letE` が入るのは、束縛する名前も評価する式も**評価を始める前に決まっている**からで、既存の証明が
すでにその形を歩いている。

この線で断片に入るのは 27 形。届く公開関数は 23 本から **43 本**になる（`Program.publicDecls` のうち
`inFragmentB` が真になる本数を数えたもの）。届かないまま残る 24 本は、`call` か上の 6 形のどれかを
使っている。

## Approach

**型の健全性を先に広げ、そのあとで断片を広げる。** Step 5 → Step 6 のときと同じ理由による。生成
コードは値の形で分岐する —— `.member` は `.obj` にしか効かず、`__at` は `.arr` にしか、`__trim` は
`.str` にしか効かない。「コンパイラが型 `T` と判断した」から「値がその形をしている」を出す道具が
`typeSound` で、これが無いと各形の証明が 1 歩目で止まる。先に断片を広げると、形ごとに毎回 `Sound` へ
戻ることになる。

**刻める単位は形の族。** `TypeChecked` も `InFragment` も帰納型で、`typeSound` /
`fragment_correct_in` / `fragment_traps_in` はその上の 1 本の帰納なので、構成子を足したコミットは
その場合分けも同じコミットで埋めないと通らない。族の中で `Sound` と `Correct` を別コミットにはできる。

**陽性と陰性は同じコミットで足す。** `InFragment` に構成子を 1 つ足すと `fragment_correct_in` と
`fragment_traps_in` の両方に穴が開く。片方だけ埋めることはできない。

**両側のモデルはすでに同じ形で書いてある。** `Eval.trimChars` と `Js.Runtime.strTrim`、
`Eval.dictWith` と `Js.Runtime.mapSet`、`Eval.sliceArr` と `Js.Runtime.arrSlice` —— 対応する定義は
意図的に同じ構造をしている。差が出るのは JS 側だけが持つ `safeMin` / `safeMax` の検査で、そこは
`Int53` の値域から潰す。

## 段取り

### Step 1. 型の健全性を広げる（`Sound.lean`）

`TypeChecked` に 21 形を足し、`typeSound` の場合分けを埋める。族の順序は、必要な補題が少ないほうから。

| 族 | 形 |
| --- | --- |
| 1a 包む形 | `noneE` / `someE` / `okE` / `errorE` |
| 1b 文字列 | `strUn` / `strBin` / `substring` |
| 1c 配列 | `arrayLit` / `index` / `length` / `arraySlice` / `arrayReverse` |
| 1d 構造体 | `ctor` / `proj` |
| 1e 辞書 | `dictLit` / `dictGet` / `dictHas` / `dictSet` / `dictKeys` / `dictValues` / `dictDelete` |

`ctor` と `proj` が後ろにあるのは、宣言の型からフィールドの型を引く経路（`Ty.subst` /
`TypeDef.ctorsAt`）を通るのがこの 2 つだけだからで、`length` が配列の族にあるのは配列・文字列・辞書の
3 つを 1 形で受けているからである。

### Step 2. 断片を同じ順で広げる（`Correct.lean`）

族ごとに `InFragment` の構成子・`inFragmentB` の場合・`InFragment.typeChecked` の場合・
`fragment_correct_in` と `fragment_traps_in` の場合を足す。伝播の補題（`eventually_*` /
`eventuallyErr_*`）は形ごとに要るぶんだけ先に置く。

`inFragmentB` は `ctor` / `arrayLit` / `dictLit` で引数のリストを歩くので、リストの補助関数を通す
構造的再帰にする。`Ty.subst` と `bindVars` を書き直したときと同じ形で、利用者が `rfl` で仮定を
落とせることが要件（`docs/next-milestone-plan.md` Step 2）。

### Step 3. 例題への具体化と数字

`addMoney` は構造体・射影・`Result` の構成をまとめて踏むので、断片が業務ロジックに届いたことを示すのは
これが一番短い。`add` と同じ 3 本（値・落ちる側・弾く側）のうち、弾く側はすでに全公開関数に立っている
ので足すのは 2 本。manifest の `Claim` と `Axioms.lean` の行、README の「保証の組み立て」と
`docs/mvp-plan.md` の Phase 2 到達点を同じコミットで直す。

## 落ち方が 1 つ増える

いまの断片が届く落ち方はゼロ除算と `Int53` 溢れの 2 つだが、広げた断片は `indexOutOfBounds` にも届く
—— 配列の添字・`slice`・`substring` が範囲外で落ちる。`typeError` はどの形からも届かないままで、
そこを閉じるのが Step 1 の仕事である。`noMatchingAlternative` は `matchE` の落ち方なので、断片の外に
残る。

したがって README の「証明（関数・落ちる側）」は、本数だけでなく**落ち方の棚卸しも**同じコミットで
直る。

## 覆っていないもの

| 外れるもの | 理由 |
| --- | --- |
| 残り 8 形と、それを使う公開関数 24 本 | 上の「引く線」のとおり。`Agree` の全件検査が受け持つ |
| `outOfFuel` | 参照側だけの概念で、JS 側に写す相手がいない |
| 生成物の中身 | 断片を広げても生成コードは 1 バイトも動かない。動くのは manifest だけ |

## 守ること

- **保証を弱めて緑にしない。** 実行時検査が落ちたときに、検査対象のベクタを減らさない
- **`sorry` で塞がない**（塞げば `Axioms.lean` が落ちる）
- **manifest に定理を足したら `Axioms.lean` に行を足す**
- **数字を動かしたら引用元を同じコミットで直す。** 断片が覆う形の数（6 → 27）と関数の本数
  （23 → 43、残り 44 → 24）は `README.md` と `docs/mvp-plan.md` が引用している
- **プッシュ前にゲートを全部ローカルで通す。** 一部だけ回した結果を判断に使わない
