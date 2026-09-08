# 値を組み立てる形

`docs/body-refusal-plan.md` までで、断片についての主張は三方向そろった —— 値が返るとき、入口が弾く
とき、本体が落ちるとき。動かしていないのは**分母のほう**だった。断片は `Core.Expr` の 35 形のうち
6 形しかなく、公開関数 67 本のうち 23 本にしか届かなかった。このマイルストーンは断片を 27 形へ広げ、
届く関数を **43 本**にした。

## 文脈

`decl_correct` と `decl_traps` は `InFragment` を仮定に取るだけで、証明の中身は `fragment_correct_in`
と `fragment_traps_in` にある。したがって**断片を広げると陽性方向と陰性方向が同時に広がる**。
`decl_refuses` は本体を見ないので今も公開関数 67 本すべてに立っていて、ここは動いていない。

## 引く線

入れたのは、**部分式を評価して値を組み立てるだけの形**。外れる 8 形は、どれも「どの式をどの環境で
何回評価するか」が実行時に決まるものである。

| 外れる形 | 理由 |
| --- | --- |
| `call` / `fnRef` | 評価するのは部分式ではなく他の宣言の本体。覆うにはプログラム全体の整合性を帰納法に載せる必要があり、`Sound.lean` が `call` を外している理由と同じ |
| `matchE` | どの腕を、どの名前を束縛した環境で評価するかが、走査対象の値で決まる |
| `mapE` / `filterE` / `findE` / `quantE` / `reduceE` | 本体を要素ごとに違う環境で評価する。fuel の帰納の内側にリストの帰納が入る |

`letE` が入るのは、束縛する名前も評価する式も**評価を始める前に決まっている**からで、既存の証明が
すでにその形を歩いていた。

**射影には但し書きが 1 つ付いた。** `InFragment.proj` は `field ≠ "tag"` を要求する。生成した構造体は
判別子を `tag` というキーに置くので、`tag` という名前のフィールドを読むと判別子のほうに当たる。
`validateType` はそういう型の宣言をそもそも拒否しているが、`fragment_correct_in` は式ひとつについての
主張でプログラム全体の検査を仮定に持たないため、断片の側が同じことを言う必要がある。

## Approach

**型の健全性を先に広げ、そのあとで断片を広げた。** Step 5 → Step 6 のときと同じ理由による。生成
コードは値の形で分岐する —— `.member` は `.obj` にしか効かず、`__at` は `.arr` にしか、`__trim` は
`.str` にしか効かない。「コンパイラが型 `T` と判断した」から「値がその形をしている」を出す道具が
`typeSound` で、これが無いと各形の証明が 1 歩目で止まる。

**刻める単位は形の族。** `TypeChecked` も `InFragment` も帰納型で、`typeSound` /
`fragment_correct_in` / `fragment_traps_in` はその上の 1 本の帰納なので、構成子を足したコミットは
その場合分けも同じコミットで埋めないと通らない。族の中で `Sound` と `Correct` は別コミットにできた。

**陽性と陰性は同じコミットで足した。** `InFragment` に構成子を 1 つ足すと `fragment_correct_in` と
`fragment_traps_in` の両方に穴が開く。片方だけ埋めることはできない。

**両側のモデルはすでに同じ形で書いてあった。** `Eval.trimChars` と `Js.Runtime.strTrim`、
`Eval.dictWith` と `Js.Runtime.mapSet`、`Eval.sliceArr` と `Js.Runtime.arrSlice` —— 対応する定義は
意図的に同じ構造をしている。差が出るのは JS 側だけが持つ `safeMin` / `safeMax` の検査で、そこは
`Int53` の値域から潰した。

## 何が動いたか

### 型の健全性（`Sound.lean`）

`TypeChecked` に 21 形が入り、`typeSound` は 27 形を覆う。要った道具は 3 つ。

- `Value.hasElemTy` を「要素ごと」に読み替える `hasElemTy_iff`。`drop` / `take` / `reverse` /
  `getElem?` はどれも「渡された要素しか残さない」ので、これがあれば `List` の所属補題から出る
- `keysDistinct` と `List.Nodup` の橋。辞書の `set` と `delete` が `Map` の性質を保つことは、
  ここから `List.Nodup.sublist` と `List.nodup_append` で出る
- 引数のリストを `typeSound` の帰納法の仮定と一緒に歩く 3 本（`hasElemTy_of_args` /
  `hasFieldTys_of_args` / `hasEntryTys_of_values`）

### 断片（`Correct.lean`）

族ごとに `InFragment` の構成子・`inFragmentB` の場合・`InFragment.typeChecked` の場合・
`fragment_correct_in` と `fragment_traps_in` の場合を足した。`inFragmentB` は `ctor` / `arrayLit` /
`dictLit` で引数のリストを歩くので、リストの補助関数を通す相互再帰にしてある。

`Decl.lean` は 4 本の帰納が `letE` だけを特別扱いして残りを一様に処理していたので、形ごとの行を
**catch-all 1 本に畳んだ**（`by constructor <;> assumption` で導出を組み直す）。以降、断片に形を足しても
この 4 本は触らずに済む。触るのは `compileExpr_types_irrel` だけで、そちらは形ごとに 1 ケース要る。

### 長さが両側で食い違っていた

`.length` を断片に入れようとして、**リファレンス意味論と JS の模型が食い違う**ことがわかった。`eval` は
`mkInt53` を通すので `Int53` に収まらない長さで trap するが、模型の `.length` は数を返すだけだった。実在の
JS エンジンでは配列も文字列も `Map` もそこまで長くならないが、模型のリストには上限がない。

**直したのはコンパイラのほう。** 配列・文字列・辞書の長さを `__i53` で包み、生成コードが同じところで
trap するようにした。実在の入力では発火しない検査だが、それが模型と `eval` を一致させる。判断は
`docs/mvp-plan.md` の「JS 意味論との対応」に入っている。

### 落ち方が 2 つ増えた

いままで断片が届く落ち方はゼロ除算と `Int53` 溢れだけだったが、広げた断片は **`indexOutOfBounds`**
（配列の添字・`slice`・`substring`）にも、**長さの `Int53` 溢れ**にも届く。`typeError` はどの形からも
届かないままで、そこを閉じているのが型の健全性である。`noMatchingAlternative` は `matchE` の落ち方なので
断片の外に残る。

### 数字

| | 前 | 後 |
| --- | --- | --- |
| 断片が覆う `Core.Expr` の形 | 6 / 35 | 27 / 35 |
| 陽性・陰性が届く公開関数 | 23 / 67 | 43 / 67 |
| manifest の `Claim` | 7 | 9 |

生成物で動いたのは `.length` を `__i53` で包んだ 8 行と、manifest に増えた 2 本の定理だけ。ベクタは
24431 件のまま。

## 覆っていないもの

| 外れるもの | 理由 |
| --- | --- |
| 残り 8 形と、それを使う公開関数 24 本 | 上の「引く線」のとおり。`Agree` の全件検査が受け持つ |
| `outOfFuel` | 参照側だけの概念で、JS 側に写す相手がいない |
| `tag` という名前のフィールドの射影 | 判別子のキーと衝突する。`validateType` が型の宣言時に拒否している |

## 守ること

- **保証を弱めて緑にしない。** 実行時検査が落ちたときに、検査対象のベクタを減らさない
- **`sorry` で塞がない**（塞げば `Axioms.lean` が落ちる）
- **manifest に定理を足したら `Axioms.lean` に行を足す**
- **数字を動かしたら引用元を同じコミットで直す。** 断片が覆う形の数と関数の本数は `README.md` と
  `docs/mvp-plan.md` が引用している
- **プッシュ前にゲートを全部ローカルで通す。** 一部だけ回した結果を判断に使わない
