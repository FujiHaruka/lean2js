# 束縛を変えて評価する形

`docs/value-shapes-plan.md` が断片を「部分式を評価して値を組み立てるだけの形」まで広げたあと、
残っているのは**評価する環境が実行時に決まる形**である。このマイルストーンはそのうち
`match` と配列走査 5 形を断片へ入れ、`call` / `fnRef` だけを外に残す。

## 文脈

断片は `Core.Expr` の 35 形のうち 27 形、公開関数 67 本のうち 43 本に届いている。外れている 24 本を
外れる理由で数えると、こうなる。

| 外れる理由 | 本数 |
| --- | --- |
| `match` だけ | 8 |
| 走査（`map` / `filter` / `find` / `all` / `any` / `reduce`）だけ | 7 |
| `call` / `fnRef` だけ | 4 |
| `match` または走査に加えて `call` | 5 |

`match` と走査を入れると **58 本**になり、残る 9 本はすべて `call` を通る。だから `call` は
このマイルストーンの外に置く —— 呼び出しを覆うには宣言の本体が使いうるすべての形をプログラム全体の
整合性ごと帰納法に載せる必要があり、`Sound.lean` が `call` を外しているのと同じ理由による。
`call` を除いた断片の上限が 33 形で、そこがこのマイルストーンの到達点になる。

## ゴール

- 断片が `Core.Expr` の **33 形**を覆う（`call` / `fnRef` だけが外）
- `decl_correct` / `decl_traps` が公開関数 **58 本**に届く
- manifest に、`match` の関数と走査の関数についての主張が載る
- 生成物は 1 バイトも動かない。コンパイラにも意味論にも触らない

## Approach

**形の族ごとに刻み、Sound を先に置く。** `TypeChecked` も `InFragment` も帰納型で、`typeSound` /
`fragment_correct_in` / `fragment_traps_in` はその上の 1 本の帰納だから、構成子を足したコミットは
その場合分けも同じコミットで埋めないと通らない。族の中で `Sound` と `Correct` は別コミットにできる。
生成コードが値の形で分岐する以上（`.map` は `.arr` にしか効かず、腕のテストは `.obj` の `tag` を読む）、
先に要るのは `Sound` のほう。

**陽性と陰性は同じコミット。** `InFragment` に構成子を 1 つ足すと `fragment_correct_in` と
`fragment_traps_in` の両方に穴が開く。片方だけ埋めることはできない。

**走査を先に、`match` を後に。** 走査は `eval` と JS の模型が**同じ形の補助関数**として書いてある
（`evalMapItems` と `evalMapJs`、`evalReduceItems` と `evalReduceJs`）。要るのは fuel の帰納の内側に
置くリストの帰納だけで、帰納法の仮定が環境と fuel について全称なので、要素ごとに違う環境へそのまま
効く。`match` はそうではない —— 生成コードはパターンをテストと束縛に落とした条件の連鎖で、
`matchPat` との対応はパターンについての別の帰納になる。

**`match` の難所は、一致しなかった腕を落とす側。** 腕を飛ばすには「テストの連鎖が trap ではなく
`false` に評価される」ことを言う必要がある。内側のフィールドを読むテストへ進むのは `tag` を確かめた
後だけで、それを守っているのは `&&` の短絡と、`patParts` がテストを外側から並べる順序である。

## Step 1. 走査 5 形の型の健全性

`TypeChecked` に `mapE` / `filterE` / `findE` / `quantE` / `reduceE` を足し、`typeSound` の場合を埋める。
要素の型は走査対象の `hasTy` から `hasElemTy_iff` で取り出し、`EnvTyped.cons` で本体の環境に積む。

## Step 2. 走査 5 形を断片へ

`InFragment` / `inFragmentB` / `InFragment.typeChecked` / `fragment_correct_in` / `fragment_traps_in`、
そして `Decl.lean` の `compileExpr_types_irrel`。走査ごとに、リストを歩く補題を陽性・陰性の 2 本ずつ置く。

`find` / `all` / `any` は短絡するので、答えが決まった後ろの要素は**どちらの側でも評価されない**。
補題はその形（走査の途中で止まった結果）をそのまま持つ。

## Step 3. `match` の型の健全性

`TypeChecked` に `matchE` を足す。腕の本体を型検査した文脈は `patParts` が返した束縛で伸びているので、
`matchPat` が返した環境がその文脈と噛み合っていること（`EnvTyped`）を、パターンについての帰納で示す。

## Step 4. `match` を断片へ

`patParts` の返すテストと束縛を、`matchPat` の結果と突き合わせる補題を置く。一致する腕については
テストがすべて `true` に評価され、`paths` から読んだ値が `matchPat` の束縛と一致すること。一致しない
腕については、テストの連鎖が `false` に評価されること。そのうえで `chain` を腕のリストについての帰納で
歩く。

## Step 5. 出荷する主張

新しく届いた関数のうち 2 本を manifest の `Claim` にする（`match` から 1 本、走査から 1 本）。
定理を足したら `Axioms.lean` に行を足す。

## 守ること

- **保証を弱めて緑にしない。** 実行時検査が落ちたときに、検査対象のベクタを減らさない
- **`sorry` で塞がない**（塞げば `Axioms.lean` が落ちる）
- **manifest に定理を足したら `Axioms.lean` に行を足す**
- **数字を動かしたら引用元を同じコミットで直す。** 断片が覆う形の数と関数の本数は `README.md` と
  `docs/mvp-plan.md` が引用している
- **プッシュ前にゲートを全部ローカルで通す。** 一部だけ回した結果を判断に使わない
