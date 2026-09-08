# 宣言単位の正しさ 計画

`docs/next-milestone-plan.md` が式の形について証明を積んだあと、**その証明を公開関数 1 本の主張に変える**
ための計画（決定 2026-09-08, ユーザーの指示）。

## 文脈

証明が届いているのは**式の形**であって、**関数**ではない。`fragment_correct` は `compileExpr` と
`evalExpr` について述べていて、`compileDecl` も `evalCall` も `Correct.lean` / `Sound.lean` に一度も
現れない。したがって出荷している公開関数 67 本のうち、**関数単位で保証されているものは 0 本**。本体が
まるごと fragment に収まっている `add` ですら、入口の型検査と呼び出しの包みが証明の外にある。

いま関数単位を受け持っているのは `Agree` の全件検査（差分ベクタ 24431 件）だけで、それは「試した入力に
ついては合っていた」の形をしている。

## ゴール

このマイルストーンの終わりに立てる主張。

> 本体が fragment に収まる公開関数 F について、**宣言した型を満たすどんな引数でも**、`eval` が値を返す
> なら生成モジュールの `F` 呼び出しが同じ値を返す。

主張の対象は `Js.callFunction` —— `Agree` が全件検査で叩いているまさにその関数にする。そうすれば、覆えた
関数について「24431 件試した」が「どんな入力でも」に置き換わり、置き換わっていない関数との境界が一行で
言える。

## 非目標

| 外すもの | 理由 |
| --- | --- |
| `call` を fragment に入れる | 呼び出しの型は呼ばれる宣言の返り値型なので、宣言の本体が使いうる全 35 形が要る。`docs/next-milestone-plan.md` Step 6 の「35 形すべては目指さない」はそのまま |
| 残り 29 形（`match` / 配列走査 / 辞書） | 同上。**分母は動かさない**。今回動かすのは「式から関数へ」の一段だけ |
| 陰性方向（`eval` が `typeError` を返すとき JS も throw する） | ゴールの主張に要るのは陽性方向だけ。型を破った引数の一致は `Agree` が受け持っている（ベクタ生成器は型エラーのベクタを作る） |
| 関数型の引数を取る宣言 | 公開されず、ベクタも作られない。境界の話に乗らない |

## Approach

**`fragment_correct` と `callFunction` の間には橋が 4 本しかない。** 新しい証明技法は要らず、既にある
定理を関数の入口と出口に繋ぐ作業になる。順序はこの 4 本の依存から出る。

1. **入口の検査が両側で一致する（陽性方向）** —— `Value.hasTy` が真なら、生成コードが呼ぶ `checkTy` も
   その記述子で真になる。これが入口検査の代金であり、同時に `EnvTyped` を fragment 側へ手渡す
2. **入口が作る環境が対応する** —— `evalCall` の `bindParams` と、生の引数の上に検査つき `const` を積んだ
   JsEnv が、本体から見て同じ束縛を返す
3. **本体が文に開かれる** —— `compileBody` は先頭の `let` を `const` 文へ開くので、`evalStmts` と
   `evalExpr` の対応を `let` の列に沿った帰納で示し、末尾で `fragment_correct` に落ちる
4. **燃料の形をそろえる** —— `fragment_correct` の結論は `Eventually`（∃ 燃料）だが `callFunction` は
   10000 固定。`callFunctionAt` を切り出して主張を `Eventually` の形に合わせる

**その手前に、展開できるようにする作業がある。** 入口の検査の記述子を作る `tyDesc` と、本体を文へ開く
`compileBody` はどちらも `private partial`。`partial` な定義は等式を 1 本も持たないので、証明は
`tyDesc p .int53` すら開けない。前のマイルストーンが `Ty.subst` / `bindVars` で踏んだのと同じ壁で、
**`add` のような最小の宣言でも先に通る**。だから Step 1 に置く。

## Step 1. 展開できるようにする

`compileBody` と `tyDesc` から `partial` と `private` を外す。

- `compileBody` は `letE` の本体へ降りるだけなので、`termination_by e` の構造再帰で落ちる
- **`tyDesc` は素直な構造再帰にならない。** `.named` を展開すると、置換後のフィールド型は元の型より
  大きくなりうる。`Paginated (Paginated Int53)` のように、型引数から同じ宣言を二度展開する経路もあるので
  `mentions` の `seen` では測れない。取る道は**燃料**（`evalExpr` / `Js.eval` と同じ
  `termination_by (fuel, sizeOf ty)` の形）で、`compileDecl` が十分余裕のある budget を渡す。展開の深さは
  「型式の入れ子の深さ × 宣言の本数」で上から抑えられる（宣言をまたぐ連鎖は `validateType` が非巡回に
  している）ので、`(sizeOf ty + 1) * (p.types.length + 1)` のような形にする
- **budget を使い切った場合はコンパイルエラーで、間違った成果物にはならない。** ここが「保証を弱めない」
  の線

**受け入れ条件**: `git diff --exit-code -- packages/verified-example` が通る（生成物は 1 バイトも動かない）。
`pnpm template:check` も通る。

## Step 2. 入口の検査が両側で一致する

```
tyDesc p ty = .ok d → Value.hasTy p v ty = true → Js.checkTy (encodeValue v) d = true
```

`beq_encodeValue` と同じ形の帰納 —— **値の構造で再帰し、型と記述子は引数として持って回る**。型で再帰すると
入れ子の型引数で止まらない。`checkFields` / `checkList` / `checkEntries` に対応する 3 本が付く。

## Step 3. 入口が作る環境が対応する

`callFunction` は `bindAll fn.params args`（名前は `__p0`, `__p1`, …）の上で検査つき `const` を順に積む。
本体から見た環境が `encodeEnv (bindParams d.params args)` と同じ束縛を返すことを示す。

- 利用者の名前は必ず生の束縛より**前**に積まれるので、利用者名の探索が `__pN` に当たることはない。
  必要なのは `validateDistinct` から来る**引数名の相異**のほう
- ここで要る文字列の事実は 2 つ。**`rawParam` が単射**（`__p{i}`）—— `Nat.toList_repr` と
  `Nat.ofDigitChars_ten_toDigits`（どちらも core 4.33.1 にある）で `Nat.repr` の単射性が数行で出る。
  そして**利用者名は `__` で始まらない**（`validateIdent`）—— `List.isPrefixOf_iff_prefix` 経由
- **`EnvTyped p (bindParams d.params args) ctx` はここで出る。** `evalCall` が本体に入る前に全引数の
  `hasTy` を見ているので、`ctx = d.params.map (name, ty)` との噛み合いは直接
- **プログラムの差を吸収する補題が要る。** `compileProgram` は宣言 *i* を `p.decls.take i` に対して
  コンパイルするが、`evalCall` は `p` 全体で走る。`fragment_correct` は両側に同じ `p` を取るので、
  `InFragment e` なら `p'.types = p.types` のとき両者が一致することを 6 形の帰納で示す（`Value.hasTy` も
  `types` しか読まない）

## Step 4. 本体が文に開かれる

`compileBody` の先頭 `let` の列について、`evalStmts` と `evalExpr` の対応を帰納で示す。

- **1 つの `let` につき分岐が 2 つ**。`ctx` に同じ名前があれば `compileBody` は開かずに `finish` へ落ちる
  （式のまま IIFE になる）。出荷物では `rebindTwice` がこの影の経路を、`discounted` が開く経路を踏む
- `Eventually` を文の列に沿って合成する補題が 1 本要る（`const` ごとに燃料の下限が足される）

## Step 5. 燃料の形をそろえる

`Js.callFunction` から `callFunctionAt (fuel : Nat)` を切り出し、`callFunction = callFunctionAt 10000` を
`rfl` で結ぶ。`Agree` と `Emit` は 10000 のほうを呼び続けるので、模型の外側は何も動かない。

**これは保証を弱める変更ではない。** 模型の燃料は `eval` を全域にするための装置で、本物の JavaScript に
燃料はない。「十分な燃料で」は `fragment_correct` が既に取っている形であり、10000 で足りることは
`Agree` の全件検査が今までどおり受け持つ。

## Step 6. 定理を組む

```
decl_correct : compileProgram p = .ok m → p.find? fn = some d → d.isPublic →
  InFragment d.body → evalCall p fn args = .ok v →
  ∃ g, ∀ g' ≥ g, Js.callFunctionAt m g' fn (args.map encodeValue) = .ok (encodeValue v)
```

**利用者が自分の宣言でこれを使えるように、`InFragment` の決定手続きを添える。** `inFragmentB : Expr → Bool`
と `of_inFragmentB : inFragmentB e = true → InFragment e` があれば、仮定は `rfl` 一行で落ちる。手で導出を
組ませない。

**最初の具体化は `add`。** 続けて `discounted`（先頭の `let`）と `rebindTwice`（影に落ちる `let`）を
Step 4 の形の試験として通す。

## Step 7. 成果物に載せる

- **覆えた公開関数の本数を数える。** `inFragmentB` で機械的に数え、その数を README に書く。手で数えた数は
  書かない
- `Example.lean` に `add` への具体化を置き、manifest に `Claim` を 1 本足す。**足したら `Axioms.lean` に
  行も足す**
- **保証の境界が動くので**、README の「保証の組み立て」と `docs/mvp-plan.md` の Phase 2 到達点を同じ
  コミットで直す。「証明」の行に、式の形の話とは別に**関数単位の行**が立つ

## 順序と依存

```
Step 1（partial を外す）
  ↓ これが無いと Step 2 は tyDesc を 1 文字も開けない
Step 2（入口の検査） → Step 3（入口の環境）
                          ↓ EnvTyped がここで出る
                       Step 4（本体の文）→ Step 5（燃料）→ Step 6（定理）→ Step 7（成果物）
```

**リスクは Step 1 に集中している。** `tyDesc` の全域化が思ったより重い場合の逃げ道は、今回の定理を
**引数の型がスカラー（`Bool` / `Int53` / `UInt32` / `String` / `BigInt`）の宣言に限る**こと。fragment に
収まる公開関数はほとんどがスカラー引数なので、覆う本数はさほど減らない。ただし**逃げても Step 1 は
消えない** —— `tyDesc p .int53` の等式ですら `partial` のままでは出ない。

Step 3 の文字列の事実が core の補題で閉じない場合の逃げ道は、`decl_correct` を閉じた定理ではなく
**宣言ごとに具体化するタクティクの形**にすること。名前が具体的な文字列になれば不等式は `decide` で
落ちる。製品の主張と manifest の `Claim` は同じように立つ。

## 守ること

- **保証を弱めて緑にしない。** 実行時検査が落ちたときに、検査対象のベクタを減らさない
- **`sorry` で塞がない。** 塞げば `Axioms.lean` が落ちる
- **manifest に定理を足したら `Axioms.lean` に行を足す**
- **数字を動かしたら引用元を同じコミットで直す。** ベクタ件数・`exports` 件数・証明が覆う形の数・
  今回足す「関数単位で覆えた本数」は README と `docs/mvp-plan.md` が引用する
- **プッシュ前にゲートを全部ローカルで通す。** 一部だけ回した結果を判断に使わない
