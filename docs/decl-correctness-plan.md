# 宣言単位の正しさ

`Correct.fragment_correct` は**式**についての定理で、公開関数についてではない。この文書は、その式の
証明を**公開関数 1 本の主張**に変える橋（`Lean2Js/Decl.lean`）がどう組まれているかを書く
（決定 2026-09-08, ユーザーの指示）。

## 立っている主張

```
decl_correct :
  compileProgram p = .ok m → p.find? fn = some d → InFragment d.body →
  evalCall p fn args = .ok v →
  ∃ g, ∀ g' ≥ g, Js.callFunctionAt m g' fn (args.map encodeValue) = .ok (encodeValue v)
```

対象は `Js.callFunctionAt` —— `Agree` が全件検査で叩いている `callFunction` から燃料を引数に出した
ものである。覆えた関数については「24431 件試した」が「どんな引数でも」に置き換わる。出荷している例題
では公開関数 67 本のうち 23 本が覆えていて、その本数は `inFragmentB` で機械的に数える。

主張は `d.isPublic` を要求しない。関数型の引数を取る宣言でも、入口が検査を省いて生の引数をそのまま
渡すだけなので、同じ形で通る。

## 覆っていないもの

| 外れるもの | 理由 |
| --- | --- |
| 残り 29 形（`call` / `match` / 配列走査 / 辞書） | 分母は `InFragment` のまま。動かしたのは「式から関数へ」の一段だけ |
| 陰性方向（`eval` が `typeError` を返すとき JS も throw する） | 型を破った引数の一致は `Agree` が受け持つ（ベクタ生成器は型エラーのベクタを作る） |

## Approach

**`fragment_correct` と `callFunctionAt` の間には橋が 4 本ある。** 新しい証明技法は要らず、既にある
定理を関数の入口と出口に繋ぐ。

1. **入口の検査が両側で一致する（陽性方向）** —— `Value.hasTy` が真なら、生成コードが呼ぶ `checkTy` も
   その記述子で真になる（`checkTy_encodeValue`）。値の構造で再帰し、型と記述子は引数として持って回る。
   型で再帰すると入れ子の型引数で止まらない
2. **入口が作る環境が対応する** —— `evalCall` の `bindParams` と、生の引数の上に検査つき `const` を積んだ
   JsEnv が、本体から見て同じ束縛を返す（`evalStmts_paramChecks`、`jsEnvAgrees_checkedBindings`）
3. **本体が文に開かれる** —— `compileBody` は先頭の `let` を `const` 文へ開くので、`evalStmts` と
   `evalExpr` の対応を `let` の列に沿った帰納で示し、末尾で `fragment_correct` に落ちる
   （`compileBody_correct`）
4. **燃料の形をそろえる** —— `fragment_correct` の結論は `Eventually`（∃ 燃料）だが `callFunction` は
   10000 固定。`callFunctionAt` を切り出して主張を `Eventually` の形に合わせる

## 展開できること

**`partial` な定義は等式を 1 本も持たない。** 証明は `tyDesc p b .int53` すら開けないので、橋が渡る
経路にある定義はすべて全域である必要がある。`compileBody`・`tyDesc`・`wfTy` がそれで、`wfTy` は
`compileExpr` の `let` の分岐から呼ばれるため橋 3 に効く。

**`mapM` も展開できない。** `Ty.subst` が `args.map` を避けてリスト補助関数を通しているのと同じ理由で、
`tyDesc` の構成子・フィールド、`compileDecl` の入口検査、`compileProgram` の宣言列も、すべて明示の
再帰に置き換えてある。

**`tyDesc` だけは構造再帰にならない。** `.named` を展開すると、置換後のフィールド型は元の型より大きく
なりうる。`Paginated (Paginated Int53)` のように、型引数から同じ宣言を二度展開する経路もある。取って
いる道は燃料で、`tyDescBudget p ty = (ty.size + 1) * (p.types.length + 1)` が上から抑える。展開の深さは
「型式の入れ子の深さ × 宣言の本数」で抑えられる（宣言をまたぐ連鎖は `validateType` が非巡回にしている）。
出荷している例題で実際に要る燃料は最大 1、渡している予算は最小 12。

**予算を使い切った場合はコンパイルエラーで、間違った成果物にはならない。** ここが「保証を弱めない」の線。

`sizeOf` は使えない。`Ty` の導出インスタンスが `noncomputable` で、この数はコンパイル中に計算する。
数えるのは `Ty.size`。

## 環境の重なり

`fragment_correct` は結論の JS 環境を `encodeEnv env` に固定していたが、**公開関数の本体はその環境で
走らない**。入口の検査は生の引数 `__p0`, `__p1`, … を残したまま、その上に宣言名の束縛を積む。そこで
`JsEnvAgrees env jenv` —— 「参照側が束縛している名前はすべて、生成側も同じ値の符号化に束縛している。
生成側はもっと束縛していてよい」—— を取る `fragment_correct_in` を立て、`fragment_correct` はその
`jenv := encodeEnv env` での系にしてある。manifest と `Axioms.lean` が引く形は変わっていない。

層を分けているのは 3 つの事実である。

- **宣言名は `__` で始まらない**（`validateIdent`）。だから宣言名を積んでも `__pN` の探索は素通りする
- **`__pN` は N について単射**。`Nat.toList_repr` と `Nat.ofDigitChars_toDigits` から `Nat.repr` の
  単射性が出る。`bindAll` が積んだ生の束縛を N 番目まで読み飛ばすのにこれが要る
- **引数名が相異なる**（`validateDistinct`）。入口は引数を最後のものから順に積むので `bindParams` と
  逆順になる。同じ名前が二度出なければ、どちらから探しても同じ束縛に当たる

## プログラムの差

`compileProgram` は宣言 *i* を `p.decls.take i` に対してコンパイルするが、`evalCall` は `p` 全体で走る。
断片の本体が読むのは型宣言だけで、`decls` の前半を取っても `types` は動かないので、`compileExpr` /
`compileBody` / `tyDesc` / `paramChecks` は両者で一致する（`*_types_irrel`）。

## 使い方

利用者が自分の宣言でこれを使うために、`InFragment` の決定手続き `inFragmentB` と
`InFragment.of_inFragmentB` を添えてある。仮定は `rfl` 一行で落ちる。`Example.lean` には `add`（単一の
二項演算）、`discounted`（先頭の `let`）、`rebindTwice`（影に落ちる `let`）への具体化が置いてある。

## 守ること

- **保証を弱めて緑にしない。** 実行時検査が落ちたときに、検査対象のベクタを減らさない
- **`sorry` で塞がない**（塞げば `Axioms.lean` が落ちる）
- **manifest に定理を足したら `Axioms.lean` に行を足す**
- **数字を動かしたら引用元を同じコミットで直す。** 関数単位で覆えた本数は `README.md` と
  `docs/mvp-plan.md` が引用する
