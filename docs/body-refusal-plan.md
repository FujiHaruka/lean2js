# 本体の陰性方向

`docs/entry-refusal-plan.md` が渡したのは入口の橋だけである ——「`eval` が受け取らない引数を生成コードも
受け取らない」。この文書は残りの半分 ——「**本体が落ちるとき、生成コードも同じコードで落ちる**」——
をどう述べ、どこまで証明するかを書く（決定 2026-09-08, ユーザーの指示）。

## 立てる主張

```
fragment_traps_in :
  InFragment e →
  EnvTyped p env ctx → EnvCovers env ctx → JsEnvAgrees env jenv →
  compileExpr p ctx e = .ok (je, ty) →
  evalExpr p f env e = .error err → err ≠ .outOfFuel →
  EventuallyErr m jenv je err.code
```

`EventuallyErr m jenv je code := ∃ g, ∀ g' ≥ g, Js.eval m g' jenv je = .error code` ——
`Eventually` の error 版である。

`fragment_correct_in` と揃えて、**コードまで一致する**ことを主張する。`Agree` の実行時検査が全ベクタに
ついて見ているのがまさにこれ（`agrees` は失敗どうしを `Err.code` で比べる）なので、ここで弱めると
検査と証明が別のことを言い始める。

## 落ち方は三つしかない

`applyUn` / `applyBin` が返しうる `Err` は `divByZero`・`int53Overflow`・`typeError` の三つで、
`evalExpr` が断片の中で足すのは `outOfFuel` と `unknownVar` だけである。主張の形はこの棚卸しから出る。

**`divByZero` と `int53Overflow` は両側で同じコードになる。** `mkInt53` が `int53Overflow` を返す
ところで `Js.Runtime.i53` が `"int53Overflow"` を投げ、`applyArith` の `b == 0` で
`i53div` / `u32div` / `bigdiv` が `"divByZero"` を投げる。ここが主張の中身である。

**`typeError` は届かない。** 断片の中で `applyBin` が型エラーを返せるのは被演算子の型が合わない
ときだけで、`compileExpr` が通っていれば `typeSound` がそれを禁じる。各演算子で潰す。

**`unknownVar` も届かない。** ただし `EnvTyped` は「ctx にある名前が env にもある」を**言っていない**。
言っているのは「両方にあるなら型が合う」だけである。そこで `EnvCovers env ctx` を足す。宣言の入口では
`bindParams` が引数を全部束ねるので満たされる。

**`outOfFuel` は除く。** 燃料は `eval` を全域にするための装置で、JS 側の主張は `EventuallyErr` で
「十分な燃料で」の形をしている。つまり参照側だけが燃料切れになる状況は、JS 側に写す相手がいない。
仮定 `err ≠ .outOfFuel` はこれを言っている。

## Approach

**`fragment_correct_in` と同じ帰納を、同じ順序で、error 側に沿って歩く。** 新しい証明技法は要らない。
効くのは、陽性方向より**各演算子でやることが少ない**ことである —— 型さえ合っていれば比較・等値・
`min` / `max` / 連結は落ちようがないので、その演算子の仕事は「落ちたなら型エラーで、型エラーは
`typeSound` が禁じる」の一行に潰れる。実質の中身は算術 5 つだけになる。

一段の形は毎回同じ二択である。

1. **部分式が落ちた** → 帰納法の仮定で JS 側の部分式が同じコードで落ち、生成した形がそれを伝える。
   伝わることは形ごとの補題にする（`eventuallyErr_binaryL` / `binaryR` / `call2L` / `call2R` /
   `andR` / `orR` / `condC` / `condT` / `condE` / `arrowArg` / `arrowBody`）。陽性方向の
   `eventually_*` と対になる。そのうえで、二項演算の 16 形については**コンパイラの表から一度だけ
   読み取る**（`numericHelper_errL` / `errR`、`compileExpr_bin_errL` / `errR`）—— そうしないと
   同じ議論を演算子ごとに 16 回書くことになる
2. **部分式は値を返し、演算が落ちた** → `typeSound` で被演算子の型を確定させ、`applyUn` / `applyBin`
   の落ちる枝を数え上げる。残るのは `mkInt53` の溢れと `b == 0` だけで、そこで JS 側のヘルパが
   同じコードを投げることを示す

短絡演算子（`&&` / `||`）だけは、右辺を評価しない枝があるので二択が三択になる。左辺が `false`
（`||` なら `true`）で確定するときは落ちようがない。

## 段取り

証明は一本の帰納なので、`sorry` を置いて刻むことはできない（置けば `Axioms.lean` の外でも
プロジェクトの規約に反する）。刻めるのは補題のほうなので、順序はこうなる。

1. `EventuallyErr`、`EnvCovers`、伝播の補題一式、`mkInt53` / `applyArith` の落ちる枝の反転補題 ——
   ここまでは独立にコミットできる
2. `fragment_traps_in` の帰納本体 —— 一発のコミット
3. 宣言まで持ち上げる（`decl_traps`）。`compileBody` が開いた `const` 文の列を error 側に歩き、
   入口の検査を通ったあとに本体が落ちるなら生成関数の呼び出しが同じコードを投げる
4. 例題への具体化と manifest の `Claim`、`Axioms.lean` の行、README と `docs/mvp-plan.md`

## 覆っていないもの

| 外れるもの | 理由 |
| --- | --- |
| 残り 29 形（`call` / `match` / 配列走査 / 辞書） | 分母は `InFragment` のまま。陽性方向と同じ幅で止める |
| `outOfFuel` | 参照側だけの概念で、JS 側に写す相手がいない |
| 未宣言の関数名（`Err.unknownFn`） | 断片に `call` が無いので届かない。断片を広げたときに戻ってくる |

## 守ること

- **コードの一致を落として「どちらも落ちる」に弱めない。** `Agree` が見ているのはコードの一致で、
  そこを弱めると検査と証明が別のことを言い始める
- **`sorry` で塞がない**（塞げば `Axioms.lean` が落ちる）
- **manifest に定理を足したら `Axioms.lean` に行を足す**
- **数字を動かしたら引用元を同じコミットで直す。** `README.md` と `docs/mvp-plan.md` が引用する
