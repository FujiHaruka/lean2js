# 入口の陰性方向

`Decl.decl_correct` は陽性方向だけの定理である ——「`eval` が値を返すなら生成コードも同じ値を返す」。
この文書は、その裏側 ——「**`eval` が受け付けない呼び出しは、生成コードも受け付けない**」—— を
どう述べ、どこまで証明するかを書く（決定 2026-09-08, ユーザーの指示）。

## 立てる主張

```
decl_refuses :
  compileProgram p = .ok m → p.find? fn = some d → d.isPublic = true →
  Js.dictKeysDistinctList jargs = true →
  ¬ EvalAccepts p d jargs →
  ∀ g, 2 ≤ g → Js.callFunctionAt m g fn jargs = .error "typeError"
```

`EvalAccepts p d jargs` は「その JS 引数列を符号化に持つ `Value` の列があって、本数も型も宣言どおり」
——つまり `evalCall` が本体まで進む引数列であること。それが**ひとつも無い**とき、生成関数は入口で
落ちる。

`decl_correct` と違って `InFragment` が要らない。入口の検査は本体の形を見ないので、この主張は
**公開関数 67 本すべて**に立つ。陰性方向のほうが陽性方向より広い。

燃料も `∃ g, ∀ g' ≥ g` の形にならない。入口の検査は `checkTy` という Bool 関数の 1 回の呼び出しで、
型の深さは燃料を食わない。2 あれば足りるので、出荷時の 10000 を取る `Js.callFunction` に直接下ろせる。

## 素直な逆は偽

`checkTy_encodeValue` の逆 —— `Value.hasTy p v ty = false → Js.checkTy (encodeValue v) d = false`
—— はそのままでは**成り立たない**。破れ方が三つあり、上の主張の形はその三つから決まっている。

**1. 符号化が数値の型を潰す。** `encodeValue (.int53 5)` も `encodeValue (.uint32 5)` も `.num 5` で、
JS 側に区別は無い。`Value.hasTy p (.uint32 5) .int53 = false` だが `Js.checkTy (.num 5) .int53 = true`
で、しかもこれは直しようがない —— 生成コードが `.num 5` を弾いたら `.int53 5` も弾いてしまう。

だから主張は Lean の値ではなく **JS の値**について述べる。境界を渡ってくるのは JS の値のほうで、
「`.num 5` は `eval` も受け取る引数の符号化である」は真である。この形にすると破れは消える。

**2. 模型の辞書は重複キーを持てる。** `Value.hasTy` は `keysDistinct` を要求するが、`Js.checkEntries`
はキーを見ない。生成コードが受け取るのは本物の `Map`（`__ck` は `x instanceof Map` を見る）で、
`Map` は同じキーを二度持てないから、実物にこの隙間は無い。隙間があるのは `JsValue.dict` を連想リストで
模型にしている側である。

だから仮定として書く：`Js.dictKeysDistinct jv = true`（値の中のすべての辞書でキーが相異なる）。
これは模型の緩さを明示する仮定で、成果物側では `Map` であることが与えている。

**3. 関数型の引数には検査が出ない。** `paramChecks` は `param.ty.isFn` のとき素の
`const name = __pN` を置くだけで、`tyDesc` も `.fn` でエラーになる。JS には関数の引数型を実行時に
見る手段が無いので、これも直しようがない。

除外の線はちょうど `Decl.isPublic`（関数型の引数を取らない）である。`decl_correct` がこれを要求
しないのと対になる —— **公開境界とは、検査が存在する範囲のことである**。

## Approach

**橋は 1 本で、向きが逆なだけ。** `checkTy_encodeValue`（`hasTy` が真 → `checkTy` が真）に対して、
`checkTy` が真なら**その JS 値は宣言どおりの `Value` の符号化である**ことを示す。逆像を構成する
証明なので、値の構造ではなく **JS 値の構造で再帰する**（`Js.checkTy` 自身の停止測度と同じ）。
`.named` を展開すると型は大きくなりうるので、型で再帰する道は無い。

そのうえで入口の文の列を歩き、各段で二択にする ——「検査が落ちて `typeError`」か「引数が復号できて
次へ」。最後まで復号できたら `EvalAccepts` が立つので、対偶が主張になる。

1. **逆像の補題** —— `checkTy_sound`。`tyDesc p b ty = .ok d` と `Js.checkTy jv d = true` と
   `Js.dictKeysDistinct jv = true` から `∃ v, encodeValue v = jv ∧ Value.hasTy p v ty = true`。
   `.uint32` の逆像は `UInt32.ofNat i.toNat`（`0 ≤ i < 2^32` が丸めを消す）、`.named` の逆像は
   `tyDescAlts_find` の逆 —— 記述子リストで見つかった構成子が、宣言側の `findAt?` でも見つかること
2. **入口の二択** —— `evalStmts_paramChecks_sound`。`paramChecks` の列を `evalStmts` で歩き、
   `.error "typeError"` か「復号できた `args` で `ParamsTyped`」の disjunction を返す
3. **本数** —— `f.params.length = d.params.length`（`rawParams_length`、既にある）。本数違いは両側とも
   入口で落ちる。`evalCall` は `Err.arity`、JS は `"typeError"` で**コードは違う**が、
   主張は「同じ落ち方をする」ではなく「どちらも落ちる」なので、ここは差し支えない
4. **例題への具体化** —— `add` の陰性方向を manifest の `Claim` に足し、`Axioms.lean` に行を足す

## 内訳

| ファイル | 足すもの |
| --- | --- |
| `Lean2Js/JsSem.lean` | `Js.dictKeysDistinct` / `dictKeysDistinctFields` / `dictKeysDistinctList` —— 値の中のすべての辞書でキーが相異なること。`Js.checkTy` の隣に置く |
| `Lean2Js/Decl.lean` | `Js.checkTy` の「真 → 形」の反転補題一式（`checkTy_bool_inv` …、`.option` / `.result` / `.ctors` は場合分けを畳んだ形）、`tyDescAlts_find_inv`、`checkTy_sound` の相互再帰 4 本、`EvalAccepts`、`evalStmts_paramChecks_sound`、`decl_refuses` と `Js.callFunction` での系 |
| `Lean2Js/Example.lean` | `add_refuses`（`decl_refuses` の具体化）と manifest の `Claim` |
| `Lean2Js/Axioms.lean` | `add_refuses` と `decl_refuses` の `#print axioms` |
| `README.md` | 「保証の組み立て」の**境界の検査**の行 —— 今は実行時検査が受け持っている主張が、公開関数 67 本について証明に変わる |
| `docs/mvp-plan.md` | Phase 2 の到達点に陰性方向を書く |

`Js.dictKeysDistinct` も `checkTy_sound` も、`mapM` と `partial` を避けた明示の再帰で書く。理由は
`docs/decl-correctness-plan.md` の「展開できること」と同じで、証明が展開できないものは橋に使えない。

## 覆っていないもの

| 外れるもの | 理由 |
| --- | --- |
| 関数型の引数を取る宣言 | 検査が出ない。JS に関数の引数型を実行時に見る手段が無い。`d.isPublic` がその線 |
| 重複キーを持つ辞書 | 模型の `JsValue.dict` が連想リストであることの緩さ。本物は `Map` で、`Js.dictKeysDistinct` を仮定として明示する |
| 本体が落ちる場合（`divByZero`・`int53Overflow` ほか） | ここで渡すのは**入口**の橋だけ。本体の陰性方向は `fragment_correct` の陰性版が要る |
| 未宣言の関数名（`Err.unknownFn`） | 別の橋（`compileDecls` が名前の不在を保つこと）。ここには含めない |

## 守ること

- **陰性方向が述べにくいからといって、命題を弱めて通さない。** 破れの三つはどれも「主張の形が
  間違っていた」のであって、「主張を諦める」ではない
- **`sorry` で塞がない**（塞げば `Axioms.lean` が落ちる）
- **manifest に定理を足したら `Axioms.lean` に行を足す**
- **数字を動かしたら引用元を同じコミットで直す。** 陰性方向が覆う本数は `README.md` と
  `docs/mvp-plan.md` が引用する
