# サブセットの輪郭を直感で持てるようにする計画

構文表は「何が書けるか」を全部書いているが、**原則**を書いていない。Lean を書ける人が
「こういうのは書けそう / これは書けなそう」を頭の中で判定できないので、毎回 `SYNTAX.md` と
にらめっこすることになる。学習コストの大半はここにある。

## ゴール

**2 本の線**で 9 割が予測できる状態にする。そのうえで、その説明を嘘にしている例外を
——文書で言い訳するのではなく——**コンパイラ側で消す**。

原則（`SYNTAX.md` に置く形）:

1. **値は JS が持っている 7 種のどれか。** `boolean` / `number` / `bigint` / `string` / `Array` / `Map` /
   タグ付きオブジェクト。`Option` / `Except` / `deriving Enc` した型は全部タグ付きオブジェクト、`Dict` は
   `Map`。語彙が `Arr.*` / `Str.*` / `Dict.*` / `Int53.*` / `BigInt.*` なのも同じ線で、それらは **JS の
   演算の名前**だから。`List.length` が読めないのは禁止だからではなく `Nat` が 7 種に無いから。
2. **呼び先は上に書かれた名前。** 再帰もクロージャもその場で作る関数も無く、関数は宣言の名前としてしか
   存在しない。これが「燃料を構文から数え切れる」の中身（`Cost.lean`: 呼び出しは宣言の並びを後ろ向きに
   しか進まないので、スタックの深さは宣言の本数で頭打ち）。走査が 6 つなのも同じ線。

読み手が打つ反射は 1 つ:「**素の JS で、関数を変数に入れず、ループは `Array` のメソッドだけで書けるか**」。
No ならここでも No。Yes でも落ちる例外は短い（小数 / `sort` / 正規表現 / `Set` / `Date` / `null` /
副作用）。**「書けるか」と「答えが同じか」は別の問い**で、後者は振る舞いの差の節が持つ。

## Approach

**例外を消してから書く。** 文書の側で「ただしこの形は通らない」と断るほど原則は嘘に近づくので、
順序は〈計測 → コンパイラを直す → 残った線を原則として書く → 拒否メッセージを原則と同じ語彙に揃える〉。
最後の一手（メッセージ）は、文書と walk が別々に動いて食い違うのを `#guard_msgs` に見張らせるためのもの。

計測の段は既存の 3 段階をそのまま使う: `lake env lean`（walk だけ）⊂ `ship_package` を置いた
`lake build`（証明書まで）⊂ `lake exe lean2js`（Node 上の差分まで）。**新しく書けるようになった形は
`Example.lean` に 1 本ずつ置く**。そうしないと「書ける」と書いた形が Node 上の差分検査を通っていない。

保証の境界は動かない: `Core.Expr` は 35 形のまま、`Eval` も `Compile` も触らない。動くのは
**Reify（Lean の項をどう読むか）だけ**で、増えるのは公開関数の本数とベクタ件数。

## Step 1. 走査のラムダの中の `match` — 完了

**書けるようになること**: `xs.map (fun s => match s with | ...)`。これまでは walk は読むのに
`ship_package` が型不一致で落ちた（`docs/operations-plan.md` の「入らなかったもの」）。`Opt.*` / `Exc.*`
を走査の中で呼ぶ形も同じ壁だったので、同時に通る。

**原因**: 走査の補題（`denotes_mapE` 他）の関数引数 `g` を `_` で渡していた。`g` が未決のまま
アームの証明を組むと、アームの期待型が `Denotes _ _ body (?g x)` にしかならず、splitter の
major premise が束縛変数 `x` ではなく外側のメタ変数に解かれる。`docs/operations-plan.md` が
記録している失敗 2 手（motive の括り出し、major premise の自由変数抽象）はどちらも
major premise 側を触っていて、**原因は `g` 側だった**。

**直し方**: `matchedFn` が使っていた自由変数の抽象を `closedOver` として括り出し、`traverse` /
`quantified` / `reduceE` が `g` をそれで明示的に渡す。`Reify.lean` だけ、10 行。

## Step 2. `@[expand]` の高階ヘルパにラムダを渡す — 完了

**書けるようになること**: `Arr.count xs (fun n => n > 0)`、`Arr.flatMap` / `Dict.ofPairs` /
`Opt.map` / `Exc.map` / `Exc.mapError` も同じ。これまでは宣言の名前しか渡せなかった。

**原因**: `@[expand]` を書き出すと本体に `p y` の β redex が残り、walk はそれを
「ラムダが値になっている」と読んでいた。`Reify.lean` に `headBeta` は 1 か所も無かった。

**直し方**: `walk` の先頭で `e.headBeta`。1 行。β は defeq なので証明側は動かない。

## Step 3. 負のリテラル — 完了

**書けるようになること**: `-1`（式でも `match` のパターンでも）。`Int` と `BigInt` の両方。

**原因**: 意味論にもテキスト層にも制限は無かった（`Core.Lit.int53` は `Int` を持ち、
`renderInt` / `parseInt` は負を往復する証明つき）。walk が `Syntax.mkNumLit` で負の数値リテラル構文を
組めなかっただけ。

**直し方**: `intLit` を足して、負なら `-(その絶対値)` の構文にする。

## Step 4. 原則を `SYNTAX.md` に置く — 完了

- 冒頭に原則と、Lean 使いが最初に打つ反射（`Nat` / 構造的再帰 / `xs.length` / `do` /
  `[BEq α]`）がどの線で落ちるかの表。
- 語彙表に「**なぜ Lean のそれではないか**」の列（再帰実装 / `Nat` を返す / 部分関数 / JS と答えが違う）。
  材料は `Prelude.lean` 冒頭の docstring にすでにある。利用者向けには一度も出ていない。
- 「型クラスは無い」を「**実行時に残らなければよい**」に直す。`if` の `Decidable` と `@[expand]` の
  `[Inhabited α]` / `[BEq α]` が通る理由がこれで説明でき、`@[ship] def` が単相な理由と両立する。
- **振る舞いの差を別節に出す**（`Str.toInt?` の狭さ、code point 単位、`Str.replace` の空パターン、
  trap、`-0`）。「書けるか」ではなく「同じ名前で答えが違うか」なので、構文の表に混ぜると原則がぼやける。
- Step 1〜3 で消えた制限の記述を落とす。

## Step 5. 拒否メッセージを原則と同じ語彙にする — 完了

`reify: <term> is outside the subset this walk reads` は総称で、3 問のどれで落ちたかを言わない。
**Q1 / Q2 / Q3 に対応する 3 つの定型文**（`valueRule` / `repeatRule` / `vocabularyRule`）を持たせ、
`Lean2Js/Denote.lean` に 1 ルール 1 件の `#guard_msgs` を置いた。文書と walk が同じ文を使うので、
片方だけ動かせば `lake build` が落ちる。

**文は行を分けて付ける。** 末尾に ` — ` で continue すると、メッセージ全体が長くなった分だけ
pretty printer が**項のほうを折る**（`reify: a /\n  b is outside ...`）。改行を 1 つ入れると項は
1 行に残り、規則がその下に来る。

## Step 6. 3 つの問いを 2 本の線に畳む — 完了

Step 4 の 3 問は「リストを 3 つ覚える」形のままで、原則になっていなかった（Q1 は 11 型、Q2 は 6 走査、
Q3 は語彙表）。**Q1 と Q3 は同じ 1 本**——どちらも「JS の値と演算しか無い」の言い換え——で、**Q2 と
「関数は値でない」も同じ 1 本**なので、2 本に畳んだ。

**確かめたこと**（推測ではなく出力と docstring）:

- `Value` は `bool` / `int53` / `uint32` / `str` / `bigint` / `obj (ctor, fields)` / `arr` / `dict` /
  `fn (name)`。JS 側に落とすと `boolean` / `number` / `bigint` / `string` / `Array` / `Map` /
  タグ付きオブジェクトの **7 種**（`int53` と `uint32` はどちらも `number`）。生成物に
  `{ tag: "some", value: v }` と `new Map([...])` がそのまま出ている。
- 6 走査の実体は `__map` / `__filter` / `__find` / `__all` / `__any` / `__reduce` で、**どれも `for...of`
  1 回**。JS の `Array` のメソッドそのもの。
- 2 本目の理由は `Cost.lean` 冒頭にすでに書かれていた。「関数引数も*先に宣言された関数の名前*でしかない
  ので、スタックの深さは宣言の本数で抑えられる」。**燃料はこの制限が買うものではなく、この制限そのもの
  の理由**。
- `exprDepth` は `mapE` に `1 + max(...)` を払う。走査が無料なのは**配列の長さ**に対してであって、
  走査のノード自体ではない。文はそこまで正確に書く。

**`repeatRule` の文言を直した。** 「a function is never a value」は `Value.fn (name)` があるので嘘。
「a function is only ever the name of a declaration」に。`Denote.lean` の `#guard_msgs` も同じ文に更新。
