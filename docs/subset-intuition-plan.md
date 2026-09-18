# サブセットの輪郭を直感で持てるようにする計画

構文表は「何が書けるか」を全部書いているが、**原則**を書いていない。Lean を書ける人が
「こういうのは書けそう / これは書けなそう」を頭の中で判定できないので、毎回 `SYNTAX.md` と
にらめっこすることになる。学習コストの大半はここにある。

## ゴール

**3 つの問い**で 9 割が予測できる状態にする。そのうえで、その説明を嘘にしている例外を
——文書で言い訳するのではなく——**コンパイラ側で消す**。

原則（`SYNTAX.md` に置く形）:

1. **その値は境界に置けるか。** 値の集合は `Core.Ty` の 11 形で閉じている。**関数は値ではない。**
2. **繰り返しは 6 つの走査で書けるか。** `map` / `filter` / `find?` / `all` / `any` / `foldl`。再帰は無い。
3. **その名前は lean2js の語彙か。** Lean 標準ライブラリはほぼ読まない。`Arr.*` / `Str.*` / `Dict.*` /
   `Opt.*` / `Exc.*` / `Int53.*` / `BigInt.*` から取る。

背後にある 1 行は「**JS 側の答えが一意に決まるものだけを読む**」で、3 問はその帰結。

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

- 冒頭に 3 つの問いと、Lean 使いが最初に打つ反射（`Nat` / 構造的再帰 / `xs.length` / `do` /
  `[BEq α]`）がどの問いで落ちるかの表。
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
