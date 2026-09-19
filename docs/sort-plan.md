# 並べ替え —— `Arr.sortByKey` を 36 形目として入れる

`docs/operations-plan.md` Step 5 は「値段ではなく順番の問題」で据え置きにしていた。凍結を開ける判断は
下りた（2026-09-19, ユーザーの指示）。ここに書くのは、開けた先で何をどの順で足すか。

## 何を入れるか

**`xs.sortByKey(x => key)`** —— 走査 1 つ。`Core.Expr` は 35 形から 36 形になる。

**比較関数は取らない。** 利用者が渡すのはキーを作る式だけで、キーの型は `Int53` か `String` に限る。
この 2 つの順序は組み込みで、全順序であることは Lean 側に既にあるので、**利用者に証明義務が出ない**。
比較関数を取る形を避ける理由はもう 1 つあって、そちらのほうが重い —— 比較は `evalExpr` の mutual
ブロックの中で呼ばれることになり、マージの再帰が `(fuel, 1, xs.length)` の測度に収まらない。

**binder + body（`mapE` と同じ形）にする。** `operations-plan.md` は「`key` は宣言の名前」と書いて
いたが、全順序はキーの**型**から出るので名前に縛る必要がない。他の走査 5 つと同じ形のほうが、
`Reify` も `Render` も `Correct` も型紙がそのまま効く。

**燃料は増えない。** キーは `evalMapItems` と同じ 1 パスで作り、並べ替えそのものは mutual ブロックの
外の純粋な関数。`Cost.lean` の「長い配列はタダ」がそのまま生き残る。

## 意味論

`Lean2Js/Sort.lean`（新規）に、core の `List.mergeSort` と同じ列を返す `msort` を、**ヘルパの形に
合わせて**置く。core の `mergeSort` は `splitInTwo` が部分型（`{ l // l.length = n }`）を運ぶので、
ヘルパとの同値証明がその部分型の等式に引きずられる。自前の `msort` は `take` / `drop` で割り、
`msort_eq_mergeSort` 1 本で core に橋を架ける —— これで `mergeSort_perm` と `merge_stable` が
利用者の定理にそのまま届く。

キーの比較は既にあるものを使う。`Int53` は `≤`、`String` は `compare`（コードポイント順、`eval` の
`<` と同じ）。JS 側の `String` も `__strcmp` を通すので、**模型が仮定する JS 組み込みの表は 1 行も
動かない**。

キーが `Int53` と `String` に揃っていない配列は `eval` が型エラーにする。型検査が通った
プログラムではそこに来ないのは、`filter` の述語が `Bool` でない場合と同じ扱い。

## 生成する JS

ネイティブの `Array.prototype.sort` は使わない。使えば V8 の TimSort を模型に足すことになる。
手書きヘルパを 4 本足す（56 → 60 本）。

| ヘルパ | 中身 |
|---|---|
| `__keyle` | スカラ 2 つの `≤`。`typeof` が `"string"` なら `__strcmp(a, b) <= 0`、でなければ `a <= b` |
| `__merge` | 整列済み 2 本を 1 本に。**ループ 1 本 + 添字 2 つ** |
| `__msort` | `length <= 1` で返し、`(n+1)/2` で割って自分を 2 回呼び、`__merge` |
| `__sortBy` | キーと元の値の組を作り、`__msort` して、組の右側を取り出す |

**`__merge` を再帰で書かない。** `xs.slice(1)` で再帰する素直な形は**再帰の深さが n** で、V8 の
スタックは 1 万フレーム前後 —— 数千要素の配列で生成 JS だけが RangeError を投げ、`eval` は成功する。
これは性能の話ではなく保証の穴。`__aconcat(xs, ys)` を 1 周する `forOf` に添字 2 つを持たせれば
深さは定数に戻り、`Helper.Stmt` に形は増えない。`__msort` の再帰は深さ log n なので問題ない。

ヘルパ言語に `else` も `continue` も無いので、どちらから取るかは式で決めて `push` は 1 回だけ書く。

## 触る場所と順

1. `Sort.lean`（新規） —— `merge` / `msort` / `msort_eq_mergeSort`
2. `Core.lean` —— `sortByKeyE`（36 形目）
3. `Eval.lean` —— キーの 1 パス + 並べ替え
4. `Cost.lean` / `Fuel.lean` / `Gather.lean` / `Step.lean` / `StepAgree.lean` / `Render.lean` / `Builder.lean`
5. `Js.lean` / `Compile.lean`（キーの型を `Int53` か `String` に絞るのはここ）/ `JsSem.lean` / `Parse.lean` / `Roundtrip.lean`
6. `Helper.lean` / `HelperProof.lean` / `HelperAgree.lean`
7. `Sound.lean` / `Decl.lean` / `Correct.lean`
8. `Prelude.lean`（`Arr.sortByKey`）/ `Denotes.lean` / `Reify.lean`
9. `Example.lean` / `Axioms.lean` / `Vectors.lean` / `Tests.lean`
10. 文書 —— `SYNTAX.md` の「無い操作」から `sort` の行を消し、`business-logic-plan.md` /
    `next-milestone-plan.md` / `operations-plan.md` の非目標を畳む。ベクタ件数と燃料を
    `README.md` / `docs/guarantees.md` / `docs/mvp-plan.md` で同じコミットで直す。

いちばん重いのは 6 の `__merge` —— 添字 2 つの不変条件で、型紙は `calls_filter`。次が 7 の
`Correct.lean`。

## 保証の境界

**動かさない。** 走査が 1 つ増えるだけで、証明が届く範囲も実行時検査が受け持つ範囲も今までどおり。
`InFragment.all` は 36 形すべてを覆ったままにする —— 1 形だけ外に置けば、それは保証を弱めて
緑にすることになる。
