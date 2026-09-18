# 操作の拡張計画

`docs/business-logic-plan.md` が広げた部分集合に、JS の業務ロジックで頻出するのに今は書けない操作を
足すための計画。**進捗は末尾の「結果」にある。**

## 文脈

今の到達点は測った数字で言える。公開関数 70 本、manifest の定理 27 本、出荷前に照合する差分ベクタ
25511 件、`Core.Expr` は 35 形。実行時ヘルパは 49 本で、模型がヘルパについて仮定している表 35 行の
全行が印字器の書き出すソースと一致する（`helpers_ship_as_modelled`）。JS の組み込みへの依存は
`Helper.lean` が名指ししている `prim` 11 種とメソッド 13 種で、それが読み取れる TCB の全部。

**値段が変わったことが、この計画の出発点。** `decl_correct` / `decl_traps` / `decl_refuses` は但し書き
無しで 35 形すべてを覆っている。`Core.Expr` に形を 1 つ足すのは、もはや「`Agree` の全件検査に任せる
ものが 1 つ増える」ことではなく、**すでに閉じている証明に場合を 1 つ開けて閉じ直すこと**になった。
`docs/next-milestone-plan.md` が「言語が凍っている」を到達点として数えているのはこのため。

実地で最初に詰まるのは数値→文字列で、金額や ID の組み立てがすべて TS 側へ出る。次が文字列の整形、
その次が並べ替え。

## ゴール

- JS の業務ロジックで頻出する操作のうち、**意味論に新しい概念を足さずに書けるもの**が全部書ける
- 何が無いかが、`reify:` の拒否より前に分かる

## 非目標

| 外すもの | 理由 |
| --- | --- |
| Float | `docs/business-logic-plan.md` の判断のまま |
| `Date` / タイムゾーン / DST / ロケール整形 | `Date` は可変で、内部値が double で、`getMonth` の答えが実行環境の TZ という ambient state で変わり、パースに実装定義が残る。対応が一意という基準を全部外す。**業務ロジックが要るのは日付の値のほうで、epoch millis の `Int` と自前の暦 `structure` は今の部分集合でそのまま書ける** |
| 正規表現 | 意味論に正規表現エンジンが入る。TCB が桁で増える |
| クロージャ / async / 公開境界の関数 | `docs/next-milestone-plan.md` の決定のまま |
| 現在時刻・乱数・採番 | 引数で受け取る。純粋なコアの外 |

## Approach

操作を、**意味論に何を足すか**で三層に分ける。層が違うと値段が桁で違う。

- **層 0 — `Core.Expr` に形を足さない。** 既存の形の組み合わせで書ける操作。`Eval` / `Compile` /
  `JsSem` / `Step` / `Sound` / `Correct` / `Helper` は 1 行も動かない。
- **層 1 — 形を 1 つ足す。** 1 操作あたり 20 ファイル強（`substring` を触っているファイル数で測った）。
  内訳は意味論（`Eval`）・型付けと生成（`Compile`）・生成コードの模型（`JsSem`）・抽象機械の継続フレーム
  （`Step` / `StepAgree`）・燃料（`Cost` / `Fuel`）・印字と読み戻し（`Render` / `Renderable` /
  `Roundtrip`）・実行時ヘルパとその一致証明（`Helper` / `HelperSem` / `HelperProof` / `HelperAgree`）・
  reify の証明項（`Denotes` / `Reify`）・**型健全性（`Sound`）とコンパイラ正当性（`Correct`）の場合**。
- **層 2 — 意味論に新しい概念。** 全順序、浮動小数、正規表現エンジン。入れない。

**層 0 を先に全部やる。** 凍結を解かずに「足りない」の相当部分が消え、層 1 に残るものが小さくなる。
層 0 を 1 件ずつ `Reify.lean` の分岐表に足すのは筋が悪い —— 表が長くなるだけで、利用者は同じことを
自分の `def` でできない。**機構を 1 つ入れて、語彙はその上のただの Lean の `def` にする。**

その機構に案が 2 つある。

- **案 A: 呼び出し位置に展開する。** 印を付けた `def` を reify が展開し、既存の形へ落とす。
  生成 JS に関数が増えない代わりに、式が深くなって燃料を食う。
- **案 B: 出荷はするが公開境界に出さない。** 印を付けた `def` を宣言として読み出し、`index.js` には
  関数として出すが `.d.ts` と輸出には出さない。呼び出しは普通の `call` のまま。

**案 A を採る。決め手は多相性で、`Gather` の値段ではない。** `Core.Decl` が持つのは `List Param` と
`Ty` だけで、型変数の置き場が無い。`@[ship] def take (xs : List α) (n : Int)` は
`reify: Type has no Enc instance, so there is no subset type to give it` で断られる（測った）。
層 0 の表はほとんどが多相 —— `take` / `drop` / `head?` / `contains` / `flatMap` / `groupBy` /
`Dict.map` / `Option.getD` —— なので、**案 B はこの語彙の宿主になれない。** 案 B で通すなら呼び出し
ごとの単相化（`Gather` で型ごとに宣言を作り分け、名前を割り当てる）が要り、それは展開より高い。
案 A なら呼び出し位置で `α` はすでに `Int` か `String` なので、展開した項はそのまま walk が読める。

**そして案 A は `Reify.lean` の外を 1 行も動かさない。** `Decl` にも `Compile` の `exported` にも
`Gather` にも `Dts` にも手が要らず、`Core.Expr` は 35 形のまま、`Sound` と `Correct` の分母も動かない。
`docs/next-milestone-plan.md` が数えている凍結は、**この機構では解けない。**

この機構が入ると、層 0 の語彙は `Prelude.lean` に**部分集合の中だけで書かれた非再帰の `def`** として
並ぶ。同じ印は利用者にも開く —— 出荷したくない補助関数を書けないのは今の不便のひとつ。

## Step 0. 無い操作を一覧にする（完了）

**書けるようになること**: 何も。`templates/verified-package/SYNTAX.md` は「書けるもの」の表しか持って
いないので、`sort` や `toString` が無いことは `reify:` に断られて初めて分かる。断り文言は止まった項を
名指しするだけで、代わりに何を書くかを言わない。

**形**: SYNTAX.md に「無い操作と、代わりに書くもの」の表を 1 つ足す。`sort` / `join` / `replace` /
`toString` / `parseInt` / `Date` / 正規表現 / Float に、代替（自前の暦 `structure`、TS 側へ出す、
`foldl` で書く）か「入れない理由」を 1 行ずつ。

**触る場所**: `templates/verified-package/SYNTAX.md` だけ。

**保証の境界**: 変わらない。他のどの Step とも独立で、いちばん安い。

## Step 1. 呼び出し位置に書き出す `def`（層 0 の機構、完了）

**書けるようになったこと**: 補助の `def` を、公開境界に出さずに呼べる。そして**その `def` は多相でよい**。

**形**: Approach の案 A。`@[expand]` を付けた `def` を walk が呼び出し位置で展開する。
展開先は定義展開で元の項と同じなので、その場で組む証明項がそのまま証明書になる。

**印を付けられるのは非再帰で、本体が部分集合の中だけで書かれた `def`。** 再帰は印の位置で断る
（`WellFounded.fix` / 再帰子が walk に届くと、どのファイルにも無い項を名指すエラーになる）。
本体が部分集合を出たときも、印を付けた `def` の名前を先に言う。

**触った場所**: `Lean2Js/Expand.lean`（新設、45 行、印とその検査だけ）、`Prelude.lean`（import 1 行）、
`Reify.lean`（walk の落ち先に分岐 1 つと `expanded` ヘルパ 1 つ）、`scripts/check-template.sh`（拒否 2 件と
「生成物に残らない」1 件）、`SYNTAX.md`。**`Core` / `Compile` / `Gather` / `Dts` / `Decl.lean` は動かない。**

**保証の境界**: 変わらない。`Core.Expr` は 35 形のままで、出荷する宣言の集合も変わらない——
印を付けた `def` はプログラムに入らないので、`decl_correct` / `decl_traps` / `decl_refuses` の分母にも
入らない。ただし**印を付けた `def` それ自体にはベクタが作られない**（ベクタは公開宣言ごと）。
層 0 の語彙は、それを使う公開宣言が `Example.lean` に無いかぎり差分テストに掛からない。Step 2 で
語彙 1 つにつき公開宣言を 1 本足すこと。

**燃料は展開した分だけ増える。** 式が深くなるので、`ship_package` の天井（10000）に近づくのは
呼び出しの数ではなく語彙の入れ子の深さ。

## Step 2. 層 0 の語彙

**書けるようになること**: 意味論を 1 行も動かさずに、下の操作。

| 受け手 | 足すもの | 既存の形での書き方 |
| --- | --- | --- |
| `List T` | `take` `drop` | `slice` |
| | `isEmpty` `contains` `sum` `count` | `length` / `any` / `foldl` |
| | `head?` `last?` `min?` `max?` | `cond` + `index`、`foldl` |
| | `indexOf?` `flatten` `flatMap` | `foldl`（添字を持ち回る / `++` で畳む） |
| | `groupBy`（キーは `String`） | `foldl` + `Dict.get` / `Dict.set` |
| `Dict V` | `getD` `map` `filter` `ofPairs`（計算キー） | `keys` + `foldl` + `set` |
| `Option` / `Except` | `getD` `map` `toOption` `mapError` | `match` |
| `String` | `isEmpty` | `length` |

**`zip` は入れない。** 2 本の配列から組の配列を作る形だが、`Ty` に組が無い。自分の `structure` を
宣言すれば書けるので、型を 1 つ足すほどの値打ちが無い。

**`Dict.map` / `Dict.filter` は生成コードが O(n²) になる。** `keys` を回して `get` を引く形なので、
`Map` の `get` が O(1) でも走査そのものが n 回入る。件数が小さい業務ロジック向けと割り切るか、
層 1 の走査として足すかは、実際に困ってから決める。

**触る場所**: `Prelude.lean`（語彙を `@[expand] def` として）、`Example.lean`（語彙ごとに公開宣言を
1 本）、`SYNTAX.md`。`Reify.lean` は Step 1 の機構が効くので動かない。

**保証の境界**: 変わらない。`Core.Expr` は 35 形のまま。

## Step 3. 数値 ⇄ 文字列

**書けるようになること**: `Int53.toString` と `Str.toInt?`。金額・ID・キーの組み立てが Lean 側に残る。

**`String(n)` は Int53 の範囲で 10 進表記と一致する。** JS が指数表記に落ちるのは |n| ≥ 1e21 で、
Int53 の上限 2^53-1 ≈ 9.007e15 はその下。だから「対応が一意」という基準を満たす。

**`Number()` は使わない。** 空文字列を 0 にし、`0x` を読み、前後の空白を飛ばす。受け付ける文字列を
`-?[0-9]+`（先頭ゼロなし、Int53 の範囲内）と自分で定義し、外れたら `none` を返す手書きヘルパに落とす。
`toInt?` が `Option` を返すので trap は無い。

**形を増やさずに済むか先に見る。** `toString` は `Int → String` なので `UnOp` に演算子として足せば
`Core.Expr` は 35 形のまま（`Sound` と `Correct` には `un` の下の場合が 1 つ増える）。`toInt?` は
`String → Option Int` で、`StrUnOp` は `String → String` を前提にしている。どちらに置くかは
`Eval` / `Compile` の型付けを読んでから決める。**形が増えないほうが、証明の分母が動かない。**

**触る場所**: 層 1 の一式。`Helper` に 2 本（`prim` の `String` と手書きのパーサ）。

**保証の境界**: 変わらない。覆う側が増える。

## Step 4. 文字列の組み立て

**書けるようになること**: `Str.join` / `Str.replace` / `Str.padStart` / `Str.repeat` /
`Str.indexOf?`。Step 3 と合わせて、金額整形が Lean 側で書き切れる。

**`join` は JS 組み込みへの依存を増やさない。** `Helper.lean` はすでに `join` を名指ししている。

**`replace` の空パターンは JS 固有。** `"abc".replaceAll("", "-")` は各位置に挿入する。意味論を
そこに合わせる価値が無いので、空パターンは拒否する（コンパイル時に落とせるのはリテラルのときだけ
なので、実行時の trap になる）。

**`padStart` / `repeat` はコードポイントで数える。** `Str.length` と同じ基準。ネイティブの
`padStart` は UTF-16 単位で数えるので手書きヘルパに落ちる。

**触る場所**: 層 1 の一式 × 5。ここがこの計画でいちばん重い。**1 つずつ入れて、1 つ入るたびに
ゲートを全部通す。**

**保証の境界**: 変わらない。

## Step 5. 並べ替え（決定を覆す提案）

**`sortBy` は `docs/next-milestone-plan.md` で非目標に置いてある。** 理由は「比較関数が全順序である
ことと、等しいキーでの安定性が Lean 側と一致することの両方が要る」——  意味論に新しい概念を足す側だから。
**その判断はそのまま据え置く。** ここに書くのは、覆すとしたらどの形なら層 1 に収まるか。

**比較関数を渡さない形にすれば、全順序は型から出る。** `Arr.sortByKey xs key` の `key` は宣言の名前
だけで、返りは `Int` か `String` に限る。この 2 つの順序は組み込みで、全順序であることは Lean 側の
定理として既にある。利用者に証明義務は生じない。

**安定性は JS 側が仕様で保証している。** `Array.prototype.sort` の安定性は ES2019 で仕様化された。
ただし比較関数を渡す形になるので、**Lean の `List.mergeSort` と同じ列を返すことの証明**は要る。
残る仕事はそこ 1 つで、これは層 1 に収まる。

**判断は着手時に。** 上が正しければ値段は Step 4 の 1 操作分と変わらない。据え置きの理由が消えた
わけではなく、「関数を渡す形をやめれば消える」という見通しが立っただけ。

## 順序と依存

Step 0 → Step 1 → Step 2 → Step 3 → Step 4 →（Step 5 は判断）。

Step 1 は Step 2 の前提。Step 2 は Step 3 以降と独立だが、先にやると層 1 に残るものが減る。
Step 3 と Step 4 は互いに独立で、Step 3 のほうが実地で先に困る。

## 証明との関係

層 0 は分母を動かさない。層 1 は 1 操作につき `Sound` と `Correct` に場合が 1 つずつ増え、
`Core.Expr` の形も 1 つ増える。**README の「35 の形すべて」は形の数ごと動く数字なので、
形を足したコミットで同じ数字を直す。**

`UnOp` / `StrBinOp` の演算子として足せるものは形が増えないので、分母は 35 のまま、覆う側だけが厚くなる。
**形を足す前に、既存の形の演算子として足せないかを必ず先に見る。**

## 動かすドキュメント

- `README.md` — サブセットの表、「35 の形すべて」
- `templates/verified-package/SYNTAX.md` — 書けるものの表、Step 0 で足す無いものの表
- `docs/guarantees.md` — ベクタ件数（今 25511 件）、実行時ヘルパの本数と仮定の表の行数
- `docs/next-milestone-plan.md` — 「言語が凍っている」を数えている行。**Step 1 と Step 2 では動かない**
  （層 0 は `Core.Expr` に形を足さない）。動くのは Step 3 以降で、そのとき凍結をどの範囲で解いたかを書く

## 結果

- **Step 0**（2026-09-18, `9e8c2b6` → 訂正 `c02f308`） — `SYNTAX.md` に「Operations that are not
  there」を足した。`sort` / `toString` / `parseInt` / `join` / `replace` / `padStart` / 正規表現 /
  `Date` / Float / 乱数・時刻の 10 行に、代替か「入れない理由」を 1 行ずつ。`foldl` と
  `Arr.slice` で今日書ける 7 行（take / drop / isEmpty / contains / sum / head? / flatten）と
  `join` の全文付き。
- **Step 1**（2026-09-18, `1b3aec6`） — `@[expand]` が入った。`Lean2Js/Expand.lean`（印と非再帰の検査）、
  `Reify.lean` の walk に分岐 1 つ。`Core` / `Compile` / `Gather` / `Dts` / `Decl.lean` は 1 行も動かなかった。
  `check-template.sh` に 3 件（多相な印が 2 型で使えて生成物に名前を残さないこと、本体が部分集合を出たとき
  印の名前で断ること、再帰を印の位置で断ること）。
- **訂正**（`c02f308`） — Step 0 に載せた `join` の全文が `ship_package` を通らなかった。
  `lake env lean` は `reify_decl%` しか走らず、証明書（citing）を作らない——**検証には 3 段階ある**：
  `lake env lean`（walk だけ）⊂ `ship_package`（証明書と compile と燃料）⊂ `lean2js --out`（ベクタを Node で）。
  **以降、文書に載せるコードは `ship_package` まで通す。**
