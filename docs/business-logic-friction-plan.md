# 業務ロジックを書かせてみた結果と、摩擦を潰すまでの計画

2026-09-19 に、5 つの業務ロジックを**文書だけを読む外部の利用者**に書かせた実測と、それを潰すまでの計画。
`docs/adoption-blockers-plan.md` が「テンプレを cold start して Quickstart が通るか」を見たのに対し、
ここが見たのは**自分の業務ロジックを最後まで書き切れるか**。

## 調べかた

5 人の独立したセッション（sonnet）に、それぞれ隔離したサンドボックス（コンパイラのクローン＋テンプレ）と、
プロダクトマネージャが書いた体裁の仕様を 1 本ずつ渡した。仕様にはサブセットの語彙を一切使っていない。

読んでよいのは `README.md` / `SYNTAX.md` / `PROVING.md` / `docs/guarantees.md` / `docs/index.md` と
コンパイラのエラー出力だけ。`Lean2Js/**`・`Example.lean`・`packages/**`・`docs/*-plan.md` は禁止。
詰まったら 3 回で諦めて「ソースを読みたくなった質問」として記録し、機能を落とす。ビルドごとに
`MyLogic.lean` をスナップショットさせ、自己申告と独立に追跡できるようにした。

到達条件は `lake build` → `lake exe lean2js` → **Node から `dist` を実際に呼ぶ**、定理 3 本以上。
走らせる道具は `scripts/dogfood/`（`setup.sh` / `BRIEF.md` / `specs/`）に置いた。

**禁止は守られた。** 5 本のセッションの全ツール呼び出しを `lean2js-dep/` への参照で数えると、
触れたのは `README.md` / `docs/index.md` / `docs/guarantees.md` だけで、`Lean2Js/**` は 0 件。

**ただし文脈の漏れが 1 つある。** 5 人とも、このリポジトリ自身の `CLAUDE.md` と
`MEMORY.md`（「Lean proof idioms in lean2js」など）が context に入っていたと自己申告している。
どれもコンパイラの開発についてであって使い方ではないが、証明側の摩擦はいくらか
**過小評価されている**可能性がある —— それでも詰まりは 7 件出た。

| # | 業務ロジック | 踏ませたかったもの |
| --- | --- | --- |
| 1 | EC の送料・代引手数料（重量階段・県別加算表・送料無料閾値・10 円切上げ・上限） | `Dict`・`foldl`・`Int53.div` |
| 2 | ドキュメント権限（4 ロール × 5 アクション × 公開範囲 × ロック × 個別付与、拒否理由つき） | 入れ子 `match`・`Dict`・和型 |
| 3 | 失効するポイント（ロット単位・期限昇順で FIFO 消費・部分消費・掃除） | `Arr.sortByKey`・`foldl`・epoch ms |
| 4 | 注文のライフサイクル（7 状態 × 6 イベント・時刻の逆行拒否・14 日以内の返金） | フィールド付き `inductive` |
| 5 | 国内振込指示の検査（桁数・全数字・全エラー収集・`1234-567-8901234`・`1,234.56`） | `Str.*` 全般 |

## 結果（実測）

**5 本すべてが `lake build` → emit → Node 呼び出しまで到達した。** 落ちたシナリオはない。

| # | `lake build` 回数 | 公開関数 | 定理 | ベクタ |
| --- | --- | --- | --- | --- |
| 1 送料 | 2（失敗 1） | 7 | 4 | 2773 |
| 2 権限 | 4 | 8 | 5 | 3550 |
| 3 ポイント | 2 | 6 | 6 | 2665 |
| 4 注文 | 4（失敗 2） | 4 | 6 | 1767 |
| 5 振込 | 10 | 9 | 6 | 3100 |

（5 本とも各自のサンドボックスで再ビルドして検証した数字。自己申告と一致する。）

**サブセットの外に出た拒否は、34 本の公開関数を通して 1 件だけ。** `match state, event with` が
`matches on more than one value, which this walk does not read` で断られたもので、しかも「これは書けるのか」を
確かめるために捨て駒の宣言を 1 本書いて出させたもの。**業務ロジックを書く言語としてのサブセットは、
5 題のどれにも足りていた。**

止めていたのは全部その外側にある。記録された詰まり 13 件のうち **7 件が証明側**、残りが
「文書に書かれていない規則」と「生成物の質」。ソースを読みたくなった瞬間は 3 件。

**5 人が誰も踏まなかった P0 が 1 本ある。** 5 番の報告「通貨の桁数から `10^n` が作れない」を
検算した副産物で、これは 5 人の観測ではなくこちらの追試で出たもの ——
`Str.repeat` と `Str.padStart` に**呼び出し側の値**を長さとして渡すと、`lake build` は通り、
`lake exe lean2js` が素の `Stack overflow detected. Aborting.`（exit 134）で落ちる。
`lean2js` としての診断は一言も出ず、どの宣言が原因かも出ない。下のフェーズ 1。

## Approach

**広げるべきは構文ではなく、証明の足場と生成物。** 今回の摩擦は、書けない形があったからではなく、
書けた形について**何を証明の材料に使えるかが分からない**ことと、**文書にない規則をビルドを落として
発見する**ことから来ている。

直す順は「クラッシュ → 証明が止まる → 文書に無い規則 → 生成物」。先のものほど後のものの内容を決める:
`Str.repeat` の扱いが決まらないと SYNTAX.md にその節が書けず、prelude の等式を出せば
PROVING.md に書ける形が増え、形が増えればテンプレの定理が変わり、そこまで固まってから
生成物の署名を触る。逆順にやると同じ文を 2 度書く。

この順序には 1 つ根拠がある。**文書の穴が、出荷する実装そのものを歪めた実例が出た** —— 5 番は
`destinationDisplay` を `Str.join` で書いたが、その証明が内部名 `joinStr` → `joinFrom` に 1 層ずつ剥がれ、
引ける等式がどこにもないので 3 ビルド使った末に**出荷する関数のほうを `++` に書き直した**。
証明できない語彙は、使われない語彙になる。

## フェーズ 1 — コンパイラのクラッシュ（P0）

**長さを呼び出し側から取る `Str.repeat` / `Str.padStart` が、emit を abort させる。** 再現は 1 宣言:

```lean
@[ship]
def rightAlign (s : String) (width : Int) : String := Str.padStart s width " "
```

`lake build` は通る。`lake exe lean2js MyLogic --out dist` が

```
Stack overflow detected. Aborting.
```

だけを出して exit 134 で落ちる。`--out` に何も残らないのは正しいが、**利用者に届く情報がゼロ** ——
宣言の名前も、どの操作が原因かも、`Str.repeat` が長さを値として受けることも出ない。
長さを `min (max n 0) 15` のように縛れば同じ形が通り、ベクタも一致する。原因は
ベクタ生成が長さに大きな値を選び、Lean 側の評価がそこで落ちること。

SYNTAX.md はこれを予告してはいる ——「`Str.repeat` と `Str.padStart` は長さを数として取る 2 つで、
`Int53` の境界を超える文字列を要求できる。それは trap し、エンジンはその手前でメモリを使い切る」——
が、書いてあるのは**生成したコードを動かしたときの話**で、`lean2js` 自身が落ちる話ではない。

**入った直し:** 長さは**プログラムの本文が縛る**ことにして、縛られていない `Str.repeat` を
`Core.Program.checked` が宣言名で断る（`Lean2Js/Bound.lean`）。`ship_package` が同じ関数を呼ぶので、
断りは `lake exe lean2js` ではなく `lake build` に出る。

```
error: MyLogic.lean:6:0: rightAlign repeats a string as many times as a value says, and nothing in
the program bounds that value. Clamp the count -- `min (max n 0) 64` -- so the bound is in the text.
(`Str.padStart` repeats its pad up to the width, so a width a caller chooses is the same thing.)
```

上限 `maxRepeat = 4096` は測って決めた。`Str.repeat` は 1 つずつ連結するので差分テストは長さの 2 乗で
効く —— 公開関数 1 本・リテラル長で emit まで **4096 で 7 秒、16384 で 17 秒、65536 で 198 秒**、
262144 は 20 分でも返らなかった。`min`/`max`・四則・`cond`/`match` の枝・`let` を辿って上界を読むので、
`min (max n 0) 15` は通り、`let width := min (max n 0) 64` も通る。入れ子は掛け算で効く
（`Str.repeat (Str.repeat s 4096) 4096` は断る）。`Example.lean` の `Str.repeat mark 32` と
`Str.padStart (Int53.toString amount) 12 " "` はそのまま通る。

## フェーズ 2 — 証明の足場（P0）

**prelude の語彙に、引ける等式を出す。** 実測で詰まったのは `Str.join` ——
`simp [Str.join]` が内部の `joinStr` に落ち、それを足すと今度は `joinFrom` に落ちる。
`Prelude.lean` に `joinStr` は `def` としてあるだけで、**その名前で引ける等式はどこにも無い**。
`Arr.isEmpty` は具体ゴール `Arr.isEmpty [] = true` を残して `simp` が止まり、`decide` が要った。
`@[expand]` で書かれた語彙はすべて同じ形をしているので、同じことが起きる範囲は
（実測したのはこの 2 つだが）語彙表の大半に及ぶ。文書に「こう書け」と足すのではなく、
`@[simp]` の等式（リテラルの場合と cons の場合）を付ける。

**PROVING.md に、実測で出た 5 つの形を足す:**

- `decide` と `rfl` の使い分け。具体的な `Except`／構造体の等式には `Decidable` インスタンスが
  降ってこない（`deriving DecidableEq` を部品に付けていても）。4 番と 5 番が独立に踏んだ。
  今の「形 1」は `Int` の等式しか見せていない。
- `simp [f, h]` に `f` とその `f` についての仮説 `h` を同時に渡すと閉じない。`f` が先に展開されて
  `h` が当たらなくなる。**しかも simp のヒントが誤った側（`h`）を「unused」と名指す。**
  2 番は 4 定理まとめてこれを踏んだ。正しい直しは `f` を simp セットから外すこと。
- 数値リテラルの綴りが違うと黙って閉じない。`14 * 24 * 60 * 60 * 1000` と `1209600000` は、
  simp がゴール側では計算するのに、書き換え規則として渡した仮説の中では計算しない。
- 仮説は `def` が検査しているのと同じ綴りで書く。`Str.trim s = ""` ではなく
  `Str.length (Str.trim s) = 0`。
- Lean 本体の `List` 補題に `simp` が届く範囲。「Mathlib は無い」しか書いていないので、
  **何があるか**が分からない。3 番は `filter` の二重適用が `simp` 一発で閉じることを、
  閉じてから知った。

**`#eval` が自前の型で通るようにする。** PROVING.md は「仮説が満たせるかを `#eval` で確かめろ」と
言っているのに、自前の `structure` / `Except` を `#eval` すると
`Unable to synthesize MonadEval instance` で落ちる。`deriving Repr` が要るが、テンプレの
`deriving` 句にも PROVING.md にもその語は無い。**文書が勧めた手段がそのままでは動かない**ので、
テンプレの `deriving` に足すか、PROVING.md に 1 行足すかのどちらかで閉じる。

**公開前に見る点を 3 つ目に増やす。** 今の 2 点（仮説は満たせるか／docstring は署名どおりか）に、
**「主張が定義の言い換えになっていないか」**を足す。5 番の
`destination_display_joins_with_two_hyphens` は、名前が業務の主張を言っているのに、中身は
`destinationDisplay a b c = a ++ "-" ++ b ++ "-" ++ c` という定義の展開で、コード自体にハイフンが
入る場合を排除していないので「ハイフンがちょうど 2 本」は証明していない。docstring は正直に
「順に連結する」と書いてあるので `/proof-audit` の既存項目には掛からない。**名前だけが強い**という形。

**入った直し:** `Prelude.lean` に空・`cons` の `@[simp]` 等式を付けた —— `Arr.length` / `isEmpty` /
`contains` / `sum` / `count` / `head?` / `last?` / `flatten` / `flatMap`、`Str.length` / `isEmpty` /
`join` / `repeat` / `padStart`、`Opt` と `Exc` の全構成子。`sum` と `count` と `flatten` と `flatMap` は
`foldl` の蓄積子を前に出す補題を経由する。`Example.lean` の `reference_from_three_parts` が
`Str.join` の等式を実際に引いて出荷する（5 番が諦めたのと同じ形）。

PROVING.md は書き直した。追加でこちらの追試で出たものが 2 件ある:

- **`decide` は自前の `structure` / `Except` の等式に届かない** ——「`Decidable` が降ってこない」は
  実測どおりで、テンプレ上で `failed to synthesize Decidable` を再現した。同じ命題が `rfl` では通る。
- **`simp` の既定集合に `String` の補題は入っていない。** `(a ++ b) ++ c = a ++ (b ++ c)` は
  `String.append_assoc` を名指す必要があり、`Example.lean` の新しい定理がそれを踏んだ。
  Lean 本体の `List` 補題は入っている、という 3 番の観測と対になる。

`simp [f, h]` の件は**条件付き**だった。壊れるのは `h` が `f` の呼び出し自体についてのとき
（`h : totalOf amounts = 500` に `simp [totalOf, h]`）で、ヒントは実際に `h` を unused と名指し
`simp [totalOf]` を勧める。`h` が `f` の本体の中のものについてのとき（`h : prices.get sku = none`）は
逆に `f` を展開しないと当たらない。テンプレのサンドボックスで両方を再現して書き分けた。

`#eval` は `deriving Enc, Repr` で通る。テンプレの 4 つの型すべてに `Repr` を足した。

## フェーズ 3 — 文書に無い規則（P1）

いずれも「ビルドを落として 1 つずつ発見する」以外に知る道がないもの。

- **JavaScript の予約語で識別子が断られること。** 利用者向け文書 4 本を `reserved` で grep して
  ヒット 0 件。実際のリスト（`Lean2Js/Ident.lean` の `jsReserved`）には業務ドメインの語が並ぶ ——
  `delete` `default` `new` `case` `class` `enum` `in` `for` `import` `export` `package` `private`
  `public` `static` `interface` `this` `throw` `try` `catch` `String` `Number` `Object` `Error`
  `Math` `Symbol` `eval`。2 番は `Action.delete` で落ちた。**断り文言自体は的確**（語とルールを名指す）
  なので、要るのは SYNTAX.md の宣言節に 1 文とリストへの参照だけ。
- **`match` は 1 つしか見られないこと。** 状態機械で最初に書きたくなる `match state, event with` が
  書けない。拒否文言は的確。SYNTAX.md はこの軸に一言も触れていない。
- **`@[expand]` の 0 引数 `def`（名前付き定数）が書けること。** 例が全部 1 引数以上なので、
  4 番は試して確かめた。マジックナンバーに名前を付けるのは業務ロジックで常時出る。
- **`Dict.ofList` と `Dict.ofPairs` の食い違い。** SYNTAX.md の本文例は `Dict.ofList [("daily", 10)]`、
  「これが語彙の全部」であるはずの `Dict V` の表には `Dict.ofPairs` しか無い。両者は別物
  （`ofList : List (String × α) → Dict α` / `ofPairs : List α → (α → String) → Dict α`）。
  **1 番と 2 番が独立に踏んだ。**
- **語彙表に型を書く。** 表は名前だけを並べているので、`Dict.getD` の引数順も
  `Arr.isEmpty : List α → Bool` も推測になる。1 番は 3 件を「運で当てた」と自己申告している。
- **`Arr.sortByKey` の複合キー。** 安定性は書いてあるが、「副キーで先にソートしてから主キーで
  ソートすれば複合キーになる」ことは書いていない。業務ロジックでは常時出る形（3 番が自力で到達）。
- **定理の中では `/` が書ける**こと（`@[ship] def` の中では `Int53.div` 必須）。この非対称は説明がない。

**入った直し:** 7 件すべて SYNTAX.md に入れた。書く前にサンドボックスで全部当てている ——
予約語は宣言・パラメータ・フィールド・構成子の 4 か所で断られ、文言は
`compile failed: constructor name is reserved in JavaScript: delete` / `... parameter name ... new`。
`match s, e with` は `matches on more than one value, which this walk does not read`。0 引数の
`@[expand] def refundWindowMs : Int := 1209600000` は通る。定理の中の `/` も通る。語彙表には
`Arr` / `Str` / `Dict` / `Int53` / `BigInt` / `Opt` / `Exc` の全項目の型を別表として足した。
複合キー（`Arr.sortByKey` を副キー → 主キーの順に 2 回）と `powTen` は emit して Node で確かめた
（`0 → 1`、`15 → 1000000000000000`、`-3 → 1`、`["east1","east9","west2"]`）。

## フェーズ 4 — 生成物（P1）

- **`@throws` を到達可能な trap だけにする。** いま全 export に一字一句同じ行が付く ——
  加算と乗算しかない `orderSubtotal` にも、`Dict` 参照だけの `regionalSurcharge` にも
  `divByZero` と `indexOutOfBounds` が並ぶ。**1 番と 4 番が独立に指摘。** fuel を構文から数えて
  いるのと同じ歩きで、本体が到達する trap を絞れる。消費者が `try/catch` を書く判断材料として、
  いまの定型文は何も言っていない。
- **公開境界に出ない型を `.d.ts` に出さない。** 3 番の `RedeemAccum` は `foldl` の蓄積用で、
  どの公開関数の署名にも現れないのに `export type RedeemAccum = …` として出る。
  `deriving Enc` した型が全部印字されている。
- **定理が名指す `@[expand]` 定数を、パッケージから引けるようにする。** 4 番の生成 `README.md`
  （npm が表示するページ）には

  ```lean
  theorem refund_past_window_is_refused (…)
    (hwindow : instant - deliveredAt > refundWindowMs) : …
  ```

  が載るが、`refundWindowMs` の値はパッケージのどこにも無い（`1209600000` は `index.js` に
  インライン展開された 2 箇所だけで、`README.md` / `proof-manifest.json` / `index.d.ts` には 0 件）。
  **出荷する主張の署名が未定義記号を含む。** 公開定理が名指す消えた定数を manifest に
  載せるか、載せられないなら断る。どちらにせよ黙って出すのはやめる。
- **毎ビルド出る `String.get?` の deprecation 警告を消す。** `Lean2Js/SourceMap.lean:19` 由来で、
  `lake build` と `lake exe lean2js` の両方が毎回印字する。初回利用者は毎回「自分のコードの警告か」を
  読み分ける。

**入った直し:**

- `@[throws]` の行は `Lean2Js/Traps.lean` が本体から読む。各演算が `eval` の自分のケースが返しうる
  コードを、呼び出しは呼び先のものを、関数として渡された宣言は渡す側の呼び出しで自分のものを出す
  （関数型パラメータ経由の呼び出しが何も足さないのはこの不変条件による）。`noMatchingAlternative` は
  `Exhaustive` が届かないことを証明しているので入らない。**証明ではないので emit が全ベクタで
  照合する** —— 行が名指さないコードで trap するベクタが 1 件でもあればビルドが落ちる。
  例では 107 本中 62 本が `typeError` だけになった（内訳: 62 / 23 が `+int53Overflow` /
  11 が `+divByZero` / 9 が `+indexOutOfBounds` / 2 が `typeError`+`indexOutOfBounds`）。
- `.d.ts` は公開署名から辿れる型だけを印字する。辿るのは引数と戻り値の型、およびそこから届いた型の
  フィールドの型。`Example.lean` には届かない型が無いので生成物に差分は出ず、`Tests.lean` の
  `#guard` 4 本が証拠になっている。
- 定理が名指す 0 引数の `@[expand]` 定数は manifest と README に値ごと載る
  （`Example.lean` の `maxLineQuantity : Int = 999`、`lineTotal` が使う上限）。`Int` / `String` /
  `Bool` 以外は断る —— これが「載せられないなら断る」の側。
- `String.get?` の警告は `base64.toList.getD` にして消した。`lake build` と `lake exe lean2js` の
  両方から出なくなっている。

## 表現力の天井は、無かった

5 番は「サブセットに冪乗が無いので通貨の桁数から `10^n` が作れない」と報告し、上限の検査を
「0 桁と 2 桁だけ手で並べる」に縮めた。**これは誤りで、サブセットの中で書ける:**

```lean
@[ship]
def powTen (n : Int) : Int :=
  Opt.getD (Str.toInt? ("1" ++ Str.repeat "0" (min (max n 0) 15))) 0
```

追試して emit まで通り、Node 上で `0 → 1` から `15 → 1000000000000000` まで正しく答える。
**サブセットを広げる必要は、5 題を通して 1 件も出なかった。** 代わりに要るのは SYNTAX.md の
*Operations that are not there* に 1 行（冪乗は `Str.repeat` と `Str.toInt?` で作る、長さは縛る）と、
その `min`/`max` がフェーズ 1 のクラッシュ回避でもあることの明示。

## 再走の結果（2026-09-19、フェーズ 1〜4 を入れたあと）

同じ 5 題を同じ条件で走らせ直した。ジャーナルの `kind:` を機械的に数え、ベースラインも同じ数え方で
数え直したもの:

| kind | 前 | 後 |
| --- | --- | --- |
| proof-stuck | 7 | **4** |
| surprise | 11 | 7 |
| wanted-source | 3 | 2 |
| lean-error | 2 | 1 |
| doc-wrong | 1 | 2 |

5 本とも `lake build` → emit → Node 呼び出しに到達（公開関数 7 / 4 / 5 / 4 / 9、定理はすべて 5 本）。
**サブセットの外に出た拒否は今回 0 件。**

`doc-wrong` の 2 件はどちらも 5 番のもので、**文書の誤りはうち 1 件**（下の `Str.split s ""`）。
もう 1 件は `rfl` が閉じないのを文書のせいと読んだ記録だが、閉じなかったのは同じ `Str.split` の
読み違いで**命題そのものが偽だった**からで、文書の欠陥ではない。以下 4 件のうち残りは
`doc-wrong` ではなく各セッションの Top 5 から拾ったもの。実測して直した:

- **定義を `simp` に名指すと、その定義についての規則がすべて本体に置き換わる。** `simp` 単独で閉じる
  `Str.join [a, b] "-" = a ++ "-" ++ b` が `simp [Str.join]` では `joinStr` を残して止まる。
  `simp [f, h]` の件と同じ仕組みで、PROVING.md はこれを 1 つの規則の 3 つの顔として書き直した。
- **`Str.isEmpty (Str.trim s)` の仮説は `Str.isEmpty` も名指さないと当たらない。** 仮説の綴りだけ
  書いていた。`simp [labelOf, h]` は `h` を unused と報告して止まり、`simp [labelOf, Str.isEmpty, h]`
  で閉じる。
- **`Str.split s ""` は `[s]`。** SYNTAX.md の書き方は逆に読める節が 1 つあるだけで、5 番は逆に読んで
  **黙って誤った検査を出荷し**、9 ビルド中 4 を溶かした。直接書くのと、「長さの分からない文字列は
  1 文字ずつ歩けない」を併せて書いた。
- `if` を 2 段重ねた `split <;> omega` の例が無い（2 番と 4 番が独立に要求）。足した。

**このセッションでは直していない新規の指摘が 2 件ある:**

- **`ship_package` の証明書合成が閉じないとき、`Denote.Denotes` / `firstMatch ?m.1377 ...` の生ゴールが
  出る。** SYNTAX.md が `reify` の拒否について約束している「名指しで断る」形になっておらず、2 番は
  原因（`≥` か / `@[expand]` の二重呼び出しか / 入れ子か）を切り分けられないまま該当関数を捨てた。
  この処理系で一番読めない出力。
- **`Str.*` の答えから `String.toList` / `Char` の事実に降りる補題が無い。** 「ハイフンがちょうど 2 本」
  のような文字を数える主張は、任意の文字列については届かない。PROVING.md には境界として 1 文書いたが、
  補題を足してはいない。

## 完了の条件

- フェーズ 1〜4 が全部入っている。
- `scripts/dogfood/` で同じ 5 題を同じ条件で走らせ直して、**証明側の詰まりが 7 件から減っている**こと
  （ビルド回数の中央値でなく、詰まりの件数で見る —— ビルド回数は題の難しさに引きずられる）。
- `Str.padStart s width " "` を `@[ship]` して emit したとき、abort ではなく宣言を名指す断りが返ること。
- ゲートは全部: `pnpm lean:build` / `lean:emit` / `typecheck` / `test` / `lint` / `package:check` /
  `template:check` / `git diff --exit-code -- packages/verified-example`。
- フェーズ 2 で prelude に等式を足したら、`Example.lean` の定理がそれを使う形に 1 本は寄せる
  （足した等式が実際に引けることを、出荷する例が示す）。
