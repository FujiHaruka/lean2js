# 操作の拡張計画

`docs/business-logic-plan.md` が広げた部分集合に、JS の業務ロジックで頻出するのに今は書けない操作を
足すための計画。**進捗は末尾の「結果」にある。**

## 文脈

今の到達点は測った数字で言える。公開関数 96 本、manifest の定理 27 本、出荷前に照合する差分ベクタ
35125 件、`Core.Expr` は 35 形。実行時ヘルパは 53 本で、模型がヘルパについて仮定している表 38 行の
全行が印字器の書き出すソースと一致する（`helpers_ship_as_modelled`）。JS の組み込みへの依存は
`Helper.lean` が名指ししている `prim` 12 種とメソッド 13 種で、それが読み取れる TCB の全部。

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

## Step 2. 層 0 の語彙（完了）

**書けるようになったこと**: 意味論を 1 行も動かさずに、下の 19 操作。全部 `@[expand] def` なので、
生成物に名前は残らない。

| 受け手 | 足したもの | 既存の形での書き方 |
| --- | --- | --- |
| `List T` | `Arr.take` `Arr.drop` | `slice` |
| | `Arr.isEmpty` `Arr.contains` `Arr.sum` `Arr.count` | `length` / `any` / `foldl` |
| | `Arr.head?` `Arr.last?` | `cond` + `index` |
| | `Arr.flatten` `Arr.flatMap` | `foldl`（`++` で畳む） |
| `Dict V` | `Dict.getD` `Dict.ofPairs`（計算キー） | `get` / `foldl` + `set` |
| `Option` | `Opt.getD` `Opt.map` | `match` |
| `Except` | `Exc.getD` `Exc.map` `Exc.mapError` `Exc.toOption` | `match` |
| `String` | `Str.isEmpty` | `length` |

**`Opt` / `Exc` が `Option` / `Except` でないのは名前が取られているから。** `Option.getD` と
`Except.map` は import 済みで `TagAttribute` を付けられず、同名を足すと `open Lean2Js` の下で
曖昧になる。

**関数を取るものには宣言の名前しか渡せない。** `Arr.count` / `Arr.flatMap` / `Dict.ofPairs` /
`Opt.map` / `Exc.map` / `Exc.mapError` にその場のラムダを渡すと、展開した先でラムダが呼ばれる形になり
`reify:` が印を付けた `def` の名前で断る。既存の「ラムダは走査の引数にだけ」という規則の帰結。

**`zip` は入れない。** 2 本の配列から組の配列を作る形だが、`Ty` に組が無い。自分の `structure` を
宣言すれば書けるので、型を 1 つ足すほどの値打ちが無い。

**触った場所**: `Prelude.lean`（語彙 19 本）、`Example.lean`（語彙ごとに公開宣言 1 本と、関数を
渡すための `amountWithTax` / `currencyOf` の 2 本）、`SYNTAX.md`。`Reify.lean` は Step 1 の機構が
効くので動かなかった。

### 入らなかったもの（2026-09-18 に測った）

**当初の表のうち 6 つは今の `Reify` では書けない。**

- `indexOf?` — 組を畳み込む形が要るが、`Ty` に組が無く `Prod.mk` は断られる。`structure` を
  `Prelude` に宣言しても、`shippedTypes` は利用者の名前空間しか集めないのでプログラムの `types` に入らない。**外す。**
- `min?` `max?` `groupBy` `Dict.map` `Dict.filter` — どれも**走査の関数の中の `match`** を要求する。
  `Dict.map` / `Dict.filter` は入ったとしても生成コードが O(n²) になる（`keys` を回して `get` を
  引くので、`Map` の `get` が O(1) でも走査が n 回入る）。件数が小さい業務ロジック向けと割り切るか、
  層 1 の走査として足すかは、実際に困ってから決める。

**走査の関数の中に `match` を書くと、walk は読むが証明書が型が合わない。** `reify:` の拒否ではなく
`ship_package` での Type mismatch になる。`Example.lean` にはこの形が 1 つも無く、踏んだのは初めて。

- 原因の見当: `Reify.matched` が splitter の major premise を `_` で渡す。最上位では期待型が
  具体なので `denotes_var` の `rfl` が `env.lookup?` を計算して埋めるが、`denotes_reduceE` の
  `(fun _ _ => …)` の下では埋まらない。
- **試して落ちた手 2 つ**（同じことをやらないこと）。① motive から fuel / env を外に括り出す ——
  env が束縛変数になり `lookup?` が計算できなくなって悪化する。② major premise を `matchedFn` と同じ
  自由変数の抽象で渡す —— 孔が埋まらず同じところで落ちる。
- **回避策は測ってある**: `match` を自分の `@[ship] def` に出し、ラムダからそれを呼ぶと通る。
  **`@[expand]` では通らない** —— 展開が `match` をラムダの中へ戻すから。つまりこの 5 つは
  「公開関数を 1 本余分に出す」形でなら今でも書けるが、層 0 の語彙としては出せない。

**だから入れたのは残りだけ。** `Opt.*` / `Exc.*` が通るのは `match` が `def` の直下にあるからで、
呼ぶ側も `@[ship] def` の直下に置くかぎり通る —— 走査のラムダの中で呼ぶと、展開が `match` を
ラムダに戻すので同じ壁に当たる（`SYNTAX.md` に 1 行足した）。`?` で終わる名前は `@[ship]` だと
`validateIdent` で落ちるが、`@[expand]` はコンパイラに届かないので `Arr.head?` と書ける。

**保証の境界**: 変わらない。`Core.Expr` は 35 形のまま。公開関数が 70 本から 91 本に増えたので、
`decl_correct` / `decl_traps` / `decl_refuses` が覆う側だけが厚くなった。

## Step 3. 数値 ⇄ 文字列

**書けるようになること**: `Int53.toString` と `Str.toInt?`。金額・ID・キーの組み立てが Lean 側に残る。

**`String(n)` は Int53 の範囲で 10 進表記と一致する。** JS が指数表記に落ちるのは |n| ≥ 1e21 で、
Int53 の上限 2^53-1 ≈ 9.007e15 はその下。だから「対応が一意」という基準を満たす。

**`Number()` は使わない。** 空文字列を 0 にし、`0x` を読み、前後の空白を飛ばす。受け付ける文字列は
**`Int53.toString` が印字するものちょうど**——読んだ値を印字し直して元の文字列と一致しなければ `none`
を返す。これは当初書いた `-?[0-9]+`（先頭ゼロなし）より狭い: `"-0"` は正規表現に合うが印字器が書かない
ので落ちる。`toInt?` が `Option` を返すので trap は無い。

### どこに置くか（2026-09-18 に測った）

**両方とも演算子で足せる。`Core.Expr` は 35 形のまま。**

- `toString` は `UnOp` に足す。`Compile` の `un` は `.un .not` / `.un .neg` / `.un .abs` と
  **op ごとに腕が分かれている**ので、`.un .toString`（`.int53 → .string`）は腕が 1 つ増えるだけで、
  既存の腕の型付けは動かない。
- `toInt?` は `StrUnOp` に足す。`strUn` の `Compile` は今 `.ok (…, .string)` と**結果型を固定**して
  いるので、`strBinResult : StrBinOp → Ty` と同じ形の `strUnResult : StrUnOp → Ty` に開く。
  **これは新しい手ではなく `strBin` の既存の形をなぞるだけ。**
- `Sound` の `TypeChecked` は `strUn {op : StrUnOp}` と op に依らないので**動かない**。`Sound` の
  `strUn` の場合は `applyStrUn_hasTy` に委ねているので、仕事はその補題の中。`strBin` が
  `applyStrBin_hasTy` で既に op 依存の結果型をやっている。

### ヘルパ（2026-09-18 に測った）

**`String` は `prim` に無い。** 今の `prim` 11 種は `Array.from` / `Array.isArray` / `BigInt` /
`Math.imul` / `Math.trunc` / `Number.isInteger` / `Number.isSafeInteger` / `Number` /
`Object.fromEntries` / `Object.hasOwn` / `Object.keys`。`toString` は `prim "String"` を 12 種目に
足すか `method … "toString"` にするかで、どちらも名指しの TCB が 1 増える。

**`toInt?` は手書きで書き切れる。** ヘルパ言語に `forOf` / `letMut` / `setVar` があり、`__upper` が
既に 1 文字ずつ回している。形は「先頭の `-` を `startsWith` で見て `slice` で落とす → 残りを 1 文字ずつ
`v = v * 10n + BigInt(__cp(c) - 48)` で畳む → `v` が 0 と Int53 上限の間にあることを BigInt のまま見る →
`Number(...)` → `String(n) !== s` なら `none`」。**`BigInt(s)` は使わない** —— 文字列を渡すと形が
違うときに投げるうえ、模型に「JS の BigInt が文字列をどう読むか」の行が要る。桁を自分で畳めば
`BigInt` に渡すのは数値だけになり、`prim` は増えない。
**形の検査は最後の印字し直しが全部やる。** 桁でない文字は畳み込みで別の値になり、印字し直すと元の
文字列と合わない。だから桁かどうかを別に確かめる腕は要らない。

**触る場所**: 層 1 の一式（`strUn` を触っているのは 16 ファイル）。`Helper` に 2 本
（`__str` と `__toInt`）。**`toString` を先に 1 つ入れて全ゲートを通し、`toInt?` は別コミット。**

**16 ファイルのうち op を名指ししているのは 11 だけ**（残りは `.strUn _ x` で op に依らない）。
`toInt?` を `StrUnOp` に足すとき手が要るのは:

| ファイル | 何を足すか |
| --- | --- |
| `Core.lean` | `StrUnOp` に `toInt`（`?` は付けない。付くのは `Prelude` の `Str.toInt?` の側）、`StrUnOp.name` に 1 行 |
| `Eval.lean` | `applyStrUn` に腕 1 つ（`.str s` → `.opt (.int53 …)`） |
| `Compile.lean` | `strUnHelper` に 1 行、`.strUn op e` の腕の `.string` 固定を `strUnResult` に開く |
| `Builder.lean` | `def toInt? (e : Expr) : Expr := .strUn .toInt? e` |
| `Reify.lean` | `Lean2Js.Str.toInt?` → `strUn` の行（`Str.trim` の隣） |
| `Denotes.lean` | `denotes_toInt`（`denotes_strUn` は結果型が `t` で一般なので通った） |
| `Sound.lean` | `applyStrUn_hasTy` を op 依存に。`TypeChecked` の `strUn` は op に依らないので動かない |
| `Correct.lean` | `strUn` の場合（`InFragment` は op に依らない） |
| `Helper.lean` | `__toInt` |
| `HelperSem` / `HelperProof` / `HelperAgree` | `__toInt` の模型と一致証明 |
| `Renderable.lean` | `okCallee_strUnHelper` が新しい名前でも通ること |

`toString` を `UnOp` に足すほうは `.un` を名指ししているファイルだけで、`Compile` の腕が op ごとに
分かれているぶん `strUn` より軽い。

### ベクタの穴（2026-09-18 に測った）

**`scalarEdges .string` に数字の文字列が 1 つも無い。** 今の 17 件は
`"" "a" "b" "ab" "ba" "abc" "Z" "z" "\"" "\\" "\n" "日本語" "🍣" "🍣a" bmpMax astral astral++"a"` で、
`toInt?` の**成功側がベクタで 1 度も踏まれない**。`"0" "-0" "007" "+5" " 5" "9007199254740991"
"9007199254740992" "-9007199254740991"` を足すのが筋だが、プールは `String` 引数の直積に効くので
**測った**（2026-09-18）: この 8 件だけを足すと 32270 → 33457 件（+1187, +3.7%）。文字列 2 引数の関数は
17² → 25² に広がるが、そこまで持つ関数が少ないので分母は 4% も動かない。**8 件とも足した**（`toInt?` を
使う公開宣言 2 本と合わせて 34291 件）。

**保証の境界**: 変わらない。覆う側が増える。

**同じコミットで直す数字**: `docs/guarantees.md` のヘルパ本数（今 50 本）と模型の表の行数（今 36 行）、
ベクタ件数、`README.md` のサブセットの表、`docs/next-milestone-plan.md` の「言語が凍っている」行
（層 1 は凍結を解く側なので、Step 3 が初めてここに届く）。

## Step 4. 文字列の組み立て

**書けるようになること**: `Str.join` / `Str.replace` / `Str.padStart` / `Str.repeat` /
`Str.indexOf?`。Step 3 と合わせて、金額整形が Lean 側で書き切れる。

**`join` は JS 組み込みへの依存を増やさない。** `Helper.lean` はすでに `join` を名指ししている。

**`replace` の空パターンは JS 固有。** `"abc".replaceAll("", "-")` は各位置に挿入する。意味論を
そこに合わせる価値が無いので、空パターンは拒否する（コンパイル時に落とせるのはリテラルのときだけ
なので、実行時の trap になる）。

**`padStart` / `repeat` はコードポイントで数える。** `Str.length` と同じ基準。ネイティブの
`padStart` は UTF-16 単位で数えるので手書きヘルパに落ちる。

### どこに置くか（2026-09-19 に測った）

**`Str.indexOf?` だけは既存の形の腕で足りる。** 引数は String 2 つで、結果型は `strBinResult` が
既に op 依存なので、**`StrBinOp` に腕を 1 つ足すだけ**。`Str.toInt?` と同じ値段で、`Core.Expr` も
`Compile` の引数検査も動かない。**5 つのうちこれを先にやる。**

**残る 4 つは引数の型が今の形に合わない。**

| 操作 | 引数の型 | 今ある形 |
| --- | --- | --- |
| `join xs sep` | `(List String, String)` | `strBin` は `(String, String)` 固定 |
| `repeat s n` | `(String, Int53)` | 同上 |
| `replace s pat rep` | `(String, String, String)` | `substring` は `(String, Int53, Int53)` 固定 |
| `padStart s n pad` | `(String, Int53, String)` | 同上 |

**`Core.Expr` を 35 形のまま通す道がある。** `strUn` の結果型をこの leg で `strUnResult` に開いたのと
同じ手で、`strBin` の**引数**型を `strBinArgTys : StrBinOp → Ty × Ty` に開き、`substring` を
`strTer (op : StrTerOp) (a b c : Expr)` に一般化する。形は増えず、`decl_correct` の分母も動かない。

**ただし `strUn` のときほど安くはない。** 測ったのはここ:

- `strBin` を名指ししているのは **16 ファイル**、`substring` は **16 ファイル**。`Cost` / `Step` /
  `Fuel` / `Gather` / `Decl` / `StepAgree` は op に依らないので、開くのは `Core` / `Eval` /
  `Compile` / `Render` / `Renderable` / `Builder` / `Reify` / `Denotes` / `Sound` / `Correct`。
- **`Correct` と `Sound` の `strBin` の場合は、今のままでは op 非依存を保てない。** 今は
  `Ty.eq_of_not_bne` で `tl = tr = .string` を出し、`hasTy_string_inv` で両引数を `String` に
  落としてから `helper_strBin` を当てている（`Correct.lean` の `| strBin hl hr` の中）。
  引数型が op 依存になると、この 2 段が op ごとに分かれる。
- **`helper_strBin` の持ち上げは済んでいる**（2026-09-19, `HASH2`）。`applyStrBin op (.str a) (.str b)`
  固定だったものを「両引数が `strBinArgTys op` の型を持つ」仮定つきの `Value` の形に上げ、
  `Compile` の `strBin` は `strBinArgTys op` と突き合わせるようにした。**生成物は 1 バイトも動かない**
  （5 操作とも `(.string, .string)` のまま）。`join` と `repeat` は、この腕に型を 1 行足すだけで入る。

**`strBin` は `indexOf?` で初めて落ちる op を持った**（2026-09-19 に入れて分かった）。位置は
文字列の長さで抑えられるが、その長さに上限が無いので `Str.length` と同じ `int53Overflow` で落ちる。
`applyStrBin_str`（「文字列 2 つなら必ず返る」）はもう成り立たないので消し、`Correct` の
`strBin` の場合は op で分けて、落ちる側は `strBin_err_indexOf` と `eventuallyErr_call2_helper` で
JS 側の同じ失敗に繋いだ。**`repeat` も同じ形を持つ**（長さが伸びる）ので、この分岐はそのまま使える。

**触る場所**: 上の一式 × 4。ここがこの計画でいちばん重い。**1 つずつ入れて、1 つ入るたびに
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
- `docs/guarantees.md` — ベクタ件数（今 35125 件）、実行時ヘルパの本数と仮定の表の行数
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
- **Step 2**（2026-09-18, `4c7ed5f`） — 層 0 の語彙 19 本が `Prelude.lean` に入った。`Arr` に 10、`Dict` に 2、
  新設の `Opt` に 2 と `Exc` に 4、`Str` に 1。全部 `@[expand]` で、`Reify.lean` も `Core` も動いていない。
  `Example.lean` に公開宣言を 21 本足したので、公開関数は 70 → 91 本、差分ベクタは 25511 → 31741 件。
  当初の表の `indexOf?` `min?` `max?` `groupBy` `Dict.map` `Dict.filter` は入っていない（理由は Step 2 に）。
  Step 0 が `SYNTAX.md` に置いた「foldl と Arr.slice で今日書ける 7 行」は、その 7 つが名前を持った
  ぶん表に移し、残したのは `join` の全文だけ。
- **Step 3 の前半**（2026-09-18, `76d2e43`） — `Int53.toString` が入った。`UnOp` に腕 1 つ、`Core.Expr` は
  35 形のまま。触ったのは `Core` / `Eval` / `Compile` / `Render` / `Builder` / `Reify` / `Denotes` /
  `Sound` / `Correct`（返す側と落ちる側で 1 つずつ）/ `Renderable`（`compileExpr` の場合が 1 つ増えるので
  番号が 1 つずれる）/ `Js.helper` の表 / `Helper` / `HelperSem` / `HelperProof` / `HelperAgree`。
  `Cost` / `Step` / `Decl` / `Gather` は op に依らないので動かなかった。
  ヘルパは `__str`（`String(x)` 1 行）で 49 → 50 本、模型の表は 35 → 36 行、`prim` は 11 → 12 種。
  **`String(n)` が 10 進なのは Int53 の範囲だけ**（JS は 1e21 で指数表記に落ちる）なので、
  `HelperSem.prim` は範囲の外で `stuck` にし、`helperArgsOk` に `__str` の行を足した
  （`__i53div` と同じ「模型のほうが慎重」な行で、要求は 3 行 + `__eq` の 1 行）。
  `Example.lean` に `orderReference` を 1 本。公開関数 91 → 92 本、差分ベクタ 31741 → 32270 件。
  `docs/guarantees.md` の燃料の数字は `503` のまま止まっていた（Step 2 の 21 本を数えていない）ので、
  測って `657` に直した。
- **Step 3 の後半**（2026-09-19, `a219e8e`） — `Str.toInt?` が入った。`StrUnOp` に腕 1 つ、`Core.Expr` は
  35 形のまま。`Compile` の `strUn` は結果型を `.string` 固定から `strUnResult` に開いた（`strBin` の
  `strBinResult` と同じ形）ので、`Sound` / `Correct` の `strUn` の場合は op に依らないまま通り、
  仕事は `applyStrUn_hasTy` / `helper_strUn` / `applyStrUn_str` の中だけで済んだ。
  **受け付けるのは `Int53.toString` の像ちょうど**で、読んだ値を印字し直して照合する。これで
  先頭ゼロ・`"+5"`・`" 5"`・`"-0"`・範囲外が 1 つの検査で落ち、JS 側も同じ形に書ける。
  ヘルパは `__toInt` で 50 → 51 本、模型の表は 36 → 37 行。**`prim` は 12 種のままで TCB は増えていない**
  ——`BigInt` / `Number` / `String` も `codePointAt` / `startsWith` / `slice` も既にあるものだけを使う。
  増えたのは `HelperSem.binOp` の 2 行（BigInt の `*` と `+`）で、桁を BigInt で畳むため。
  `Example.lean` に `amountOf` と `amountOr` を 1 本ずつ。公開関数 92 → 94 本、宣言 93 → 95、
  差分ベクタ 32270 → 34291 件（数字の文字列 8 件込み）、燃料は 657 → 671。
  `SYNTAX.md` の「無い操作」から `parseInt` / `Number(s)` の行を消した。
- **Step 4 の 1 つめ**（2026-09-19, `6af6e2a`） — `Str.indexOf?` が入った。`StrBinOp` に腕 1 つ、
  `Core.Expr` は 35 形のまま。`strBinResult` は既に op 依存だったので `Compile` の形は動かず、
  `Sound` / `Correct` の `strBin` の場合の中だけで済んだ——**ただし op 非依存では済まなかった**。
  位置が安全整数を超えると落ちるので、`applyStrBin_str` を消して `strBin_err_indexOf` に置き換え、
  `Correct` の `strBin` を `cases op` で分けた（詳細は Step 4 の本文）。
  ヘルパは `__startsAt`（接尾辞に針が立つか）と `__indexOf` で 51 → 53 本、模型の表は 37 → 38 行。
  **`prim` は 12 種・メソッドは 13 種のままで TCB は増えていない** —— `join` / `slice` / `startsWith`
  はどれも既にあるものだけを使う。**数えるのはコードポイント**なので、ネイティブの `indexOf`
  （UTF-16 単位）ではなく `__chars` の配列を 1 つずつ削って接頭辞を見る。
  `Example.lean` に `separatorAt` と `referencePrefix` を 1 本ずつ。公開関数 94 → 96 本、宣言 95 → 97、
  差分ベクタ 34291 → 35125 件、燃料は 671 → 685。
  leg 4 が気づいた「受け入れ集合が emit のベクタにしか無い」穴は、`Tests.lean` に
  `Str.toInt?` と `Str.indexOf?` の値の `#guard` を置いて塞いだ（`lake build` が見る）。
- **`strBin` の引数型を開いた**（2026-09-19, `HASH2`） — `Compile.strBinArgTys : StrBinOp → Ty × Ty` を
  置き、`helper_strBin` / `strBin_err_indexOf` を `Value` と `hasTy` の仮定の形に上げた。
  `Correct` の `strBin` の 2 箇所（返る側・落ちる側）は `typeSound` から型を取って渡すだけになり、
  `hasTy_string_inv` はどちらも `helper_strBin` の中に移った。**振る舞いは変わらない**：
  ベクタ件数も生成物も 1 バイト動かず、`Core.Expr` は 35 形のまま。**残る仕事は `strTer`
  （`substring` の一般化）だけ**で、これは `replace` / `padStart` が要る。
