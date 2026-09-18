# 普通の Lean を入力に取る frontend 計画

利用者が表層構文ではなく**普通の Lean の `def`** を書き、**普通の Lean の定理**を証明し、
それがそのまま出荷物についての主張になるようにするための計画。**済** —— Step 0 から 5 まで
通っていて、以下は各段で何を決め、何が分かったかの記録。

## 文脈

この計画の前は、利用者が書いていたのは Lean ではなかった。Lean のパーサだけ借りた別の文法
（`decl%` / `type%`）で、`Core.Expr` の 35 形へマクロが展開する。だから定理は利用者の関数について
ではなく、**プログラムを解釈器にかけた結果**について述べることになっていた。

```lean
evalCall program "seatCharge" [.obj "free" [], .int53 seats] = .ok (.int53 0)
```

これが `seatCharge .free seats = 0` になる、というのがこの計画の目的。表現力ではなく**証明の書き味**が
主眼で、対外的な「Lean を JS に変換する」が字義どおりになるのはその副産物。

`docs/mvp-plan.md` の Approach は、この frontend を明示的に後回しにしていた。理由は 2 つ挙がっていた。

1. **`Lean.Expr` を入力に取ると、証明すべき命題そのものが書けない** —— ソース側の意味論が Lean 本体の
   elaborator に委ねられるため
2. `brecOn` / `casesOn` / `OfNat` インスタンスの展開といった、サブセットの本質と無関係なノイズ

**1 は、宣言ごとの証明書という形を取れば当たらない**（検討 2026-09-17）。

```lean
theorem seatCharge_denotes (p : Plan) (s : Int53) :
  evalCall program "seatCharge" [enc p, enc s] = .ok (enc (seatCharge p s))
```

`seatCharge` も `evalCall` も `enc` も普通の Lean の関数なので、この文は Lean の意味論を形式化しなくても
書けるし検査できる。変換器はどの規則を適用したか知っているので、AST と一緒にこの証明項を吐ける。
**証明が通れば AST が正しい。変換器は信頼しなくてよく、trusted base は 1 行も増えない。**

**2 は当たるが、見積りほどではない。** `Lean.Meta.matchMatcherApp?` が入れ子なしの `match` の腕を
そのまま返すので、reifier が `casesOn` / `brecOn` を手で剥がすことにはならない（Step 0 で実測）。
残りは Step 2 で相手にする。

## ゴール

- 利用者が普通の Lean の `def` で業務ロジックを書く
- 定理が利用者の関数についての普通の等式になる
- その定理が、出荷した JavaScript についての主張へ機械的に降りる
- **trusted base が増えない** —— reifier は証明を吐くので信頼しない

## 非目標

| 外すもの | 理由 |
| --- | --- |
| 表現力を広げること | 受け付ける集合は 35 形のまま。再帰も Mathlib も型クラスも依存型も入らない。**狭さは消えない。消えるのは構文だけ**で、「何が書けるか」の説明責任は残る |
| 一度に全プログラムについての変換正当性 | Lean 自身の意味論を Lean で形式化することになる。`docs/mvp-plan.md` の Approach の判断はこの点では生きている |
| trap しないことを自動で証明すること | 「返るなら一致する」は片側。「この入力では落ちない」は別建ての宿題で、この計画には入れない |
| 表層構文との恒久的な併存 | ベクタも docs もテンプレートもエラーメッセージも二重になる。移行が済んだので退役させた |

## Approach

**証明書を吐く reifier にする。** 変換器は信頼しない。`Lean.Expr` から `Core.Expr` を作るとき、同時に
「この Lean 関数はこの AST の解釈と一致する」の証明項を組み立てる。Lean がそれを検査する。
これが `docs/mvp-plan.md` が避けた道に入らずに済む唯一の理由で、設計上ここは動かせない。

**定理は片側（部分正当性）に倒す。**

```
evalCall … = .ok v → v = enc (f args)
```

利用者が普通の `Int` で書くと、溢れで停止する側と停止しない側が食い違うので等式は偽になる。片側に倒すと、
既存の `decl_traps`（落ちるなら同じコードで落ちる）・`decl_refuses`（型を破る引数は本体に入らない）と
合成して、買い手への文言はこうなる。

> **出荷した関数は、列挙されたコードのどれかを投げるか、あなたの Lean 関数が計算した値を返すか、
> どちらかである。**

代案は、利用者に trap する型（`Except` を返す算術）で書かせて両側の等式にすること。採らない ——
算術が monadic になり、定理も monadic になり、**書き味という目的そのものを失う**。

**証明項は reifier が組み立て、タクティクスに任せない。** 形ごとに denotation 補題を置き、reifier は
適用した規則に対応する補題を貼るだけにする。利用者の `def` を `simp` で展開していく方式は取らない ——
テンプレートの README が既に `evalExpr.eq_def` を `simp` に渡すなと警告しているのと同じ壁に当たる。

**Core から先は 1 行も動かさない。** これは新しい前半であって、書き直しではない。

| | 行数 | 出どころ |
| --- | --- | --- |
| Core から先（`Compile` / `Correct` / `Decl` / `Dts` / `Roundtrip` / `Agree` / `Emit` …） | 34,515 | 実測（`wc -l`, 2026-09-17） |
| 置き換え（`Syntax.lean` 513 / `Builder.lean` 117 / `Example.lean` 672） | 1,302 | 実測 |
| 新規 | 4,000〜6,000 | **見積り** |

新規の内訳（すべて**見積り**であって実測ではない）。

| 部品 | 見積り |
| --- | --- |
| 符号化層 —— `Enc` クラス、`Value` の 7 コンストラクタぶんの instance、利用者の型への `deriving` | 700〜1,400 |
| 形ごとの denotation 補題（35 形） | 1,500〜3,000 |
| 証明を吐く reifier（メタプログラム） | 800〜1,500 |
| prelude（`Int53` / `Str` / `Arr` / `Dict`） | 500〜1,000 |

## Step 0. 縦に 1 本通す —— 済

`Lean2Js/Denote.lean`。`add` / `clampQuantity` / `lineTotal` / `roleRank` の 4 本を、符号化も証明書も
手書きで通した。reifier は無い。**合成は閉じる。**

```lean
def add (a b : Int) : Int := a + b
theorem add_comm' (a b : Int) : add a b = add b a := Int.add_comm a b
```

この `add_comm'` は `Core.Expr` も `evalCall` も `Value` も知らない。それが `add_denotes`（証明書）と
`Decl.decl_correct` / `Decl.decl_traps_at_cost` を経由して、出荷した JavaScript についての 1 本の主張に
なる —— 「**列挙されたコードのどれかを投げるか、`add b a` を返すか、どちらかである**」。
降ろす手順は `rw [← add_comm']` 1 行で、宣言の形を一切見ていない。

### 証明書の形（ここで決まった）

**本体について、任意の fuel で述べる。** `evalCall` について述べると、宣言が別の宣言を呼んだときに
呼び先の証明書を引用できない —— 呼び先は残った fuel で走るので、`defaultFuel` での主張が当たらない。
一般化の代償は無い: `.ok` は fuel 切れの形ではないので `Fuel.evalExpr_of_le` が仮定を `defaultFuel` まで
持ち上げ、証明は一般化しなかった場合と同じものになる。`lineTotal` → `clampQuantity` で実測。

**entry check は証明書に出てこない。** 引数が境界の受け付ける値かは `Decl.decl_refuses` の問いで、
呼び出しの一箇所でだけ訊く。証明書どうしを繋ぐときには出てこないので、宣言が深くなっても増えない。

**境界の仮定は符号化が全域かで決まる。** `enc : Int → Value` は entry check が撥ねる値（Int53 の外）を
作れるので `add_ships` は範囲の仮定を持ち、`encRole` は作れないので `roleRank_ships` は持たない。
これは払うべき代価ではなく、`decl_refuses`（境界を破る引数は本体に入らない）を素直に書いたもの。
**`Enc` の `hasTy` が無条件の法則にならない**ことだけが設計への制約で、prelude の `Int53` を
前倒しする理由にはならない。

### matcher

**復元は見積りより軽い。** `Lean.Meta.matchMatcherApp?` が入れ子なしの `match` について
スクルティニー・腕・`altNumParams` をそのまま返す（`roleRank` で実測: `discrs 1, alts 3,
altNumParams [1, 1, 1]`）。reifier が `casesOn` / `brecOn` を手で剥がす必要はない。
残るのは腕と構成子の対応が位置でしか決まらないことで、`match n { 0 => … | _ => … }` のような
リテラル・既定パターンは matcher 側の情報を読む必要がある。

**証明側に matcher は出てこない。** 証明書は利用者の型を構成子ごとに `cases` で割って書くので、
補助 matcher に触らずに済む。Step 2 の難所は reifier の側だけ。

## Step 1. 符号化層と、スカラの断片 —— 済

核は `Lean2Js/Denotes.lean` と `Lean2Js/Reify.lean` —— `Denotes`、形ごとの補題、AST と証明を同じ
walk で出す reifier。`reify_proof% add` が出す証明にタクティクスは 1 つも無い。**証明項は組める。**

符号化層も入っている —— `Lean2Js/Enc.lean` の `Enc` クラスと、`Bool` / `Int` / `UInt32` / `String` /
`Option` / `Except` / `List` の instance。利用者の型は `Lean2Js/EncDeriving.lean` の `deriving Enc` が
受け持ち、`Core.TypeDef`・符号化・復号・entry check を出す。

この段で walk が読む形は 13 —— 変数・`Int53` リテラル・`+` / `-` / `*`・単項 `-`・
`<` / `≤` / `>` / `≥`・`if`・`let`・呼び出し。`lineTotal` の証明書は `clampQuantity` の証明書を
引用して組まれる —— 引用するのは reifier で、手では書いていない。

### 分かったこと

**AST と証明は同じ walk で作る。** 規則を AST に当てたその場で補題を証明に当てるので、変換だけ進んで
証明が付かない状態を構造として作れない。「reifier を信頼しない」の実装はこれで、後から証明を付ける
設計にはしない。

**断りは利用者の `def` までは届き、その中の項までは届かない。** `Lean.Expr` は位置を持たないので、
`findDeclarationRanges?` で `def` の範囲を取って、そこに断りを置いている。**同じファイルにある `def` に
限る** —— 位置は別のモジュールでは意味を持たないので、輸入された `def` については `reify_decl%` を
書いた位置に戻る。frontend は利用者のモジュールの上で走るので、これは最終形では常に当たる側。
`def` の中の `/` を指すには項から構文への対応が別に要り、これは付け足しでは出ない。

**instance が立つのは 9 コンストラクタのうち 7 つで、`Value.fn` には永久に立たない。** `.fn` は宣言を
名指しする値で、Lean の関数値は自分がどの宣言かを知らない —— 高階の引数は reifier が宣言名に落とす話で、
利用者の型の符号化ではない。`.bigint` と `.dict` は立つが、いま `Int` が `Int53` を、
`List (String × α)` が配列を先に取っているので、別の Lean 型が要る。**どちらも prelude（Step 4）の側。**

**`hasTy` の仮定は `accepts` に化けて利用者の定理から消える。** `Enc` は「境界が受け付ける条件」を
`accepts : Program → α → Prop` として持つので、`add_ships` の仮定は `Value.hasTy` の等式ではなく
`Int53` の範囲そのものになった。条件が `True` の型（`Bool` / `String` / …）では仮定ごと消える。
`Role` のように符号化が全域な型では、条件は値ではなく**プログラムがその型を宣言していること**になる。

**呼び先を名指しした証明書は、プログラムも名指しすることになる。** 引用は `p.find? 呼び先 = some d`
を通るので、`p` を全称量化したままでは `rfl` が立たない。`add` / `clampQuantity` の証明書は `p` について
一般だが、`lineTotal` の証明書は `Example.program` についてのものになる。**frontend はまずプログラムを
組み立て、それから証明書を出す** —— 順番はこれで決まった。

**引用は名前の規約で繋ぐ。** reifier は呼び先の定数 `C` に対して `C_certificate` を環境から探し、
無ければ「その呼び出しには `C_certificate` が要る」と断る。引数の埋め方は `f ..` ではなく
**その定理の文に現れる明示引数の数**を数える —— `..` は `Denotes` を展開した先の `∀` まで食う。
最終形では frontend がこの定理を生成するので、規約は妥協ではなく設計。

**`Prop` は `decide P` の形でしか subset に入らない。** 利用者は `if quantity < 1` と書き、`eval` は
`Value.bool` で分岐する。だから条件は命題ではなく `decide P` として運び、`if` の側は利用者が書いた
`Decidable` インスタンスをそのまま担ぐ。比較 1 つにつき `compare` と `decide` を繋ぐ補題が 1 本要る。

**`deriving` が出すのは top-level の宣言で、instance はそれを繋ぐ 1 行。** 証明を instance の
フィールドの中に書くと、構成子ごとの場合分けが `where` の中の戦術になる。`T.toValue` / `T.ofValue` /
`T.accepts` / `T.ofValue_toValue` / `T.toValue_hasTy` を別々に出しておくと、証明は構成子についての
ふつうの等式定義になり、instance は 6 行で済む。

**`accepts` は「プログラムがその型を宣言していること」を match の外に出す。** 中に入れると、変数の
まま（構成子が分かっていないまま）では簡約できず、`hasTy` を使う側がいちいち `cases` することになる。
外に出しておけば `h.left` で常に取れる。

**生成する宣言の名前は `_root_` で書く。** `deriving` ハンドラは利用者の名前空間の中で走るので、
`Colour.typeDef` をそのまま宣言すると `利用者の名前空間.Colour.typeDef` になる。

**`exprToSyntax` は `deriving` では使えない。** コマンドを組み立てた `TermElabM` は `elabCommand` の
前に閉じるので、そこで作った構文は生き残らない。フィールドの型は定数名から構文を書き起こす。

**`/` は形として断る。** Lean の `/` は床で、サブセットの `/` は切り捨て（`Eval.lean` の `applyArith`
がそう書いてある）。利用者には prelude 側の除算を書かせ、素の `/` は reify できないものとして落とす。
`Reify.lean` の `#guard_msgs` がその断りを固定している。

## Step 2. `match` —— 済

reifier は `matchMatcherApp?` で matcher を見つけ、その **splitter** を引いて腕を復元する。splitter は
腕ごとに「パターンの束縛子 → 先の腕が外れた条件 → `motive <パターン>`」という型をしていて、
**パターンは `motive` の引数として `Expr` で読める** —— 構成子もリテラルも `_` も入れ子も同じ形で
出てくるので、形ごとの規則が要らない。`Option` や `Except` のように利用者が宣言していない型の
`match` も同じ道で通る。

証明も splitter を引用する。motive は
`fun y => Denotes _ _ scrut y → Denotes _ _ (matchE scrut alts) (g y)` で、
腕ごとに `denotes_matchE_of` を使い、`firstMatch` が同じ腕を選ぶことを外れた条件から出す。

### 分かったこと

**`match` 全体は `g x` として運ぶ。** 結論に `match` をもう 1 つ書くと、それは利用者が書いた matcher
とは別の補助定義になって単一化しない。`g : T → α` を取って結論を `Denotes … (g x)` にすると利用者が
書いた形にそのまま当たる。**走査する値は変数でなくてよい** —— `dailyLimit` は呼び出しの答えを
`match` するので、scrutinee は `kabstract` で出現ごとに抽象する。

**重なりのない腕は `g <パターン>` が ι で腕の本体に落ちるが、重なる腕は落ちない。**
`Match.getEquationsFor` が返す腕ごとの等式を `simp only` で当てる。外れた条件は仮定として文脈に
あるので、条件付き書き換えの discharger がそのまま拾う。

**外れた条件は `matchPat` と向きが逆。** splitter は `x = 0 → False` を渡すが、`matchPat` は
パターンのリテラルを左に置いて比べるので、`ne_of_missed` で `0 ≠ x` に直してから simp に渡す。

**何も束縛しない腕もパラメタを 1 つ取る。** matcher は空の腕に `Unit` の引数を付けるので、
`altNumParams` は `max 1 フィールド数`。splitter でも同じで、その束縛子はパターンに現れない。

**matcher は定義をまたいで共有される。** `Denote.trackingOf` の matcher は `deriving Enc` が出した
`OrderState.toValue` のもので、splitter の束縛子は `x0` / `x1` と名乗る。**名前は `app.alts[i]` の
ラムダから取る** —— splitter から取ると、他人が付けた名前が生成する JS に出る。

**`_` は macro scope で分かる。** 利用者が `_` と書いた束縛子は macro scope 付きの名前になり、
名前を付けた束縛子は付かない。生成される JS の変数名は利用者が書いたものになる。

**利用者は引数に名前を付けなければならない。** `def roleRank : Role → Int | .guest => 0` の形だと
パラメタ名が `x✝` になり、生成する関数の引数名にならない。reifier はこれを断る。

## Step 3. 走査 —— 済

`List.map` / `filter` / `find?` / `all` / `any` / `foldl` を読む。

### 分かったこと

**要素の補題は walk の一段ではなく、リスト上の帰納。** 走査は本体を要素ごとに、しかも**節点と同じ
fuel で**回す（`evalMapItems` などが `f` をそのまま渡す）。だから形ごとの補題は 1 本では済まず、
`evalXItems` についての帰納補題と、それを使う節点の補題の 2 本になる。

**`all` と `any` は分けて証明する。** 演算子をパラメタに取って `if op == .all then … else …` で
1 本にまとめると、短絡する向きが逆なので場合分けが絡まって `simp` が壊れる。

**`if b then` の条件は `b = true` になる。** 利用者が `Bool` を `if` に置くと Lean は
`decide (b = true)` を作るので、それを `Bool` 本体に戻す補題が 1 本要る。

**λ を eta 展開してはいけない。** すでに λ のものに `etaExpand` を掛けると β 簡約されない適用が
できて walk が読めなくなる。

## Step 4. 文字列・辞書・prelude —— 済

`Lean2Js/Prelude.lean`。`Arr` / `Str` / `Int53` / `Dict` / `BigInt`。walk が読む形は 13 + 6 から
配列 6 形（リテラル・添字・長さ・スライス・反転・連結）・文字列 9 形・辞書 8 形・除算と絶対値・
`BigInt` の算術と比較まで伸びた。

### 分かったこと

**prelude は型ではなく関数から生えた。** 最初の分岐は「`Int` → `Int53`、`String` → `Str` に寄せるのか、
prelude 型を別に足すのか」だったが、**どちらでもない**のが答えだった。`Enc` の instance を動かす理由が
あるのは `Value` のコンストラクタに Lean 型が残っていないときだけで、それは `.bigint` と `.dict` の
2 つしかない（`Int` が `.int53` を、`List (String × α)` が配列を先に取っている）。`Int` と `String` は
instance をそのまま残し、**違うのは関数のほうだけ**なので prelude は関数を持つ。

**文字列で違うのは長さではなく、大小文字と trim と順序。** 計画は「Lean の `String.length` は
呼べない、JS は UTF-16 単位だから」と書いていたが、これは層を取り違えていた —— JS と `eval` の一致は
`Agree` が受け持っていて、証明書の層が言うのは `eval` と利用者の `def` の一致だけ。`eval` の
`.length` は `s.toList.length` で、Lean の `String.length` と同じものを数える。本当にずれるのは
`String.trim`（JS は NBSP・BOM・行区切りも取る）と `String.toUpper`（`ß` → `SS` で長さが変わる）で、
そこだけ `Str.trim` / `Str.upper` が subset の側を名指しする。

**総関数で書けないところが prelude の残り半分。** 配列の添字・スライス・`substring` は範囲外で trap
するので、Lean 側は総関数にせざるを得ない。`Arr.get` は範囲外で `default` を返すが、**証明書が
片側なので、その場合について何も主張しない** —— 溢れた `Int` と同じ形で、片側性がそのまま総関数を
許している。

**型が同じ演算子は、適用された型で lemma を選ぶ。** `+` は `Int` と `BigInt` で別の `Value` に降り、
`<` は `Int` / `String` / `BigInt` で別の順序に降りる。walk は `HAdd.hAdd` の第 1 引数を `whnf` して
lemma を選ぶ。**数値リテラルも同じ** —— `Expr.int?` は型を見ないので `(5 : BigInt)` も拾ってしまう。
リテラルの枝は `inferType` を見てから `.int53` か `.bigint` かを決める。

**`Dict` の entry check はキーの一意性を含む。** `Value.hasTy` の `.dict` は `keysDistinct` を見るので、
`Enc (Dict α)` の `accepts` は「キーが重複しない」かつ「値がそれぞれ受け付けられる」。キーは符号化を
素通りする（`keys_encEntry`）ので、この条件は利用者の辞書についてそのまま述べられる。

## Step 5. 移行 —— 済

パッケージは `@[ship]` を付けた普通の Lean の `def` の名前空間になった。印を付けた時点で宣言が
読み出され、`ship_package` がそれを集めて宣言 1 本につき 1 本の証明書を書く。
**`lean2js` は証明書の無い宣言を出荷しない**ので、AST を手で渡して迂回する道は無い。表層構文
（`decl%` / `type%`）は退役した。

walk が読む形の一覧はこの表。

| 形 | 状態 |
| --- | --- |
| `==` / `!=` | 済。`Enc` の外に `EncBEq`（符号化が等価を保つ）を置き、instance は 1 本 —— `LawfulBEq` があれば `Enc` の往復から出る。利用者の型は `deriving DecidableEq` で届く |
| `&&` / `\|\|` | 済。短絡するので `bin` は通らず、専用の補題 2 本 |
| `min` / `max` | 済（`Int53` と `UInt32`。`BigInt` には `Min` instance が無いので、そもそも walk に届かない） |
| 構成子と射影 | 済。**構成子はプログラムを名指しする** —— `eval` が型を引いてフィールド名を取るので、`findType?` を `rfl` で通すために証明書が `Example.program` についてのものになる。射影は通らない |
| `none` / `some` / `ok` / `error` | 済。型注釈が形に乗るので `encTy` を通す |
| `UInt32` の算術と比較 | 済。ラップするので `Int53` の補題は使えず、`+ - * / %` と `< ≤ > ≥` に別系統を置いた。**`/` と `%` は `UInt32` でだけ演算子そのものを読む** —— 両側とも自然数を割って同じ丸めをするので、prelude の関数が要らない |
| 関数を取る引数 | 済（1 引数のみ）。`.fn` に `Enc` は立たないので `Enc` の外に `DenotesFn`（名前と利用者の関数を結ぶ）を置いた。関数を取る宣言の証明書はそれを仮定に取り、呼ぶ側が callee 自身の証明書から答える |
| リテラル・`_` の腕、入れ子 `match` | 済。matcher の splitter がパターンをそのまま返すので、形ごとの規則は要らない。`Option` / `Except` の `match` も同じ道で通る |
| 型パラメタを取る型 | 済。`deriving Enc` がパラメタを `Ty.var` のまま `TypeDef` に書き、instance は `[Enc T]` を担いで `Ty.named` に渡す |

### ここで分かったこと

**`match` を関数として渡すとき、腕が外の変数を読んでいたら一緒に抽象する。** 対応補題は `match` 全体を
`g x` として取るが、`g` は reifier が `exprToSyntax` で作る。その構文は telescope を抜けたあとで
elaborate されるので、腕が読む外側の変数（`canRefund` の `role`、`ship` の `trackingId`）は
その時点で存在しない。**捕捉している変数ごと抽象して、穴として適用し直す** —— 穴は期待型から埋まる。
`g` を `_` にして推論に任せる手は使えない: `?g ?x =?= ship state trackingId` は引数が 2 つあると
一次近似が `?g := ship state` を選んで型が合わなくなる。

**型パラメタは `Enc` を通らない。** `Enc` はすでに分かっている型に答えるものなので、パラメタを
含むフィールドの型は `Enc.ty` では書けない。`TypeDef` は宣言のときに 1 度だけ書かれるもので、そこでは
パラメタは `Ty.var` のまま —— 使う側が `Ty.subst` で埋める。`deriving Enc` は
`List T` / `Option T` / `Except` / `Dict` / 他の宣言型をたどって `Ty` を組み立て、パラメタを含まない
フィールドはこれまでどおり `Enc.ty` に落とす。

- **`TypeDef.params` の名前は利用者のもの。** `structure Paginated (T : Type)` の `T` がそのまま
  `params := ["T"]` になり、生成する型定義にも出る。
- **生成する宣言はパラメタを担ぐ。** `Paginated.toValue` ほかは `{T : Type} [Enc T]` を取り、
  instance は `ty := .named "Paginated" [Enc.ty (α := T)]`。
- **構成子とパターンは型引数を先に取る。** `Expr.ctor` の `tyArgs` は構成子適用の先頭
  `numParams` 個から来る。パターンでも同じ数だけ落とす。

**関数は値ではなく宣言の名前として渡る。** Lean の関数値はどの宣言なのかを知らないので `Enc` が
立たない。`Enc` の外に `DenotesFn p name f`（`p` が `name` を宣言していて、それを走らせると `f` に
なる）を置き、**関数を取る宣言の証明書はそれを仮定に取る** —— `priced_certificate` は
`ruleName` と `hrule : DenotesFn p ruleName rule` を取り、環境は
`bindParams pricedCore.params [.fn ruleName, toValue amount]` になる。

- **呼ぶ側は callee 自身の証明書から答える。** `memberPrice` は `priced_certificate` を引くとき、
  `DenotesFn` を求めている引数の位置を型から探して `tenPercentOff_certificate` で埋める。
- **関数を取る側は `by assumption` で仮定を引く。** 仮定の名前は利用者のものなので、名前では引けない。
  `Env.lookup?` が `rfl` で解けた時点で `name` が決まるので、探す型は一意。
- **1 引数だけ。** `Ty.fn` は n 項だが `DenotesFn` は 1 項で、`encTy` は矢印の右がまた矢印なら断る。
- 関数がインラインのラムダだったり、呼ばずに返されたりする形は `#guard_msgs` で断りを固定してある。

**`EncBEq` は型ごとに書くものではなかった。** 最初は `deriving Enc` に instance を出させる話に見えたが、
`Enc` はすでに `ofValue_toValue` で符号化が単射だと言っている。足りないのは「両側の `==` が等価を
決めている」ことだけで、それは `LawfulBEq` そのものなので、instance は
`[Enc α] [BEq α] [LawfulBEq α] → EncBEq α` の 1 本になる。代わりに要るのが `Value.beq` の
`beq_refl` / `eq_of_beq`（`Ty` に同じ形がある）で、利用者の型は `deriving DecidableEq` で
`LawfulBEq` に届く —— `deriving BEq` だけでは届かない。

**`match` の道は Step 2 に書いてある。** パターンは splitter が返し、`hs` を motive の中に入れる
ことで腕の中に `Denotes … scrut <パターン>` が立つ。`p` と `env` は穴でよく、最後に `hs` を当てた
時点で決まる。

**宣言と証明書は 2 段に分かれる。** 証明書はプログラムを名指しする（呼び出しが `p.find?` を
`rfl` で通る）ので、プログラムより後にしか書けない。一方プログラムは宣言を集めるので宣言より後。
だから `reify_decl%` は callee の証明書がまだ無くても AST を読み、`reify_proof%` だけが
証明書の不在を断る —— 歩きは同じ 1 本で、捨てるのは証明項の検査だけ。出荷物の側では
`lean2js` が宣言 1 本ごとに証明書を要求するので、**証明書の無い宣言は出荷されない**という
不変条件はそのまま残る。

**走査する値の抽象は discriminant だけ。** `match` を `g x` として運ぶとき、式全体から scrutinee を
出現ごとに抜くと、腕の中で scrutinee を読み直す形や、`let` が scrutinee を読んでいる形が壊れる
（環境の側は元の項のまま、値の側だけ置き換わる）。`MatcherApp` の `discrs` だけ差し替えれば
どちらも通る。

## 順序と依存

```
Step 0（縦に 1 本）                済 —— 手で書いた証明書が形を決めた
  ↓
Step 1（符号化 + スカラ）          済 —— `Lean2Js/Enc.lean` / `EncDeriving.lean` / `Reify.lean`
  ↓
Step 2（match）                    済 —— matcher の splitter を reifier が引く
  ↓
Step 3（走査）                     済 —— `denotes_mapE` ほか
  ↓
Step 4（文字列・辞書・prelude）    済 —— `Lean2Js/Prelude.lean`
  ↓
Step 5（移行・README の文言）    済 —— `@[ship]` / `ship_package`
```

## リスク

| リスク | 何が起きるか | 先に何をするか |
| --- | --- | --- |
| matcher の復元が重い | Step 2 で日程が超過する | **Step 0 で下がった。** `matchMatcherApp?` が入れ子なしの `match` の腕をそのまま返す。残るのは腕と構成子の対応（位置でしか決まらない）と、入れ子 |
| 証明がタクティクス頼みになる | 利用者の `def` の展開で長く脆くなり、宣言が増えるほど悪化する | **Step 1 の spike で下がった。** AST と証明を同じ walk で出す形になっていて、出た証明にタクティクスは無い |
| prelude の外を呼ばれる | 失敗が reify 時になる。**何でも書けてしまうぶん、agent が書く用途では今より悪い**（今はパーサが必ず止める） | エラーメッセージを Step 1 の受け入れ条件に入れる。`Lean.Expr` は位置を持たないので、利用者の構文を指すには decl range が要る —— 付け足しでは出ない |
| 前半が二重化する | ベクタ・docs・テンプレート・エラーメッセージがすべて 2 系統になる | 済 —— Step 5 で表層構文を退役させた |

## 守ること

- **保証を弱めない。** 証明書が付かない宣言は出荷しない。AST を直接渡して迂回する道を作らない
- **`sorry` で塞がない**（塞げば `Axioms.lean` が落ちる）
- **reifier は信頼しない。** 証明が付かない変換は、変換ではない
- **README の文言は Step 5 で直した。** 「普通の Lean の `def` を書く」が字義どおりになったのは
  表層構文が退役した時点で、それより前に直すと誇大になっていた
- 保証の境界が動いたら、`docs/guarantees.md` と `docs/mvp-plan.md` の到達点を同じコミットで直す
- **プッシュ前にゲートを全部ローカルで通す**
