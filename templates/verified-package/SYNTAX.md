# 受け付ける Lean

`@[verified]` を付けた `def` の中に書けるのは、Lean の中の**狭い部分集合**だけ。`Array` や `String` の
API、Lean のラムダ、再帰、`do`、型クラス、依存型はここには入らない。このページがその部分集合の全部。

読めない形に当たると、`declarations%` が**その `def` を名指しして**、止まった項ごと断る。

## 宣言

```lean
open Lean2Js Lean2Js.Core Lean2Js.Enc

/-- 取り扱う通貨と金額。 -/
structure Money where
  Money ::
  amount : Int
  currency : String
  deriving DecidableEq, Enc

inductive Role where
  | guest
  | member
  | admin
  deriving Enc

structure Paginated (T : Type) where
  Paginated ::
  items : List T
  total : Int
  deriving Enc

@[verified]
def orderTotal (unitPrice quantity : Int) : Int := unitPrice * quantity

declarations%

def program : Program := program%

certificates%

#eval program.check
```

- **`@[verified]` を付けた `def` だけが出荷される。** 付けない `def` は補助として使えるが、
  呼び出すと「証明書が無い」と断られる。
- **型は `deriving Enc` が要る。** `Enc` が、その型が `Value` のどこに載るかを書き、
  `TypeDef` をプログラムに出す。`==` を使うなら `deriving DecidableEq, Enc`。
- 引数には名前が要る。`def f : Role → Int | .guest => 0` の形はパラメタ名が付かないので断られる。
- `declarations%` が、それより上の `@[verified] def` から宣言を読み出す。`program%` はそれを集め、
  呼び出しが前へ進む順に並べる（書く順序は問わない）。`certificates%` が、宣言 1 本につき
  「この宣言はこの `def` を計算する」の証明を書く。**証明書の無い宣言は `lean2js` が出荷しない。**
- `#eval program.check` は、`lean2js` がベクタを走らせる前に断る条件を `lake build` の側に置いたもの。

## 型

| Lean | JS / TS に出る形 |
| --- | --- |
| `Bool` | `boolean` |
| `Int` | `number`（±2^53-1 の整数。溢れは trap） |
| `UInt32` | `number`（0..2^32-1） |
| `BigInt` | `bigint` |
| `String` | `string` |
| `Option T` | `{ tag: "none" } \| { tag: "some", value: T }` |
| `Except E A` | `{ tag: "ok", value: A } \| { tag: "error", error: E }` |
| `List T` | `readonly T[]` |
| `Dict V` | `Map`（`.d.ts` では `ReadonlyMap<string, V>`） |
| `deriving Enc` した自分の型 | タグ付きオブジェクト |
| `Int → Int` | 公開できない。関数を取る宣言は内部専用になる |

`Int` はそのまま `Int53` に写る。Lean の `Int` は無限で `Int53` は有限なので、証明書が言うのは
「返るなら一致する」の片側だけ —— 溢れた側は `decl_traps` が受け持つ。

## 式

### リテラル

```lean
123            Int（期待される型が BigInt なら BigInt）
"text"         String
true  false    Bool
```

負のリテラルは書けない（`0 - 1` と書く）。`UInt32` のリテラルは読めないので、引数か別の宣言から
受け取る。

### 演算子

| 演算 | 書ける型 |
| --- | --- |
| `+` `-` `*` | `Int` / `UInt32` / `BigInt` |
| `/` `%` | `UInt32` だけ。`Int` は `Int53.div` / `Int53.mod`、`BigInt` は `BigInt.div` / `BigInt.mod` |
| `-x` | `Int` / `BigInt` |
| `<` `≤` `>` `≥` | `Int` / `UInt32` / `String` / `BigInt` |
| `==` `!=` | `Enc` と `LawfulBEq` のある型（自分の型は `deriving DecidableEq, Enc`） |
| `&&` `\|\|` | `Bool`。JS と同じに短絡する |
| `++` | `String` / `List` |
| `min` `max` | `Int` |

**`/` を `Int` に書くと断られる。** Lean の `/` は床で、サブセットの `/` は切り捨てなので、
同じ記号のまま通すと意味が変わる。`Int53.div` / `Int53.abs` / `Int53.mod` を書く。

ゼロ除算・`Int53` の溢れ・範囲外アクセス（`Arr.get` / `Arr.slice` / `Str.substring`）は trap で、
リファレンス意味論と生成コードが同じコードで落ちる。

### 条件・束縛・分岐

```lean
if quantity < 1 then 0 else quantity

let rate := 100 - percent
Int53.div (amount * rate) 100

match state with
| .draft => "not placed"
| .placed _ => "placed"
| .shipped _ trackingId => trackingId
| .cancelled reason => reason
```

- パターンは `_` / 数値 / 文字列 / `true` / `false` / コンストラクタ / 名前（束縛）。入れ子にできる。
- **`_` と書いた束縛子は生成コードにも出ない。** 名前を付けた束縛子は、その名前がそのまま
  生成される JS の変数名になる。
- 腕は網羅していなければならない（Lean がそれを見る）。網羅なら最後の腕はテストなしで取られる。
- `Option` や `Except` の `match` も同じ道で読める。
- 走査する値は変数でなくてよく（呼び出しの答えでもよい）、腕の中でその値そのものを読み直してもよい。

### 呼び出しと値の組み立て

```lean
clampQuantity quantity 999            宣言の呼び出し
Money.Money amount "JPY"              コンストラクタ
Paginated.Paginated xs n              型パラメタのあるコンストラクタ
some x    (none : Option String)      Option
(.ok x : Except String Money)         Except
[1, 2, 3]                             配列リテラル
Dict.ofList [("daily", 10)]           辞書リテラル（キーは文字列リテラル）
page.total                            フィールド
Arr.length xs                         長さ
Arr.get xs 0                          添字
priced tenPercentOff amount           宣言を関数として渡す
```

- 呼び出せるのは、**同じ名前空間の `@[verified] def` で、証明書が先に書かれているもの**だけ。
  `certificates%` が呼ばれる順に並べるので、書く順序は問わない。
- 関数として渡せるのは**宣言の名前だけ**。その場のラムダは渡せない。

### 配列・文字列・辞書

| 受け手 | 書けるもの |
| --- | --- |
| `Int` / `UInt32` / `BigInt` | `Int53.abs` `BigInt.abs` `min` `max` |
| `String` | `Str.trim` `Str.upper` `Str.lower` `Str.startsWith` `Str.endsWith` `Str.includes` `Str.split` `Str.substring` `Str.length` |
| `List T` | `.map` `.filter` `.find?` `.all` `.any` `.foldl` `Arr.slice` `.reverse` `Arr.length` `Arr.get` `++` |
| `Dict V` | `.get`（`Option V` が返る） `.set` `.has` `.erase` `.keys` `.values` `.size` |

`Arr.length` / `Arr.get` / `Arr.slice` と `Str.*` は prelude のもので、Lean の `List.length` や
`String.length` ではない。範囲外で trap するところを総関数として書くために別に置いてある。

ラムダが書けるのは `.map` / `.filter` / `.find?` / `.all` / `.any` / `.foldl` の引数の位置**だけ**で、
本体からは外側の引数を読める（`states.filter (fun state => canRefund role state)`）。

## 文法の外にある規則

- **呼び出しは循環できない。** Lean 自身が相互再帰の `def` を断るので、循環は書く前に止まる。
  繰り返しは配列の走査（`.map` / `.filter` / `.foldl` …）が受け持つ。
- **関数は値にならない。** 渡せるのは宣言の名前だけで、`program%` は渡される宣言を渡し先の宣言より
  前に並べる。`xs.map double` は書けない —— 走査が取るのはラムダの構文であって値ではない。
- **関数を引数に取る宣言は公開されない。** 公開境界に関数型は出せないので、`.d.ts` にも
  `index.js` の輸出にも現れず、内部からだけ呼ばれる。取れる関数は 1 引数のものだけ。
- **型パラメタは `Type` だけ。** `Paginated (T : Type)` は書けるが、`Type 1` や型クラス制約は入らない。
- **燃料の上限。** 必要な燃料は式の深さと宣言の本数から決まり、10000 を超えるプログラムは書き出せない。
  `#eval program.check` がこれを見る。

## サブセットの外に出たとき

| 書いたもの | 返るもの |
| --- | --- |
| `Int` の `/` | `reify: a / b is outside the subset this walk reads` |
| 証明書の無い宣言の呼び出し | `reify: the call to f needs f_certificate, which is not in scope` |
| `deriving DecidableEq` の無い型の `==` | `reify: comparing two values of type T needs EncBEq T, ...` |
| その場のラムダを関数として渡す | `reify: fun x => x is a function that is not a declaration, ...` |
| 関数をそのまま返す | `reify: rule is a function, and a function reaches the subset only where it is called or handed to a call` |
| `deriving Enc` の無い型 | `reify: T has no Enc instance, so there is no subset type to give it` |
| その他 | `reify: <項> is outside the subset this walk reads` |

**断りは `def` を名指しする。** `Lean.Expr` は位置を持たないので、指せるのは読んだ `def` までで、
その中のどの項で止まったかは文言の中に出る。サブセットのどこにいるか分からなくなったら、
コンパイラの `Lean2Js/Example.lean` が全部の形をひととおり使っている。
