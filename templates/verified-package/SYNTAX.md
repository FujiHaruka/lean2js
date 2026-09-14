# 書ける構文

`decl%` / `type%` の中に書くのは **Lean の式ではない**。Lean のパーサだけ借りた別の文法で、
`lake build` が受け取るのはその文法で書かれたプログラムだけ。Lean の `Array` や `String` の API、
ラムダ、再帰、`do`、型クラスはここには無い。このページがその文法の全部。

## 宣言

```lean
def orderTotal : Decl := decl%
  orderTotal(unitPrice : Int53, quantity : Int53) : Int53 :=
    unitPrice * quantity

def Money : TypeDef := type% Money := Money(amount : Int53, currency : String)

def Role : TypeDef := type% Role := guest | member | admin

def Paginated : TypeDef := type%
  Paginated<T> := Paginated(items : Array<T>, total : Int53)

def program : Program := {
  types := [Money, Role, Paginated]
  decls := [orderTotal]
}

#eval program.check
```

- 左の `def` の名前は Lean のもの。成果物に出るのは `decl%` / `type%` の中の名前。
- 引数と返り値の型は省略できない。引数ゼロの `f() : T := ...` も書ける。
- `decls` は**依存の順**に並べる。宣言は自分より前の宣言しか呼べない（後述）。
- `types` に載せ忘れた型は `unknown type: Name` になる。
- `#eval program.check` は、`leants` がベクタを走らせる前に断る条件を `lake build` の側に置いたもの。

## 型

| 書き方 | JS / TS に出る形 |
| --- | --- |
| `Bool` | `boolean` |
| `Int53` | `number`（±2^53-1 の整数。溢れは trap） |
| `UInt32` | `number`（0..2^32-1） |
| `BigInt` | `bigint` |
| `String` | `string` |
| `Option<T>` | `{ tag: "none" } \| { tag: "some", value: T }` |
| `Result<A, E>` | `{ tag: "ok", value: A } \| { tag: "error", error: E }` |
| `Array<T>` | `readonly T[]` |
| `Dict<V>` | `Map`（`.d.ts` では `ReadonlyMap<string, V>`） |
| `Name` / `Name<T, U>` | 自分で `type%` した型 |
| `(Int53) => Int53` | 公開できない。関数を取る宣言は内部専用になる |

## 式

### リテラル

```
123          Int53
-123         Int53
"text"       String
true false   Bool
u32(7)       UInt32
big(42)      BigInt
```

`u32(...)` と `big(...)` が取るのは数値リテラルだけで、式は渡せない。

### 演算子

強い順。比較は連鎖しない（`a < b < c` は書けない）。

| 優先 | 演算子 |
| --- | --- |
| 90 | `e.field` / `e.method(...)` / `e[i]` |
| 75 | `-e` |
| max | `!e` |
| 70 | `*` `/` `%` |
| 65 | `+` `-` `++`（文字列と配列の連結） |
| 50 | `<` `<=` `>` `>=` `==` `!=` |
| 35 | `&&` |
| 30 | `\|\|` |
| 10 | `if` / `let` / `match` |

`/` は整数の切り捨て除算。ゼロ除算・`Int53` の溢れ・範囲外アクセス（添字・`slice` / `substring`）は
trap で、Lean のリファレンス意味論と生成コードが同じコードで落ちる。

### 条件・束縛・分岐

```
if quantity < 1 then 0 else quantity

let rate : Int53 := 100 - percent; amount * rate / 100

match state {
    draft() => "not placed"
  | placed(orderId) => "placed"
  | shipped(_, trackingId) => trackingId
  | cancelled(reason) => reason
}
```

- `let` は型注釈と `;` が要る。
- `match` は `{ }` で囲み、腕を `|` で区切る。
- パターンは `_` / 数値 / 文字列 / `true` / `false` / `Ctor(...)` / 名前（束縛）。入れ子にできる。
- **引数ゼロのコンストラクタもパターンで `guest()` と書く。** `guest` と書くと、それは変数束縛
  —— つまり catch-all —— になり、後ろの腕が `match alternative N is unreachable` で落ちる。
- 腕は網羅していなければならない。網羅なら最後の腕はテストなしで取られる。

### 呼び出しと値の組み立て

```
clampQuantity(quantity, 999)          宣言の呼び出し
Money::Money(amount, "JPY")           コンストラクタ
Paginated<Int53>::Paginated(xs, n)    型パラメータのあるコンストラクタ
Role::guest()                         引数ゼロのコンストラクタ
some(x)  none<String>                 Option
ok<String>(x)  error<Money>("...")    Result（型引数は反対側の型）
Array<Int53>{1, 2, 3}                 配列リテラル
Dict<Int53>{"daily": 10}              辞書リテラル（キーは文字列リテラル）
page.total                            フィールド
xs.length                             長さ（() は付けない）
xs[0]                                 添字
@tenPercentOff                        宣言への関数参照
```

### メソッド

| 受け手 | 書けるもの |
| --- | --- |
| `Int53` / `UInt32` / `BigInt` | `abs()` `min(x)` `max(x)` |
| `String` | `trim()` `toUpper()` `toLower()` `startsWith(s)` `endsWith(s)` `includes(s)` `split(s)` `substring(lo, hi)` `length` |
| `Array<T>` | `map(fun x => ...)` `filter(fun x => ...)` `find(fun x => ...)` `all(fun x => ...)` `any(fun x => ...)` `reduce(init, fun (acc, x) => ...)` `slice(lo, hi)` `reverse()` `length` `++` |
| `Dict<V>` | `get(k)`（`Option<V>` が返る） `set(k, v)` `has(k)` `delete(k)` `keys()` `values()` |

`length` はフィールドで、`xs.length()` は「そんなメソッドは無い」になる。
`find` は `Option<T>`、`get` は `Option<V>`。`set` / `delete` は新しい `Dict` を返す。

ラムダが書けるのは `map` / `filter` / `find` / `all` / `any` / `reduce` の引数の位置**だけ**で、
本体からは外側の引数を読める（`states.filter(fun state => canRefund(role, state))`）。

## 文法の外にある規則

- **宣言は自分より前の宣言しか呼べない。** 自己再帰も相互再帰も通らない。繰り返しは配列の走査
  （`map` / `filter` / `reduce` …）が受け持つ。
- **関数は値にならない。** 渡せるのは `@name` という宣言への参照だけで、渡し先より前に宣言されて
  いなければならない。`xs.map(@double)` は書けない —— 走査が取るのはラムダの構文であって値ではない。
- **関数を引数に取る宣言は公開されない。** 公開境界に関数型は出せないので、`.d.ts` にも
  `index.js` の輸出にも現れず、内部からだけ呼ばれる。
- **燃料の上限。** 必要な燃料は式の深さと宣言の本数から決まり、10000 を超えるプログラムは書き出せない。
  `#eval program.check` がこれを見る。

## サブセットの外に出たとき

| 書いたもの | 返るもの |
| --- | --- |
| Lean の関数適用（`xs.foldl f 0`）、小数、`do` | パーサの `unexpected token; expected leants_expr` |
| 無いメソッド（`s.padStart(2)`） | `padStart: the subset has no such method` と、受け手ごとの一覧 |
| ラムダを走査の外に書く | `a lambda is only ever the argument of map, filter, ...` |
| 再帰、宣言の順序違い | `#eval program.check` が `a call in this program does not go backwards` |
| 無い関数・無い型・型が合わない | `#eval program.check` が `compile failed: ...` |

パーサのエラー（1 行目）だけは位置しか言わない。サブセットのどこにいるか分からなくなったら、
`lean/LeanTs/Example.lean` が全部の形をひととおり使っている。
