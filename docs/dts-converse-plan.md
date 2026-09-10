# `.d.ts` の逆向きを閉じる

`docs/closing-the-chain-plan.md` が保証の鎖を閉じたあとに残った、**利用者が実際に踏む**唯一の穴を
塞ぐための計画。

## 文脈

`entry_check_fits_dts` は「入口検査を通った引数は `.d.ts` の型を満たす」を言っている。逆は成り立たず、
それは利用者から見ると**型どおりに書いた呼び出しが `typeError` になる**という形で現れる。出荷物で
実測した 2 つ:

| 呼び出し | いま | 原因 |
| --- | --- | --- |
| `addMoney({ currency: "JPY", amount: 1, tag: "Money" }, …)` | `typeError` | 入口検査がフィールドを**位置**で見る。TS のオブジェクト型はキーの順序を縛らない |
| `addMoney({ tag: "Money", amount: 1e300, currency: "JPY" }, …)` | `typeError` | `Int53` / `UInt32` はどちらも `number` に写るので、TS は範囲を言えない |

範囲のほうは TypeScript の型で表現できないので消せない。**並びのほうは消せる。** 検査が位置で見て
いるのは、`eval` 側の `Value.obj` が順序付きの連想リストで、`checkTy_sound` が
「検査を通った JS 値は `encodeValue v` **そのもの**である」という形をしているから。

読んで確かめた地形:

- 入口検査は生成コードでは `__ck(x, t)` の 1 行に閉じている（`Helper.lean` の `ck`）。
  実体は `__has` → `__hasFields` で、位置を見ているのは `__hasFields` の
  `keys[i + 1] !== f[0]` だけ
- `__eq` はオブジェクトを**キー名**で比較する（`Object.hasOwn` + `a[key]`）。並びを緩めても等値は
  壊れない。位置を見ているのは辞書（`Map`）の側だけで、そちらは宣言された鍵の集合が無いので
  そもそも正規順という概念が無い
- 生成された本体はフィールドを名前で読む（`(a).currency`）。並びに依存しているのは入口検査と
  `encodeValue` の像だけ

## ゴール

このマイルストーンの終わりに立っている場所。

- **`.d.ts` が公開している型を満たす値は、数値が `Int53` / `UInt32` の範囲に収まっているかぎり、
  入口検査を通る。** 但し書きはこの 1 つだけ
- その逆（`entry_check_fits_dts`）も引き続き成り立つ。両方向が manifest に載る
- README の「`.d.ts` の型が通ることは、入口検査を通ることを意味しない」の段落が、
  範囲についての 1 文に縮む

## 非目標

これまでの判断を引き継ぐもの（Promise / async、クロージャ、公開境界に関数を出すこと、`sortBy`、
Float、JS 全体の字句・構文、TypeScript の型検査器のモデル化、Node / V8 の正しさ）に加えて、
このマイルストーンで新たに外すもの。

| 外すもの | 理由 |
| --- | --- |
| `Int53` / `UInt32` の範囲を `.d.ts` に載せること | ブランド型にすれば書けるが、利用者は `number` を渡せなくなり、境界の使い勝手を型の厳密さと引き換えにすることになる。範囲は仮定として明示する側に倒す |
| 辞書（`Map`）の鍵の並び | 宣言された鍵の集合が無いので正規順が定義できない。`eval` と生成コードは同じ並びを見ており、ずれていない |
| `-0` の正規化 | `__ck` の why-not のまま。構造の正規化は数値に触れない |

## Approach

原則が三つあり、Step の刻み方はこの三つから出る。

**検査を緩めるのではなく、通ったものを正規順に組み直す。** 検査を名前引きにするだけでは
`checkTy_sound` の「検査を通った JS 値は `encodeValue v` そのもの」が偽になり、その 1 本に
`Decl.lean` と `Correct.lean` の全体がぶら下がっている。代わりに入口で**正規化**を挟み、
主張を「検査を通った JS 値は、正規化すると `encodeValue v` になる」に置き換える。下流が受け取る値は
これまでどおり `encodeValue v` そのものなので、`Correct.lean` は文面を変えずに済む。

**受け入れる集合を変えないコミットを先に置く。** 正規化を先に入れて `__ck` に繋ぐところまでを、
検査が位置を見たままで済ませる。そのとき正規化は恒等なので、新しい主張は古い主張から出る。
下流の形を全部動かし終えてから、検査だけを緩める。緩める側のコミットは `Decl.lean` の中で閉じる。

**逆向きは仮定を 1 つに絞って述べる。** 「`.d.ts` の型を満たす」から「入口検査を通る」を導くのに
本当に要るのは数値の範囲だけにする —— 並びは正規化が吸収し、余分なキーは正規化が落とす。
仮定が 2 つ以上残るなら、それは設計がまだ穴を残しているということ。

## Step 1. 正規化を模型に足す — 完了

`JsSem.lean` に `normTy` / `normList` / `normEntries` / `normFields`。記述子に沿ってオブジェクトを
`tag` 先頭・宣言順に組み直し、配列・辞書・`option` / `result` / `ctors` の中身へ再帰する。フィールドは
名前で引くので、`hasV` と同じく `sizeOf` の補題を渡して停止性を通す。

`descOk` / `namesOk` / `fieldsOk` / `altsOk` は `HelperProof.lean` から `JsSem.lean` へ移した。
「フィールド名が相異なり、どれも `tag` でない」は模型の側の条件で、`__has` の証明だけのものではない。

`Norm.lean`（新規）の `normTy_of_checkTy` —— **検査を通った値の上で正規化は恒等**。検査がフィールドを
位置で見ているうちは、通った値はもう正規順だから。Step 2 が下流を動かすのに使う。

**生成コードには何も足さない。** プレリュードは使われるものだけに絞られず全部出るので、配線前の
`__norm` を足すと出荷物にデッドコードが載る。ソース側の `__norm` は Step 3 で検査を緩めるのと同時に。

## Step 2. 下流を正規化を通した形に移す — 完了

模型の `Js.Expr.check` が `.ok (normTy v d)` を返すようになった。`normTy` が恒等なので、**受け入れる
集合も出荷物も 1 バイトも変わらない**。

`Decl.eval_check` は文面を変えず、`Js.descOk d = true` を取るようになった。そこから出た宿題が 2 つ:

- `descOk_tyDesc` —— コンパイラが書き出した記述子は `descOk` を満たす。`Compile.tyDesc.induct` に
  沿った帰納で、`tyDescFields` の側は「名前の並びが元のフィールド名の並びと同じ」を運ぶ
- `typesNamesOk_of_compileProgram` —— その前提は `compileProgram` が成功したことから出る
  （`validateType` が全型について「フィールド名は相異なり `tag` でない」を見ている）

`HelperProof.calls_ck_checkTy` も同じ形に置き換えた。出荷される `__ck` は引数をそのまま返すが、
検査が位置で見ているうちはそれが正規化した値そのものである、と言っている。

## Step 3. 検査を名前引きにし、生成コードに正規化を入れる

ここで初めて受け入れる集合が広がり、出荷物が変わる。**模型とソースは同時に動かす**（`has_checkTy` が
両者を縛っているので、片方だけでは `lake build` が落ちる）。

1. `JsSem.checkFields` を名前引きに。位置の一致と本数の一致をやめ、
   「宣言された各フィールドがその名前で在り、型が合う」だけにする
2. `checkTy` のオブジェクトの節を `.obj (("tag", .str ctor) :: rest)` から `tag` を名前で引く形に。
   `tag` が先頭でなくても通る
3. `Helper.lean` に `__norm` / `__normFields`、`__ck` を
   `__has(x, t) ? __norm(x, t) : __fail("typeError")` に。`__hasFields` は `Object.hasOwn` で
   名前を引く形に。`HelperSem` の builtin の表に `Object.fromEntries` を 1 行足す
   （オブジェクトを動的な鍵で組み立てる手段が helper の言語に無い）
4. `HelperProof` に `__norm` の模型と、ソースがそれを計算することの証明。`hasFieldsAt_check` を
   張り直す。`calls_ck_checkTy` を新しい `__ck` について証明し直す
5. `Decl.checkTy_sound` を
   `checkTy jv d = true → ∃ v, normTy jv d = encodeValue v ∧ hasTy p v ty = true` として本当に証明する

**余分なキーを落とすのは意図した選択。** TypeScript のオブジェクト型は、変数を経由して渡す値に
余分なプロパティが載っていることを許す（禁じるのはその場のオブジェクトリテラルだけ）。落とさずに
弾くと、逆向きの主張に「余分なキーが無いこと」という 2 つ目の仮定が付く。落としても生成コードは
そのキーを読まないし、`__eq` はオブジェクトを名前で比べるので、観測できる違いは受理か `typeError` かだけ。

## Step 4. 逆向きを述べて manifest に載せる

1. `Dts.lean` に `tsSat_checkTy`:
   `TsSat p ty jv → InRange jv d → Js.checkTy jv d = true`。
   `InRange` は「`.num` が `Int53` / `UInt32` の記述子に当たる位置で、その範囲に収まっている」だけを
   言う述語。これ以外の仮定を置かない
2. `Example.lean` に利用者向けの形で書き、`Claim` を 1 本足す（16 → 17 本）
3. `Axioms.lean` に `#print axioms` の行を足す
4. `Dts.lean` の冒頭の「The converse fails」を書き直す

## Step 5. 実地で確かめて、文書を合わせる

1. `Vectors.lean` に、フィールドを並べ替えた引数と余分なキーを持つ引数の出荷ベクタを足す。
   `checkAgreement` が `eval` と JS の模型の一致を見る
2. `packages/lean-ts/` に、生成された ESM を Node で実際に呼ぶ差分テストを足す。
   計画の冒頭の表の 1 行目が通り、2 行目が変わらず `typeError` であることを実測する
3. README の「保証の組み立て」の `.d.ts` の項と、その下の「`.d.ts` の型が通ることは…」の段落を
   書き直す。`docs/mvp-plan.md` の到達点も
4. ベクタ件数・`Helper.defs` の本数・`HelperSem` の表の行数・`Claim` の本数を、
   引用しているすべての場所で直す

## 順序と依存

Step 1 → 2 → 3 は一本道で、順番を入れ替えられない。Step 2 が受け入れる集合を変えないまま下流を
動かし終えていることが、Step 3 で `Correct.lean` を動かさずに済む条件になっている。
Step 4 は Step 3 のあと。Step 5 は Step 3 のあとならいつでもよいが、README を 2 回書き直さないために
最後に置く。

## 守ること

- **保証を弱めて緑にしない。** 逆向きが重いときに `InRange` 以外の仮定を足して通さない。
  仮定が増えるなら、それは Step 3 の正規化がまだ足りていない
- **`sorry` で塞がない**（塞げば `Axioms.lean` が落ちる）
- **実行時検査が落ちたときにベクタを減らさない**
- **`packages/verified-example/` は生成物。** 手で直さない
- **manifest に定理を足したら `Axioms.lean` に行も足す**
- **数字は測ったものだけ書く**
