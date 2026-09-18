# 採用を止めているものを全部取り除く

2026-09-18 に、公開リポジトリの main を外から使う形で調べた結果（実測）と、それを潰すまでの計画。
調査の生ログは `scratchpad/blockers.md`（セッション外）。ここには残す判断と、やることだけを書く。

## いま分かっていること

動くほうは動いている。テンプレを cold start して `lake build` 64s → emit 28s（`.lake` 273MB）、
README の Quickstart スニペットは逐語で通り、印字される `942 vectors` も一致し、生成物を Node から
import した結果は README の出力例とバイト一致する。**止めているのは証明ではなく、梱包と文書と 1 本のバグ。**

見つかったもの（すべて再現済み）:

1. **束縛するコンストラクタパターンの後ろに `_` を置くと、証明が閉じずにコンパイラ内部を吐く。**
   `match d.get k with | .some v => v | _ => 0` が `unsolved goals` で落ち、行番号は `ship_package` を指し、
   **どの `def` が悪いか出ない**。`| .none => 0` と書けば通り、`| .free => … | _ => …`（束縛しない腕＋`_`）も通る。
   `if let` も同じ（desugar 先が同じ形）。原因は `Reify.casesOn` が、条件を倒すための `cases` を
   **`typeDef` を持つ型（= `deriving Enc` した利用者の型）にしか出していない**こと。`Option` / `Except` は
   サブセット組み込みで `typeDef` を持たないので `cases y0` が出ず、`c0 : ∀ v, ¬y0 = some v` が使われないまま残る。
2. **前方参照が偽の 2 次エラーを連れてくる。** `Unknown identifier` の後に
   `reify: a binder here has no name, and the generated code needs one` が続く。
3. **SYNTAX.md が 2 箇所で実物と違う。**「書く順序は問わない」（Lean が前方参照を許さない）、
   「`xs.map double` は書けない」（`seats.map bumpOne` は通る）。
4. **`structure` の `Name ::` を省くと、黙って `tag: "mk"` が消費者の型に出る。**
5. **`Prod` の断り**が「`deriving Enc` を付けろ」と言うが、`Prod` には付けられない（実行不能な直し方）。
6. **生成物が消費者向けになっていない。** npm ページの Exports が Lean 表記、`@[ship] def` の docstring が
   `.d.ts` にも README にも届かない、throw する事実とコードの記載ゼロ、install / import 例なし、JSDoc ゼロ。
7. **定理ゼロのパッケージが「証明済み」の体裁で出る。** 生成 README に「Proved in Lean …」と
   「The proofs above reach no axioms beyond …」が残り、manifest は `"theorems": []` ＋ axioms 3 本。
8. **`--out` が既存ファイルを掃除しない。** パッケージ名を変えると古い `<name>.lean2js` が残る。
9. **英語 README の先が全部日本語。** SYNTAX.md（サブセットの唯一のリファレンス）、テンプレ README、
   `docs/guarantees.md`。README は英語で配っているのに、断り文言の一覧も保証の文章も読めない。
10. **証明側が無文書。** Mathlib が無い（`norm_num` は `unknown tactic`）、`Int53.div` の中身、`Dict` の扱い、
    どのタクティクが使えるかがどこにも書かれていない。README の「普通の Lean の証明でいい」は実態と違う。
11. **出荷の最後の 1 マイルが英語側に無い。** `isPrivate := false` / `license` / `repository`（`Manifest` に実在）は
    日本語テンプレ README だけ。`npm publish` も、`dist` を自分のアプリに入れる手順も無い。
12. **固定先が無い。** tag も release も無く、テンプレは `rev = "main"`。GitHub の description は空、topics 無し。

## Approach

**1 本のバグ → 生成物 → 文書 → 運営の順に、外側へ向かって直す。** 先に直すものほど、後のものの内容を決める:
バグを直せば SYNTAX.md に書く規則が変わり、生成物を直せばテンプレ README と README の記述が変わり、
文書が固まってはじめてタグを切る意味がある。逆順にやると同じ文を 2 度書く。

4 つのフェーズに切り、**各フェーズの終わりにゲートを全部ローカルで通してから main にプッシュする**
（この repo は main 直プッシュ、PR 無し）。フェーズをまたぐ状態は持たない ——
どのフェーズの終わりでも、リポジトリは配れる状態になっている。

方針として決めたこと（実装の前に確認を取らない）:

- **言語の線を引き直す。** 利用者に届く文書（`templates/**/*.md`、`docs/guarantees.md`、`docs/index.md`）は
  **英語**にする。日本語のまま残すのは開発の内部文書（`docs/*-plan.md`）と `CLAUDE.md` だけ。
  README が英語で世界に配っている以上、その先が読めないのは保証を配っていないのと同じ。
  `CLAUDE.md` の言語節も同じコミットで直す（これは 2026-09-07 の決定の変更で、ユーザーの「全部やる」が承認）。
- **`tag: "mk"` は黙って出荷しない。** `deriving Enc` の時点で、コンストラクタ名が `mk`（= `Name ::` を
  書かなかった）構造体を断り、文言で `Name ::` を教える。消費者の型に出る名前は成果物の一部で、
  書き手が意図していない名前が出るほうが、断られるより高くつく。
- **定理ゼロは「証明済み」に見せない。** 定理が 1 本も無ければ、生成 README は Theorems / Axioms 節を出さず、
  「このパッケージは定理を載せていない」と書く。manifest の `axioms` も空にする。
- **サブセットは広げない。** バグは「書けると書いてある形が通らない」ことであって、書けない形を増やす話ではない。
  `Prod` も `Nat` も断ったままで、断り文言だけを実行可能なものにする。

各フェーズで触るのは以下。`packages/verified-example/` は生成物なので、フェーズ 1・2 では
`pnpm lean:emit` の結果を同じコミットに入れる。

## フェーズ 1 — コンパイラのバグ（P0）

**Lean2Js/Reify.lean**
- 分割は 1 段では足りない（入れ子パターンでは、分割して初めて現れた値をもう一度分割する必要がある）ので、
  `casesOn` の「腕の束縛子を 1 つ選んで `cases`」をやめ、**ゴールに現れるサブセット型のローカルを
  再帰的に分割する戦術** `lean2js_split_tested` を置き、生成する証明をそれに差し替える。
- 前方参照の 2 次エラー: elaboration が既に失敗している（`sorryAx` / `Expr` にエラーが混じっている）ときは、
  `reify:` を投げずに黙る。`Unknown identifier` だけが残るようにする。

**Lean2Js/Example.lean**（＋ `Lean2Js/Axioms.lean`）
- `Option` と `Except` を束縛する腕＋ワイルドカードで受ける `@[ship] def` を足し、その定理を書く。
  公開定理を足したら `Axioms.lean` に `#print axioms` の行も足す（不変条件）。
- `deriving Enc` が `mk` を断ることの `#guard` / テストを足す（フェーズ 2 の変更と同じ場所なので、
  順序はどちらでもよいが、コミットは分ける）。

**ゲート**: 全部。`git diff --exit-code -- packages/verified-example` まで。

## フェーズ 2 — 出荷物を消費者のものにする（P1）

**Lean2Js/Dts.lean / Render.lean / Emit.lean / Manifest.lean**（実装時に確定）
- `@[ship] def` の docstring を `.d.ts` の JSDoc と生成 README の Exports に載せる。
  docstring は Lean の側で読めているので、落としているのは出力側だけ。
- 生成 README の Exports を **TypeScript の綴り**にする（`readonly number[]` /
  `ReadonlyMap<string, number>` / `Result<Money, string>`）。Lean の綴りは `.lean2js` と manifest が持っている。
- 生成 README に **throw する事実**の節を出す: `typeError` / `int53Overflow` / `divByZero` と、
  それぞれがいつ出るか。`.d.ts` 側は JSDoc の `@throws` 1 行。
- 生成 README に **install と import の例**を出す。`repository` が manifest にあればリンクも。
- **定理ゼロのとき**は Theorems / Axioms 節を出さず、載せていないことを 1 行書く。manifest の `axioms` も空。
- `--out` は書く前に**自分が書くファイル群の古い版を掃除する**（`<name>.lean2js` の名前が変わる経路）。
  ディレクトリごと消すことはしない（利用者が置いたものを消さない）。

**Lean2Js/Reify.lean / EncDeriving.lean**
- `Prod` の断り文言を実行可能なものに直す（「タプルはサブセットに無い。`structure` を作る」）。
- `deriving Enc` が、コンストラクタ名が `mk` の構造体を断る（`Name ::` を教える文言つき）。

**ゲート**: 全部 ＋ 生成物の再 emit。`package:check` / `template:check` がここの主役。

## フェーズ 3 — 文書（P2）

**templates/verified-package/SYNTAX.md** — 英語化し、同時に:
- 「書く順序は問わない」を「Lean の通常どおり、使う前に書く。`ship_package` が並べ替えるのは出力の順序」に直す。
- 「`xs.map double` は書けない」を実物に合わせる（名前で渡せる／その場のラムダも書ける位置はどこか）。
- 束縛する腕＋ワイルドカードが**書ける**ことを（フェーズ 1 の後は事実）パターンの節に明示する。
- `Name ::` が要る理由（消費者の型に出るタグ名）を 1 行書く。
- 証明側の節を新設（Mathlib 無し、使えるタクティク、`Int53.div` は `Int.tdiv`、`Dict` をどう開くか）。
  ここは新規ファイル `templates/verified-package/PROVING.md` に切り出してもよい（実装時に決める）。

**templates/verified-package/README.md** — 英語化。publish の手順（`isPrivate := false` / `license` /
`repository`）と、`dist` を自分のアプリに入れる手順を書く。

**docs/guarantees.md**、**docs/index.md** — 英語化（内容は変えない）。

**README.md**
- 冒頭で**誰が Lean を書くのか**を 1 文で言う（書き手と消費者は別の人でよい）。
- publish と consume の節（`isPrivate` / `license` / `repository` / `npm publish` / workspace への入れ方）。
- 実測値（初回 `lake build` / emit / `.lake` サイズ）と、定理ゼロでも emit できる速い道。
- 証明側の前提（Mathlib 無し）を Writing theorems に 1 行。
- Lean を知らない読者向けの入り口リンク。

**CLAUDE.md** — 言語節を上の線引きに直す。

**ゲート**: 全部（文書だけでも `template:check` は動かす。テンプレの md はコピーされる）。

## フェーズ 4 — 固定先と見つかりかた（P3）

- `CHANGELOG.md` を置く（0.1.0 の中身は「最初の公開」で足りる）。
- `v0.1.0` のタグを切ってプッシュする。`templates/verified-package/lakefile.toml` の `rev` をそのタグにする。
  テンプレ README の「rev を固定しろ」が指せる先ができる。
- GitHub の description と topics を `gh` で設定する（`lean4`, `formal-verification`, `typescript`,
  `compiler`, `npm`）。
- `lakefile.toml` / `Manifest.compilerVersion` / タグの 3 つがずれないこと（`template:check` が既に見ている）。

**ゲート**: 全部 ＋ タグを切った後にテンプレを cold start して、タグ固定で `lake build` と emit が通ること。

## 完了の条件

- 上の 12 個が全部消えている。
- `pnpm lean:build` / `lean:emit` / `typecheck` / `test` / `lint` / `package:check` / `template:check` /
  `git diff --exit-code -- packages/verified-example` が緑。
- 外から（このリポジトリを知らない状態で）テンプレをタグ固定でコピーして、
  英語の文書だけで `dist` を作り、`npm publish --dry-run` まで行ける。

## 結果（2026-09-18 に完了）

4 フェーズすべて main にプッシュ済み。タグ `v0.1.0` と GitHub リリースも公開した。

- `f46e522` — 束縛する腕＋ワイルドカードを読めるようにし（`lean2js_split_tested`）、前方参照の
  2 次エラーを止めた。`Example.lean` に `Option` / `Except` の同型を追加（ベクタ 25075 → 25511、
  公開関数 68 → 70、宣言 69 → 71、fuel 489 → 503）
- `bf415a4` — 生成物を消費者のものにした（docstring → `.d.ts` の JSDoc と README、TS 表記の署名、
  throw する `code` の節、import 例、定理ゼロのときの文言、`--out` の後始末、`mk` タグの拒否、
  タプル・`Nat`・`Float` の実行可能な断り）
- `eb0312b` — 利用者に届く文書を英語へ（`SYNTAX.md` は誤り 2 箇所も修正、`PROVING.md` を新設、
  `guarantees.md` / `index.md` / テンプレ README / README、`CLAUDE.md` の言語節）
- `3df1d5a` — `CHANGELOG.md`、テンプレの `rev` をタグへ、`v0.1.0` タグとリリース、
  GitHub の description と topics

受け入れ確認: タグ固定のテンプレをコピーして `lake build` 1m07s → emit（2733 ベクタ一致・9 exports）
→ `npm publish --dry-run` が 7 ファイル・6.9kB で通る。
