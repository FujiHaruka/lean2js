# 依存して書き出す — 利用者のパッケージ体験

`templates/verified-package` を `cp -R` する導線をやめ、**lakefile に `require` を 1 つ書けば
あとは使える**形にするための計画。

## いまの体験

利用者がやることを順に並べると、こうなる。

1. このリポジトリを clone する（雛形はリポジトリの中にしかない）
2. `cp -R templates/verified-package my-logic`
3. `lakefile.toml` の `name` / `[[lean_lib]]` を自分の名前に書き換える
4. `MyLogic.lean` の例題を消して自分のロジックと定理を書く
5. `manifest` の 4 フィールドを埋める
6. `lake build && lake exe leants MyLogic --out dist`
7. 出た `dist/` を自分の npm ワークスペースに置く

利用者の手元に残る定型ファイルは 3 つ（`lakefile.toml` / `lean-toolchain` / `MyLogic.lean` の
枠組み）で、うち自分のものは `MyLogic.lean` の中身だけ。

## 何が壊れているか

**雛形が配布物ではない。** 入口が「clone してディレクトリをコピー」なので、`require` で始まる
Lean の普通の作法に乗れない。コピーした瞬間に処理系との縁が切れ、処理系が直っても手元は直らない。

**`rev = "main"` を指している。** 利用者のビルドが main の更新で足元から変わる。

**`lean-toolchain` は利用者の仕事ではない。** `lake update` が依存から書ける（下記）。

## Approach

`require` 一つに畳む。動きは 3 つ、そこに保証が 1 つ増える。

**(1) 実行ファイルを汎用にする。** `leants` が利用者のモジュールを**実行時に読む**。
`lake exe` は依存パッケージの実行ファイルを解決し、`LEAN_PATH` に利用者自身のビルド出力を
含めて起動するので、`leants` は `importModules` で利用者の `MyLogic` を読み、
`evalConstCheck Manifest` で `MyLogic.manifest` を取り出せる。**これで `Main.lean` が消える。**
（この節の主張はすべて実機で確認済み。末尾「確かめたこと」を参照。）

**(2) 依存として解決できる形にする。** Lean の作法で `require` できるようにする ——
リポジトリ root の `lakefile.toml`（ソースは `srcDir = "lean"` で今の場所に残す）、版のタグ、
Reservoir の scope/version、`preferReleaseBuild` によるビルド済み配布、そして
**証明を利用者のビルドから外すモジュール分割**。

**(3) 成果物を利用者のものにし、Node での検査を書き出しに入れる。** ソース名とパッケージの公開設定を
利用者のものにし、`leants` が書き出す前に、利用者の成果物に対して差分テストを Node で回す。

**そして (1) が可能にする保証を足す。** 実行時にモジュールを読むということは、`leants` が
`Environment` を持つということで、`collectAxioms` が呼べる。**manifest 定数の公理集合に
`sorryAx` があれば書き出しを拒否する。** `#print axioms` による今の自衛が、そのまま利用者にも届く。
1 回の呼び出しで全 claim を覆う（manifest の値が証明項を含むため）。

### 到達点

利用者が持つファイルは 2 つになる。

```toml
# lakefile.toml
name = "orderLogic"
version = "0.1.0"
defaultTargets = ["OrderLogic"]

[[require]]
name = "LeanTs"
scope = "FujiHaruka"
version = "0.1.0"

[[lean_lib]]
name = "OrderLogic"
```

```lean
-- OrderLogic.lean
import LeanTs
namespace OrderLogic
open LeanTs LeanTs.Core LeanTs.Core.Dsl

def orderTotal : Decl := decl% ...
theorem nothing_charged_below_one ... := by ...

def manifest : Manifest := {
  package := "@acme/order-logic"
  version := "0.1.0"
  program := { decls := [orderTotal] }
  claims := [{ name := "nothing_charged_below_one", statement := "...",
               proof := nothing_charged_below_one }]
}
end OrderLogic
```

```sh
lake update                                        # LeanTs を取り、lean-toolchain を書く
lake exe leants OrderLogic --out packages/order-logic  # Node で全ベクタを当ててから書き出す
```

`lean-toolchain` は書かない（`lake update` が依存から書く）。`Main.lean` は書かない。
`compiler` / `leanToolchain` / `source` は書かない（処理系が入れる）。

## 段階

順序は依存関係で決まっている。1 が 2 と 3 を可能にし、5 は 1〜4 と独立に進められる。

### 1. `leants` が利用者の manifest を読む — 完了

`lean/Main.lean` を汎用ドライバに書き換える。

```
leants <Module> [--manifest <const>] [--out <dir>]
```

- `--manifest` の既定は `<Module>.manifest`、`--out` の既定は `dist`
- `IO.getEnv "LAKE"` が取れたら、読む前に `$LAKE build <Module>` を回す（古い olean から
  黙って書き出すのを防ぐ。`lake exe` は実行ファイルを起動する前にビルドを終えているので、
  入れ子の `lake build` は詰まらない —— 実測で確認済み）
- `importModules` → `evalConstCheck Manifest` → 既存の `emit` に渡す。
  **`emit` の中身は変えない**（検査は今のまま、コンパイル済みコードが値に対して回る）
- `lakefile.toml` の `[[lean_exe]] leants` に `supportInterpreter = true` を足す

このリポジトリ自身の emit は `lake exe leants LeanTs.Example --out packages/verified-example` になる。

**注意**: いまの `Main.lean` は `import LeanTs.Axioms` / `LeanTs.Tests` で `#guard` と公理固定を
`lake build` に載せている。汎用ドライバはこれらを import できない（利用者が引いてしまう）ので、
**検査は別の default target に移す**（段階 5 と同じ話）。ここを落とすと `pnpm lean:build` が
黙って何も検査しなくなる。

### 2. `sorry` を止める — 完了

`leants` が manifest 定数について `collectAxioms` を回し、`propext` / `Classical.choice` /
`Quot.sound` 以外があれば **書き出さずに落ちる**。使った公理は `proof-manifest.json` に載せる
（成果物が何に依っているかを成果物自身が述べる）。

これは保証の境界を動かすので、`README.md` の「保証の組み立て」と `docs/mvp-plan.md` の到達点を
同じコミットで直す。

### 3. `manifest` から手書きを削る — 完了

`Manifest` から `compiler` / `leanToolchain` / `source` が落ちた。`compiler` は
`LeanTs.compilerVersion`、`lean` は `Lean.versionString` と `Lean.githash`、`source` は `leants` が
読んだモジュール名。`compilerVersion` と lakefile の `version` が割れていないことは
`scripts/check-template.sh` が見る。利用者が書くのは `package` / `version` / `program` / `claims`
の 4 つ。

### 4. 生成物を利用者のものにする — 完了

- ソースは `<package の末尾>.leants` に出る。`sourceMapFor` の引数と `package.json` の `files` も
  同じ名前を指す
- `Manifest` が `isPrivate` / `license` / `repository` を持つ。既定は `isPrivate := true`
  （事故で publish されない側に倒してある）
- 生成する `README.md` が 1 枚出る（公開 API・定理・公理）。npm のページに
  「何が証明されているか」が出るのは、この成果物の売り物そのもの

### 5. 依存として解決できるようにする

**root に lakefile を置いた — 完了。** `lakefile.toml` / `lean-toolchain` / `lake-manifest.json` は
root にあり、ソースは `srcDir = "lean"` で `lean/` に残っている。Reservoir が見るのは root の
lakefile。`pnpm lean:*` の `cd lean` は消えた。雛形の `require` から `subDir` も消えた。

**版を切る。** `v0.1.0` のタグを打ち、雛形の `rev = "main"` を捨てる。Reservoir に登録すれば
`scope` + `version` だけで `require` できる（登録前は
`git = "https://github.com/FujiHaruka/lean.ts"` + `rev = "v0.1.0"` で同じことができる）。

**モジュールを分けた — 完了。** `LeanTs.lean` が引くのは `Emit` の閉包 + `Syntax` / `Builder`
（`decl%`）+ `Eval`（定理を書くための `evalCall_eq` / `evalExpr_*` はここにある）だけになった。
`LeanTs/Checks.lean` が残り —— `Correct` / `Sound` / `Exhaustive` / `Roundtrip` / `Renderable` /
`Decl` / `Dts` / `HelperProof` / `HelperAgree` / `HelperSem` / `Norm` / `Example` / `Tests` /
`Axioms` —— を引き、`defaultTargets` に入っているので `pnpm lean:build` は今までと同じものを検査する。

素のソースから下流パッケージを建てて実測すると、建つのは **23 モジュール・56 MB**（52 秒）で、
証明の olean は 1 つも作られない。全部建てると 149 MB なので、**利用者のビルドから 93 MB が消えた。**

**ビルド済みを配る。** `preferReleaseBuild = true` を lakefile に置き、CI（macOS / Linux の
matrix）でタグごとに `lake upload <tag>` する。これで利用者は 55 MB 分すらビルドしない。
Lake は `lake cache` 経由の Reservoir ビルドキャッシュも見るので、そちらが使えるなら合わせる。

### 6. Node での検査を書き出しに入れる — 完了

`leants` は組み立てたパッケージを一時ディレクトリに書き、ベクタと検査スクリプト
（`LeanTs/NodeCheck.lean`）を並べて `node` で走らせる。全件が `eval` と一致したときだけ出力先に書く。
ベクタは出力先に残らず、`node` が起動できなければ書き出さずに落ちる。利用者は npm の道具も vitest も
持たずに、このリポジトリと同じ差分テストを書き出しのたびに受ける。回し忘れる経路が無い。

検査スクリプトは `.mjs` ファイルではなく Lean の文字列として持つ。`include_str` が読むファイルを Lake は
追跡しないので、ファイルにすると直したあとも古いスクリプトが走りうる。

検査スクリプトが素通りしないことは `packages/lean-ts/src/node-check.test.ts` が見る —— 値違い・`-0`・
BigInt・export 欠け・落ちるべきところで返る・エラーコード違い・読み込めないモジュールをそれぞれ失敗と
して報告すること、並べ替えたオブジェクトと余分なキーを実際に渡すことまで固定してある。食い違ったときに
出力先へ何も書かないことは、`scripts/check-template.sh` が全件に食い違う `node` を PATH に置いて確かめる。

### 7.（任意）属性で `decls` と `claims` を集める

`@[leants] def orderTotal : Decl := ...` と `@[claim] theorem ... ` を用意し、
`program.decls` と `claims` を環境から集める。宣言順がそのまま依存順になるので、
手で並べる仕事が消える。`claims` の `statement` は定理の `Prop` を pp したものにできる ——
**手書きの説明文が定理と食い違えなくなる**ので、段階 2 と同じ向きの改善。
`Manifest` は `package` / `version` の 2 フィールドになる。

段階 1〜6 と独立に効くので、後回しでよい。

## 雛形と CI

`templates/verified-package` と `scripts/check-template.sh` は役目が変わる。到達点では利用者が
書くのは `lakefile.toml` と 1 つの `.lean` なので、**コピーする雛形ではなく、README が引用し
CI がビルドする例**にする。

- `examples/quickstart/{lakefile.toml, OrderLogic.lean}` に置く（2 ファイル）
- `scripts/check-template.sh` → `scripts/check-quickstart.sh`。やることは今と同じ
  （空のディレクトリに展開し、`LeanTs` の require を作業ツリーへ向け直し、`lake build` →
  `lake exe leants` → 出たファイルを見る）
- README の「自分のロジックを書く」は `cp -R` ではなく `require` の 3 行になる

## やらないこと

- **lake を包む npm CLI（`npx leants build`）は作らない。** Lean のツールチェーンは利用者が
  持つ必要があり、包んでも隠しきれない。npm 側には何も置かない —— Node での検査も `leants` の中にある
  （段階 6）
- **`lake init` のテンプレートは狙わない。** Lake の組み込みテンプレートは拡張できない
- **利用者のビルドから証明を外すが、証明を消すわけではない。** 外すのは「利用者が再検査する」
  ことだけで、CI は今と同じものを全部通す（段階 5 の `LeanTs/Checks.lean`）

## 確かめたこと（この計画の前提）

実機（Lean 4.33.1 / Lake 5.0.0）で確認済み。

- `lake exe <依存の実行ファイル>` は、利用者側に `[[lean_exe]]` も `Main.lean` も無しに解決して走る
- `lake exe` が渡す `LEAN_PATH` に**利用者自身のビルド出力が入る**ので、依存側の実行ファイルから
  `importModules` で利用者のモジュールを読める
- 依存側の実行ファイルが `importModules` → `evalConstCheck` で、利用者のモジュールにある
  証明項つき構造体（`{prop : Prop} proof : prop` を含む）を取り出せる
- `collectAxioms` を manifest 定数に当てると、claim に混ざった `sorry` が `sorryAx` として出る。
  `lake build` はこれを警告だけで通す（exit 0）
- 実行ファイルの中から `$LAKE build <Module>` を回せる（`lake exe` はビルドを終えてから
  起動するので詰まらない）
- root の `lakefile.toml` + `srcDir = "lean"` で、ソースを今の場所に置いたままビルドできる
- `lake update` は依存の `lean-toolchain` を利用者の root に書く
- `[[lean_exe]]` の `supportInterpreter` は TOML から効く
- olean 実測: 全 149 MB / 利用者向け閉包 55 MB / 証明のみ 93 MB
