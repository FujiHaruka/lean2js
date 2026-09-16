#!/usr/bin/env bash
# Builds templates/verified-package in a scratch directory and checks that an npm package comes out.
# The template depends on this library over git so that a user can copy it and build; the copy here is
# pointed at the working tree instead, so the check tests the template as it stands rather than as it
# was last pushed.
set -euo pipefail

repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

cp -R "$repo/templates/verified-package/." "$work/"
rm -rf "$work/.lake" "$work/lake-manifest.json"

python3 - "$work/lakefile.toml" "$repo" <<'PY'
import re, sys
path, dep = sys.argv[1], sys.argv[2]
with open(path) as f:
    text = f.read()
patched = re.sub(
    r'\[\[require\]\]\nname = "Lean2Js"\n(?:(?!\[\[).*\n)*',
    f'[[require]]\nname = "Lean2Js"\npath = "{dep}"\n\n',
    text,
)
assert patched != text, "the template no longer has a Lean2Js require to redirect"
with open(path, "w") as f:
    f.write(patched)
PY

cd "$work"
lake build
lake exe lean2js MyLogic --out dist

for file in index.js index.d.ts index.js.map package.json proof-manifest.json README.md \
            my-logic.lean2js; do
  test -s "dist/$file" || { echo "the template did not write dist/$file"; exit 1; }
done
test ! -e dist/vectors.json || { echo "the vectors were written into dist"; exit 1; }

# A node that disagrees with every vector stands in for a module that disagrees with eval on Node.
mkdir "$work/disagreeing-node"
printf '#!/bin/sh\nexit 1\n' > "$work/disagreeing-node/node"
chmod +x "$work/disagreeing-node/node"
if PATH="$work/disagreeing-node:$PATH" lake exe lean2js MyLogic --out refused; then
  echo "lean2js wrote a package Node did not agree with"; exit 1
fi
test ! -e refused || { echo "lean2js left files behind for a package Node did not agree with"; exit 1; }

# The namespace is the package, so neither a declaration program% did not gather nor a public theorem that
# is not proved may slip out of it quietly.
cp MyLogic.lean MyLogic.lean.orig
cat >> MyLogic.lean <<'LEAN'

namespace MyLogic
open Lean2Js.Core Lean2Js.Core.Dsl
def lateTotal : Decl := decl% lateTotal(x : Int53) : Int53 := x
end MyLogic
LEAN
if lake exe lean2js MyLogic --out late 2> late.err; then
  echo "lean2js wrote a package without a declaration program% did not gather"; exit 1
fi
grep -q 'would not ship' late.err || { cat late.err; echo "lean2js refused for another reason"; exit 1; }
cp MyLogic.lean.orig MyLogic.lean
cat >> MyLogic.lean <<'LEAN'

namespace MyLogic
theorem unfinished : 1 = 2 := sorry
end MyLogic
LEAN
if lake exe lean2js MyLogic --out unproved 2> unproved.err; then
  echo "lean2js wrote a package claiming a theorem proved with sorry"; exit 1
fi
grep -q 'rests on sorryAx' unproved.err || { cat unproved.err; echo "lean2js refused for another reason"; exit 1; }
mv MyLogic.lean.orig MyLogic.lean

grep -q 'export declare function invoiceFor' dist/index.d.ts
grep -q 'free_plan_is_never_charged' dist/proof-manifest.json

# `Lean2Js.compilerVersion` is written down separately from the lakefile's, and a manifest naming a
# version the package was not built at is worse than one naming none.
lakefile_version="$(sed -n 's/^version = "\(.*\)"$/\1/p' "$repo/lakefile.toml")"
sed -n '/"compiler"/,/}/p' dist/proof-manifest.json | grep -q "\"version\": \"$lakefile_version\"" \
  || { echo "the emitted manifest does not name the version in lakefile.toml ($lakefile_version)"; exit 1; }
echo "template check passed: $(grep -c '^export function ' dist/index.js) export(s) written"
