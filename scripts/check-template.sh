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

python3 - "$work/lakefile.toml" "$repo/lean" <<'PY'
import re, sys
path, dep = sys.argv[1], sys.argv[2]
with open(path) as f:
    text = f.read()
patched = re.sub(
    r'\[\[require\]\]\nname = "LeanTs"\n(?:(?!\[\[).*\n)*',
    f'[[require]]\nname = "LeanTs"\npath = "{dep}"\n\n',
    text,
)
assert patched != text, "the template no longer has a LeanTs require to redirect"
with open(path, "w") as f:
    f.write(patched)
PY

cd "$work"
lake build
lake exe leants MyLogic --out dist

for file in index.js index.d.ts index.js.map package.json proof-manifest.json vectors.json; do
  test -s "dist/$file" || { echo "the template did not write dist/$file"; exit 1; }
done

grep -q 'export declare function orderTotal' dist/index.d.ts
grep -q 'nothing_charged_below_one' dist/proof-manifest.json
echo "template check passed: $(grep -c '^export function ' dist/index.js) export(s) written"
