#!/usr/bin/env bash
# Builds one sandbox for a documentation-only dogfood: an isolated clone of this compiler plus a fresh
# copy of the template, with the template's git require redirected at the clone. The clone is what the
# session is allowed to read three files of; this checkout stays untouched.
#
#   scripts/dogfood/setup.sh <sandbox-root> <name>
#
# leaves <sandbox-root>/<name>/{lean2js-dep,project}. Hand the session BRIEF.md beside this script,
# a spec from specs/, and those two paths.
set -euo pipefail

repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
root="$1/$2"

rm -rf "$root"
mkdir -p "$root"
cp -Rc "$repo" "$root/lean2js-dep" 2>/dev/null || cp -R "$repo" "$root/lean2js-dep"
rm -rf "$root/lean2js-dep/.git" "$root/lean2js-dep/node_modules"
cp -R "$repo/templates/verified-package/." "$root/project/"
rm -rf "$root/project/.lake" "$root/project/lake-manifest.json"

python3 - "$root/project/lakefile.toml" "$root/lean2js-dep" <<'PY'
import re, sys
path, dep = sys.argv[1], sys.argv[2]
text = open(path).read()
patched = re.sub(r'\[\[require\]\]\nname = "Lean2Js"\n(?:(?!\[\[).*\n)*',
                 f'[[require]]\nname = "Lean2Js"\npath = "{dep}"\n\n', text)
assert patched != text, "the template no longer has a Lean2Js require to redirect"
open(path, "w").write(patched)
PY

echo "ready: $root/project"
