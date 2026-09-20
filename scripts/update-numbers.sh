#!/usr/bin/env bash
# Writes the numbers the documents quote into them, measured by emitting the example. CI runs this and
# fails on the diff, so a number that reaches a document is one nobody typed.
set -euo pipefail

repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

lake exe lean2js Lean2Js.Example --out "$work/out" > "$work/emit.log"

python3 - "$work/emit.log" docs/guarantees.md templates/verified-package/reference/*.md <<'PY'
import re, sys

log, docs = sys.argv[1], sys.argv[2:]
printed = open(log).read()


def measured(pattern: str) -> str:
    found = re.search(pattern, printed, re.M)
    if not found:
        raise SystemExit(f"emit printed nothing matching {pattern!r}:\n{printed}")
    return found.group(1)


numbers = {
    "vectors": measured(r"^(\d+) vectors agree"),
    "fuelNeeded": measured(r"needs (\d+) of the"),
    "fuelCeiling": measured(r"of the (\d+) fuel"),
}

written = set()
for doc in docs:
    source = open(doc).read()
    for name in re.findall(r"<!--n:(\w+)-->", source):
        if name not in numbers:
            raise SystemExit(f"{doc} marks {name}, which nothing here measures")
        written.add(name)
        source = re.sub(f"<!--n:{name}-->.*?<!--/n-->", f"<!--n:{name}-->{numbers[name]}<!--/n-->",
                        source, flags=re.S)
    open(doc, "w").write(source)

unused = set(numbers) - written
if unused:
    raise SystemExit(f"nothing carries a marker for {sorted(unused)}, so measuring it is dead work")

print(" ".join(f"{name} {value}" for name, value in numbers.items()))
PY
