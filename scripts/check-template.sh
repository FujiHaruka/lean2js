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

for file in index.js index.d.ts package.json proof-manifest.json README.md; do
  test -s "dist/$file" || { echo "the template did not write dist/$file"; exit 1; }
done
test ! -e dist/vectors.json || { echo "the vectors were written into dist"; exit 1; }

# A node that disagrees with every vector stands in for a module that disagrees with eval on Node. It has
# to print the verdict the real check prints, because that line is the whole of what tells a module the
# engine refused from a node that never reached the comparison.
mkdir "$work/disagreeing-node"
printf '#!/bin/sh\necho "3 of 3 vectors disagree on Node v0.0.0"\nexit 1\n' > "$work/disagreeing-node/node"
chmod +x "$work/disagreeing-node/node"
if PATH="$work/disagreeing-node:$PATH" lake exe lean2js MyLogic --out refused 2> refused.err; then
  echo "lean2js wrote a package Node did not agree with"; exit 1
fi
grep -q 'disagrees with eval on Node' refused.err \
  || { cat refused.err; echo "lean2js refused for another reason"; exit 1; }
test ! -e refused || { echo "lean2js left files behind for a package Node did not agree with"; exit 1; }

# A node that dies without a word stands in for a broken install rather than a bad module. It is refused
# too, but under its own name: reported as a disagreement it sends a reader to the compiler for a fault
# that is on their machine.
mkdir "$work/silent-node"
printf '#!/bin/sh\nexit 137\n' > "$work/silent-node/node"
chmod +x "$work/silent-node/node"
if PATH="$work/silent-node:$PATH" lake exe lean2js MyLogic --out unrun 2> unrun.err; then
  echo "lean2js wrote a package no node ever checked"; exit 1
fi
grep -q 'before the check reached a verdict' unrun.err \
  || { cat unrun.err; echo "a node that never ran was reported as a module that disagrees"; exit 1; }
test ! -e unrun || { echo "lean2js left files behind for a package no node checked"; exit 1; }

# The namespace is the package, so neither a declaration ship_package did not gather nor a public theorem
# that is not proved may slip out of it quietly.
cp MyLogic.lean MyLogic.lean.orig
cat >> MyLogic.lean <<'LEAN'

namespace MyLogic
@[ship] def lateTotal (x : Int) : Int := x
end MyLogic
LEAN
if lake exe lean2js MyLogic --out late 2> late.err; then
  echo "lean2js wrote a package without a declaration ship_package did not gather"; exit 1
fi
grep -q 'does not carry it' late.err || { cat late.err; echo "lean2js refused for another reason"; exit 1; }
cp MyLogic.lean.orig MyLogic.lean
# A tag is what a consumer reads in the generated type, so a structure that never named its constructor
# would ship as "mk" and say nothing to them.
cat >> MyLogic.lean <<'LEAN'

namespace MyLogic
structure Quota where
  soft : Int
  deriving Lean2Js.Enc
end MyLogic
LEAN
if lake build > unnamed.err 2>&1; then
  echo "deriving Enc accepted a structure whose constructor has no name"; exit 1
fi
grep -q 'would ship as "mk"' unnamed.err || { cat unnamed.err; echo "the build failed for another reason"; exit 1; }
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

# A `def` marked `@[expand]` is written out where it is called, so it has to leave nothing of itself in
# the package: no export, no entry in the types, no function at all.
cat > MyLogic.lean <<'LEAN'
import Lean2Js

namespace MyLogic

open Lean2Js Lean2Js.Core Lean2Js.Enc

@[expand] def take (xs : List α) (n : Int) : List α := Arr.slice xs 0 n

@[ship] def firstThree (xs : List Int) : List Int := take xs 3
@[ship] def firstThreeNames (names : List String) : List String := take names 3

def manifest : Manifest := { package := "@example/my-logic", version := "0.1.0" }

ship_package

end MyLogic
LEAN
lake exe lean2js MyLogic --out expanded
grep -q 'export declare function firstThree' expanded/index.d.ts
test "$(grep -c '^export function ' expanded/index.js)" = 2 \
  || { echo "an @[expand] def reached the generated module"; exit 1; }
if grep -qw 'take' expanded/index.js expanded/index.d.ts; then
  echo "an @[expand] def left its name in the generated package"; exit 1
fi
cp MyLogic.lean.orig MyLogic.lean

# The expansion has no declaration to be refused at, so a body that leaves the subset has to name the
# `def` the author marked rather than the term it was written out into.
cat >> MyLogic.lean <<'LEAN'

namespace MyLogic
@[expand] def half (x : Int) : Int := x / 2
@[ship] def halved (x : Int) : Int := half x
end MyLogic
LEAN
if lake build > expand.err 2>&1; then
  echo "an @[expand] def whose body leaves the subset was accepted"; exit 1
fi
grep -q 'which is marked @\[expand\]' expand.err \
  || { cat expand.err; echo "the build failed for another reason"; exit 1; }
cp MyLogic.lean.orig MyLogic.lean

# Recursion is refused at the mark: a recursor reaching the walk would be reported as a term that is in
# no file.
cat >> MyLogic.lean <<'LEAN'

namespace MyLogic
@[expand] def mySum : List Int → Int
  | [] => 0
  | x :: rest => x + mySum rest
end MyLogic
LEAN
if lake build > recursive.err 2>&1; then
  echo "a recursive def was accepted as @[expand]"; exit 1
fi
grep -q 'cannot be recursive' recursive.err \
  || { cat recursive.err; echo "the build failed for another reason"; exit 1; }
cp MyLogic.lean.orig MyLogic.lean

# A result whose size a value decides is refused where the program text does not bound that value, at
# `ship_package` rather than at the mark. A length is not a bound: nothing in the text says how long an
# array a caller passes is.
cat > MyLogic.lean <<'LEAN'
import Lean2Js

namespace MyLogic

open Lean2Js Lean2Js.Core Lean2Js.Enc

@[ship] def indices (xs : List Int) : List Int := Arr.range (Arr.length xs)

def manifest : Manifest := { package := "@example/my-logic", version := "0.1.0" }

ship_package

end MyLogic
LEAN
if lake build > unbounded.err 2>&1; then
  echo "an Arr.range the program text does not bound was accepted"; exit 1
fi
grep -q 'one element per whole number below a value' unbounded.err \
  || { cat unbounded.err; echo "the build failed for another reason"; exit 1; }
cp MyLogic.lean.orig MyLogic.lean

# Which key a type's constructors are told apart by is the author's call, written above the type. The
# happy path goes all the way through the differential run on Node before anything is written.
cat > MyLogic.lean <<'LEAN'
import Lean2Js

namespace MyLogic

open Lean2Js Lean2Js.Core Lean2Js.Enc

/-- Told apart by `kind` rather than by the default `tag`. -/
@[discriminator "kind"]
inductive Plan where
  | free
  | team
  deriving Enc

@[ship] def planName (plan : Plan) : String :=
  match plan with
  | .free => "Free"
  | .team => "Team"

def manifest : Manifest := { package := "@example/my-logic", version := "0.1.0" }

ship_package

end MyLogic
LEAN
lake exe lean2js MyLogic --out keyed
grep -q 'readonly kind: "free"' keyed/index.d.ts \
  || { echo "the key an author wrote did not reach the generated type"; exit 1; }
grep -q '"kind"' keyed/index.js || { echo "the key an author wrote did not reach the module"; exit 1; }

# The key has to stay free as a field name, whatever the author keyed the type by.
cat > MyLogic.lean <<'LEAN'
import Lean2Js

namespace MyLogic

open Lean2Js Lean2Js.Core Lean2Js.Enc

@[discriminator "kind"]
structure Quota where
  Quota ::
  kind : Int
  deriving Enc

@[ship] def quotaOf (q : Quota) : Int := q.kind

def manifest : Manifest := { package := "@example/my-logic", version := "0.1.0" }

ship_package

end MyLogic
LEAN
if lake build > keyfield.err 2>&1; then
  echo "a field named the key its own type is told apart by was accepted"; exit 1
fi
grep -q 'may not have a field named kind' keyfield.err \
  || { cat keyfield.err; echo "the build failed for another reason"; exit 1; }
cp MyLogic.lean.orig MyLogic.lean

# A program written by hand rather than by ship_package carries no certificate for its declarations, and
# a certificate is the whole of what ties a declaration to the `def` it was read from.
cat > MyLogic.lean <<'LEAN'
import Lean2Js

namespace MyLogic

open Lean2Js Lean2Js.Core

def program : Program := {
  decls := [{ name := "seatCharge", params := [{ name := "seats", ty := .int53 }],
              ret := .int53, body := .lit (.int53 0) }] }

def manifest : Manifest := { package := "@example/my-logic", version := "0.1.0" }

end MyLogic
LEAN
if lake exe lean2js MyLogic --out handbuilt 2> handbuilt.err; then
  echo "lean2js wrote a package from a program it never read out of a def"; exit 1
fi
grep -q 'with no certificate' handbuilt.err \
  || { cat handbuilt.err; echo "lean2js refused for another reason"; exit 1; }
test ! -e handbuilt || { echo "lean2js left files behind for a program with no certificates"; exit 1; }
mv MyLogic.lean.orig MyLogic.lean

grep -q 'export declare function invoiceFor' dist/index.d.ts
grep -q 'free_plan_is_never_charged' dist/proof-manifest.json

# `Lean2Js.compilerVersion` is written down separately from the lakefile's, and a manifest naming a
# version the package was not built at is worse than one naming none.
lakefile_version="$(sed -n 's/^version = "\(.*\)"$/\1/p' "$repo/lakefile.toml")"
sed -n '/"compiler"/,/}/p' dist/proof-manifest.json | grep -q "\"version\": \"$lakefile_version\"" \
  || { echo "the emitted manifest does not name the version in lakefile.toml ($lakefile_version)"; exit 1; }
echo "template check passed: $(grep -c '^export function ' dist/index.js) export(s) written"
