import Lean2Js.Json
import Lean2Js.Vectors

/-!
# Holding the artifact against the real JavaScript engine before it is written

The script `emit` runs on Node against the package it is about to write, calling every vector on the real
JavaScript engine. `JsSem` is Lean's picture of JavaScript; this is where the picture is held against the
engine itself.
-/

namespace Lean2Js

/-- A string rather than a `.mjs` file read by `include_str`: Lake does not track a file `include_str`
reads, so an edit to it would leave the old script running until this module rebuilt for another reason. -/
def nodeCheckScript : String := r#"
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { pathToFileURL } from "node:url";

// Not an identifier, so no declared field can be named it.
const EXTRA_KEY = "not a field";
const MAX_LISTED_FAILURES = 10;

function decode(value) {
  switch (value.t) {
    case "bigint":
      return BigInt(value.v);
    case "obj": {
      const out = { tag: value.ctor };
      for (const [key, field] of Object.entries(value.fields)) out[key] = decode(field);
      return out;
    }
    case "arr":
      return value.v.map(decode);
    case "dict":
      return new Map(value.v.map(([key, entry]) => [key, decode(entry)]));
    default:
      return value.v;
  }
}

// A Map's keys are left in place: no order is declared for them.
function reshape(shape, value) {
  if (Array.isArray(value)) return value.map((item) => reshape(shape, item));
  if (value instanceof Map) {
    return new Map([...value].map(([key, item]) => [key, reshape(shape, item)]));
  }
  if (typeof value !== "object" || value === null) return value;
  const entries = Object.entries(value).map(([key, item]) => [key, reshape(shape, item)]);
  const out = {};
  for (const [key, item] of shape === "reversed" ? entries.reverse() : entries) out[key] = item;
  if (shape === "extraKey") out[EXTRA_KEY] = true;
  return out;
}

// `Object.is` rather than `===`, which cannot see a `-0` the generated code failed to normalise.
function agrees(actual, expected) {
  if (Object.is(actual, expected)) return true;
  if (Array.isArray(actual) && Array.isArray(expected)) {
    return actual.length === expected.length && actual.every((x, i) => agrees(x, expected[i]));
  }
  if (actual instanceof Map && expected instanceof Map) {
    return (
      actual.size === expected.size &&
      [...actual].every(([key, value]) => expected.has(key) && agrees(value, expected.get(key)))
    );
  }
  if (typeof actual !== "object" || actual === null) return false;
  if (typeof expected !== "object" || expected === null) return false;
  const keys = Object.keys(actual);
  return (
    keys.length === Object.keys(expected).length &&
    keys.every((key) => key in expected && agrees(actual[key], expected[key]))
  );
}

function errorCode(thrown) {
  return typeof thrown === "object" && thrown !== null && typeof thrown.code === "string"
    ? thrown.code
    : undefined;
}

function show(value) {
  return JSON.stringify(value, (_, v) =>
    typeof v === "bigint" ? `${v}n` : Object.is(v, -0) ? "-0" : v instanceof Map ? [...v] : v,
  );
}

function describeValue(value) {
  switch (value.t) {
    case "obj":
      return `${value.ctor}{${Object.keys(value.fields).join(",")}}`;
    case "arr":
      return `[${value.v.map(describeValue).join(",")}]`;
    case "dict":
      return `{${value.v.map(([key]) => key).join(",")}}`;
    default:
      return `${value.v}`;
  }
}

function describeCall(index, vector) {
  const args = vector.args.map((arg, i) => {
    const shape = vector.shapes?.[i] ?? "canonical";
    return shape === "canonical" ? describeValue(arg) : `${describeValue(arg)} as ${shape}`;
  });
  return `#${index} ${vector.fn}(${args.join(", ")})`;
}

const [dir] = process.argv.slice(2);
const vectors = JSON.parse(readFileSync(join(dir, "vectors.json"), "utf8"));
const exported = await import(pathToFileURL(join(dir, "index.js")).href);

const failures = [];
for (const [index, vector] of vectors.entries()) {
  const call = describeCall(index, vector);
  const fn = exported[vector.fn];
  if (typeof fn !== "function") {
    failures.push(`${call}: ${vector.fn} is not exported`);
    continue;
  }
  const args = vector.args.map((arg, i) => reshape(vector.shapes?.[i] ?? "canonical", decode(arg)));
  let returned;
  try {
    returned = fn(...args);
  } catch (thrown) {
    const threw = errorCode(thrown) ?? String(thrown);
    if (vector.ok) {
      failures.push(`${call}: threw ${threw} instead of returning`);
    } else if (errorCode(thrown) !== vector.error) {
      failures.push(`${call}: threw ${threw}, expected ${vector.error}`);
    }
    continue;
  }
  if (!vector.ok) {
    failures.push(`${call}: returned instead of throwing ${vector.error}`);
  } else if (!agrees(returned, decode(vector.value))) {
    failures.push(`${call}: returned ${show(returned)}, expected ${show(decode(vector.value))}`);
  }
}

if (failures.length === 0) {
  console.log(`${vectors.length} vectors agree on Node ${process.version}`);
} else {
  console.log(`${failures.length} of ${vectors.length} vectors disagree on Node ${process.version}`);
  for (const failure of failures.slice(0, MAX_LISTED_FAILURES)) console.log(failure);
  if (failures.length > MAX_LISTED_FAILURES) {
    console.log(`... and ${failures.length - MAX_LISTED_FAILURES} more`);
  }
  process.exitCode = 1;
}
"#

#guard (nodeCheckScript.splitOn (Json.str extraKeyName).render).length == 2

end Lean2Js
