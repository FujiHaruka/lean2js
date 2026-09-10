import { readFileSync } from "node:fs";

export type EncodedValue =
  | { t: "bool"; v: boolean }
  | { t: "int53"; v: number }
  | { t: "uint32"; v: number }
  | { t: "string"; v: string }
  | { t: "bigint"; v: string }
  | { t: "obj"; ctor: string; fields: Record<string, EncodedValue> }
  | { t: "arr"; v: EncodedValue[] }
  | { t: "dict"; v: [string, EncodedValue][] };

/** How the vector says an argument may be written on the JS side. `decode` produces the spelling
 * `encodeValue` writes; the `.d.ts` names no key order and tolerates keys the type does not declare, so
 * the other two spellings have vectors of their own. */
export type ArgShape = "canonical" | "reversed" | "extraKey";

export type Vector = {
  fn: string;
  args: EncodedValue[];
  shapes?: ArgShape[];
} & ({ ok: true; value: EncodedValue } | { ok: false; error: string });

/** The key `extraKey` adds. It is not an identifier, so no declared field can be named it. */
const EXTRA_KEY = "not a field";

/** Turns an `eval` value back into a JS value. The output of the generated code is matched directly
 * against this result. Going the other way (encoding the run's result and comparing) cannot tell Int53
 * from UInt32 given a JS value alone, growing a per-type branch in the harness as well. */
export function decode(value: EncodedValue): unknown {
  switch (value.t) {
    case "bigint":
      return BigInt(value.v);
    case "obj": {
      const out: Record<string, unknown> = { tag: value.ctor };
      for (const [key, field] of Object.entries(value.fields)) {
        out[key] = decode(field);
      }
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

/** Rewrites a decoded argument the way `shape` says a caller may write it. An object's keys come back in
 * insertion order, so rebuilding one back to front is what a reordered call looks like from the callee. A
 * Map's keys are left where they are: no order is declared for them. */
export function reshape(shape: ArgShape, value: unknown): unknown {
  if (Array.isArray(value)) return value.map((item) => reshape(shape, item));
  if (value instanceof Map) {
    return new Map([...value].map(([key, item]) => [key, reshape(shape, item)]));
  }
  if (typeof value !== "object" || value === null) return value;

  const entries = Object.entries(value).map(([key, item]) => [key, reshape(shape, item)] as const);
  const out: Record<string, unknown> = {};
  for (const [key, item] of shape === "reversed" ? [...entries].reverse() : entries) {
    out[key] = item;
  }
  if (shape === "extraKey") out[EXTRA_KEY] = true;
  return out;
}

export function decodeArgs(vector: Vector): unknown[] {
  return vector.args.map((arg, i) => reshape(vector.shapes?.[i] ?? "canonical", decode(arg)));
}

export function loadVectors(path: string): Vector[] {
  return JSON.parse(readFileSync(path, "utf8")) as Vector[];
}

export function describeValue(value: EncodedValue): string {
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

export function describeArgs(args: EncodedValue[], shapes?: ArgShape[]): string {
  return args
    .map((arg, i) => {
      const shape = shapes?.[i] ?? "canonical";
      return shape === "canonical" ? describeValue(arg) : `${describeValue(arg)} as ${shape}`;
    })
    .join(", ");
}
