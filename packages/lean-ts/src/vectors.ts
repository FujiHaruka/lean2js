import { readFileSync } from "node:fs";

export type EncodedValue =
  | { t: "bool"; v: boolean }
  | { t: "int53"; v: number }
  | { t: "uint32"; v: number }
  | { t: "string"; v: string }
  | { t: "bigint"; v: string }
  | { t: "obj"; ctor: string; fields: Record<string, EncodedValue> }
  | { t: "arr"; v: EncodedValue[] };

export type Vector = {
  fn: string;
  args: EncodedValue[];
} & ({ ok: true; value: EncodedValue } | { ok: false; error: string });

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
    default:
      return value.v;
  }
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
    default:
      return `${value.v}`;
  }
}

export function describeArgs(args: EncodedValue[]): string {
  return args.map(describeValue).join(", ");
}
