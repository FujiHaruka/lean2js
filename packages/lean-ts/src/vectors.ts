import { readFileSync } from "node:fs";

export type EncodedValue =
  | { t: "bool"; v: boolean }
  | { t: "int53"; v: number }
  | { t: "uint32"; v: number }
  | { t: "string"; v: string }
  | { t: "bigint"; v: string };

export type Vector = {
  fn: string;
  args: EncodedValue[];
} & ({ ok: true; value: EncodedValue } | { ok: false; error: string });

export function decode(value: EncodedValue): boolean | number | string | bigint {
  return value.t === "bigint" ? BigInt(value.v) : value.v;
}

/** 実行結果を `eval` 側の符号化に戻す。JS の値だけからは Int53 と UInt32 を区別できないので、
 * 期待値の型を手がかりにする。 */
export function encode(result: unknown, expected: EncodedValue["t"]): EncodedValue {
  switch (expected) {
    case "bool":
      return { t: "bool", v: result as boolean };
    case "int53":
      return { t: "int53", v: result as number };
    case "uint32":
      return { t: "uint32", v: result as number };
    case "string":
      return { t: "string", v: result as string };
    case "bigint":
      return { t: "bigint", v: String(result as bigint) };
  }
}

export function loadVectors(path: string): Vector[] {
  return JSON.parse(readFileSync(path, "utf8")) as Vector[];
}

export function describeArgs(args: EncodedValue[]): string {
  return args.map((a) => `${a.t}(${a.v})`).join(", ");
}
