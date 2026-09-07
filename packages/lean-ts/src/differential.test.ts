import { fileURLToPath } from "node:url";
import * as generated from "@leants/verified-example";
import { describe, expect, it } from "vitest";
import { decode, describeArgs, encode, loadVectors } from "./vectors.js";

const vectorsPath = fileURLToPath(new URL("../../verified-example/vectors.json", import.meta.url));
const vectors = loadVectors(vectorsPath);

const exported = generated as unknown as Record<string, (...args: unknown[]) => unknown>;

describe("生成した ESM は Lean の eval と一致する", () => {
  it("ベクタが空でない", () => {
    expect(vectors.length).toBeGreaterThan(0);
  });

  for (const [index, vector] of vectors.entries()) {
    const label = `${vector.fn}(${describeArgs(vector.args)})`;
    it(`#${index} ${label}`, () => {
      const fn = exported[vector.fn];
      expect(fn, `${vector.fn} is not exported`).toBeTypeOf("function");
      const args = vector.args.map(decode);

      if (vector.ok) {
        expect(encode(fn(...args), vector.value.t)).toEqual(vector.value);
      } else {
        expect(() => fn(...args)).toThrowError(expect.objectContaining({ code: vector.error }));
      }
    });
  }
});
