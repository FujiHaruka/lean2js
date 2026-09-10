import { fileURLToPath } from "node:url";
import * as generated from "@leants/verified-example";
import { describe, expect, it } from "vitest";
import { decode, decodeArgs, describeArgs, loadVectors } from "./vectors.js";

const vectorsPath = fileURLToPath(new URL("../../verified-example/vectors.json", import.meta.url));
const vectors = loadVectors(vectorsPath);

const exported = generated as unknown as Record<string, (...args: unknown[]) => unknown>;

describe("the generated ESM agrees with Lean's eval", () => {
  it("has a non-empty set of vectors", () => {
    expect(vectors.length).toBeGreaterThan(0);
  });

  for (const [index, vector] of vectors.entries()) {
    it(`#${index} ${vector.fn}(${describeArgs(vector.args, vector.shapes)})`, () => {
      const fn = exported[vector.fn];
      expect(fn, `${vector.fn} is not exported`).toBeTypeOf("function");
      const args = decodeArgs(vector);

      if (vector.ok) {
        expect(fn(...args)).toEqual(decode(vector.value));
      } else {
        expect(() => fn(...args)).toThrowError(expect.objectContaining({ code: vector.error }));
      }
    });
  }
});
