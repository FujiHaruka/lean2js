import * as generated from "@leants/verified-example";
import { describe, expect, it } from "vitest";

/** The two calls the milestone is about, made against the shipped ESM rather than the model: a `Money`
 * the `.d.ts` type admits but `encodeValue` would never write, and the one thing a TypeScript type still
 * cannot say. The vectors cover the same ground generatively; these name the cases. */
const { addMoney, sameMoney } = generated as unknown as {
  addMoney: (a: unknown, b: unknown) => unknown;
  sameMoney: (a: unknown, b: unknown) => unknown;
};

const jpy = { tag: "Money", amount: 1, currency: "JPY" } as const;
const two = { tag: "ok", value: { tag: "Money", amount: 2, currency: "JPY" } };

describe("a call the .d.ts type admits", () => {
  it("is accepted with the fields in another order", () => {
    expect(addMoney({ currency: "JPY", amount: 1, tag: "Money" }, jpy)).toEqual(two);
  });

  it("is accepted carrying a key the type does not declare", () => {
    expect(addMoney({ ...jpy, note: "ignored" }, jpy)).toEqual(two);
  });

  it("has the undeclared key dropped before the body reads it", () => {
    expect(sameMoney({ ...jpy, note: "ignored" }, jpy)).toBe(true);
  });

  it("is refused when a number falls outside the Int53 range", () => {
    expect(() => addMoney({ tag: "Money", amount: 1e300, currency: "JPY" }, jpy)).toThrowError(
      expect.objectContaining({ code: "typeError" }),
    );
  });
});
