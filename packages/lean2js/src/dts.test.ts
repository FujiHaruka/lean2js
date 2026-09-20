import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import type { Money, OrderState, TrapCode, TrapError } from "@lean2js/verified-example";
import {
  add,
  addMoney,
  allLines,
  divide,
  limitsFor,
  mostRecentFirst,
  objCatalogueSize,
  objRepriced,
  roleRank,
  scaleFee,
  ship,
} from "@lean2js/verified-example";
import { describe, expect, it } from "vitest";

/** How TypeScript reads the printed `.d.ts` text is the one thing `docs/guarantees.md` trusts rather
 * than proves: `entry_check_fits_dts` and `dts_fits_entry_check` are about `Dts.TsSat`, the declared
 * type read as a predicate in Lean. These say what tsc makes of the same text. Every
 * `@ts-expect-error` below fails `pnpm typecheck` the moment the call it sits on starts compiling. */

const generatedDts = fileURLToPath(new URL("../../verified-example/index.d.ts", import.meta.url));
const tsc = fileURLToPath(new URL("../../../node_modules/typescript/bin/tsc", import.meta.url));

const typeError = expect.objectContaining({ code: "typeError" });

const jpy = { tag: "Money", amount: 1, currency: "JPY" } as const satisfies Money;
const twoJpy = { tag: "ok", value: { tag: "Money", amount: 2, currency: "JPY" } };

describe("the generated .d.ts", () => {
  // `tsconfig.base.json` has `skipLibCheck`, so this is the only place the file is read on its own
  // terms rather than only where a call site happens to reach into it.
  it("is TypeScript the compiler accepts on its own terms", () => {
    const run = spawnSync(
      process.execPath,
      [tsc, "--noEmit", "--strict", "--target", "es2023", "--module", "nodenext", generatedDts],
      { encoding: "utf8" },
    );
    expect(run.stdout.trim()).toBe("");
    expect(run.status).toBe(0);
  });

  it("prints a list of lists as a type a caller can pass", () => {
    const orders: readonly (readonly number[])[] = [[1, 2], [3]];
    expect(allLines(orders)).toEqual([1, 2, 3]);
  });

  it("carries the declared result type through", () => {
    const sum: number = add(1, 2);
    const fee: bigint = scaleFee(2n, 3n);
    expect(sum).toBe(3);
    expect(fee).toBe(5n);
  });
});

describe("what the declared type refuses, the entry check refuses too", () => {
  it("a string where the subset declared a number", () => {
    // @ts-expect-error `add` is declared over `number`
    const call = () => add("1", 2);
    expect(call).toThrowError(typeError);
  });

  it("an argument that was not passed at all", () => {
    // @ts-expect-error `add` takes two
    const call = () => add(1);
    expect(call).toThrowError(typeError);
  });

  it("a number where the subset declared a bigint", () => {
    // @ts-expect-error `scaleFee` is declared over `bigint`
    const call = () => scaleFee(2, 3n);
    expect(call).toThrowError(typeError);
  });

  it("a tag the declared union does not name", () => {
    // @ts-expect-error the union names `guest`, `member` and `admin`
    const call = () => roleRank({ tag: "superuser" });
    expect(call).toThrowError(typeError);
    expect(roleRank({ tag: "admin" })).toBe(2);
  });
});

describe("where the two do not line up", () => {
  // The caveat docs/guarantees.md names: `Int53` and `UInt32` are both `number`, so a number that is
  // not an integer, or is outside the range, satisfies TypeScript and is refused when passed.
  it("TypeScript takes a number that is no Int53", () => {
    expect(() => add(1e300, 1)).toThrowError(typeError);
    expect(() => add(1.5, 1)).toThrowError(typeError);
  });

  // The other direction, which is TypeScript's own rule rather than anything the printer chose: a key
  // the declaration does not name is dropped before the body reads it, but a fresh literal carrying
  // one is where the excess property check fires.
  it("TypeScript refuses an undeclared key only when it is written as a literal", () => {
    const noted = { tag: "Money", amount: 1, currency: "JPY", note: "ignored" } as const;
    expect(addMoney(noted, jpy)).toEqual(twoJpy);
    // @ts-expect-error the excess property check fires on the literal
    const call = () => addMoney({ ...jpy, note: "ignored" }, jpy);
    expect(call()).toEqual(twoJpy);
  });

  it("`readonly` and `ReadonlyMap` bind tsc and not the engine", () => {
    const recent = mostRecentFirst(["a", "b"]);
    const limits = limitsFor({ tag: "admin" });
    // @ts-expect-error `readonly string[]` carries no `push`
    const push: unknown = recent.push;
    // @ts-expect-error a `ReadonlyMap` carries no `set`
    const set: unknown = limits.set;
    expect(recent).toEqual(["b", "a"]);
    expect(limits.get("daily")).toBe(1000);
    expect(push).toBeTypeOf("function");
    expect(set).toBeTypeOf("function");
  });

  it("a dictionary handed back is the plain object alone, and goes straight back in", () => {
    // The return is printed at the object alone, so it lands in an object-typed binding with no
    // narrowing of the consumer's own; the parameter is printed at the union, so it goes back in.
    const book: { readonly [key: string]: number } = objRepriced({ a: 1 }, "b", 2);
    // @ts-expect-error the union a parameter takes is what a `ReadonlyMap` binding needs, not this
    const asMap: ReadonlyMap<string, number> = book;
    expect(book.b).toBe(2);
    expect(objCatalogueSize(book)).toBe(2);
    expect(asMap).toBeTypeOf("object");
  });
});

describe("the codes an export throws", () => {
  // A code added to or dropped from `Traps.allCodes` fails `pnpm typecheck` here: a missing key and an
  // extra one are both errors against `Record<TrapCode, string>`. That is the whole point of publishing
  // the codes as a union — a consumer's own exhaustive handling breaks at compile time rather than
  // falling through at run time.
  const explanation = {
    typeError: "an argument the declared type does not admit",
    int53Overflow: "arithmetic that left the safe-integer range",
    divByZero: "a division or remainder by zero",
    indexOutOfBounds: "an index, slice or substring outside the value it reads",
  } satisfies Record<TrapCode, string>;

  it("narrows to the codes the function it was thrown by reaches", () => {
    const caught = ((): TrapError<"typeError" | "int53Overflow" | "divByZero"> => {
      try {
        divide(1, 0);
      } catch (thrown) {
        return thrown as TrapError<"typeError" | "int53Overflow" | "divByZero">;
      }
      throw new Error("a division by zero returned a number");
    })();
    expect(caught).toBeInstanceOf(Error);
    expect(caught.code).toBe("divByZero");
    expect(explanation[caught.code]).toBe("a division or remainder by zero");
  });
});

describe("a union the generated types hand back", () => {
  it("narrows on the key its own type declares, both ways round", () => {
    const outcome = ship({ kind: "placed", orderId: 7 }, "T-1");
    if (outcome.tag !== "ok") throw new Error(outcome.error);
    const state: OrderState = outcome.value;
    expect(state).toEqual({ kind: "shipped", orderId: 7, trackingId: "T-1" });
  });

  it("refuses the key another type is told apart by", () => {
    // @ts-expect-error `OrderState` is told apart by `kind`, not by `tag`
    const call = () => ship({ tag: "placed", orderId: 7 }, "T-1");
    expect(call).toThrowError(typeError);
  });
});
