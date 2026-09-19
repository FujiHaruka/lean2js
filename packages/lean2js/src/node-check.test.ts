import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { describe, expect, it } from "vitest";

const leanSource = readFileSync(
  fileURLToPath(new URL("../../../Lean2Js/NodeCheck.lean", import.meta.url)),
  "utf8",
);
const script = /r#"([\s\S]*?)"#/.exec(leanSource)?.[1];
if (script === undefined)
  throw new Error("NodeCheck.lean no longer holds the script as a raw string");

type Vector = Record<string, unknown>;

const int53 = (v: number) => ({ t: "int53", v });
const vector = (fields: Vector = {}): Vector => ({
  fn: "f",
  args: [int53(1)],
  ok: true,
  value: int53(1),
  ...fields,
});

function check(indexJs: string, vectors: Vector[]): { status: number | null; stdout: string } {
  const dir = mkdtempSync(join(tmpdir(), "node-check-"));
  try {
    writeFileSync(join(dir, "package.json"), '{ "type": "module" }');
    writeFileSync(join(dir, "index.js"), indexJs);
    writeFileSync(join(dir, "vectors.json"), JSON.stringify(vectors));
    writeFileSync(join(dir, "check.mjs"), script as string);
    const run = spawnSync(process.execPath, [join(dir, "check.mjs"), dir], { encoding: "utf8" });
    return { status: run.status, stdout: run.stdout };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

const throwing = (code: string) =>
  `export function f() { throw Object.assign(new Error("boom"), { code: "${code}" }); }`;

describe("the script emit runs on Node", () => {
  it("passes a module that agrees on every vector", () => {
    const run = check("export function f(x) { return x; }", [vector(), vector()]);
    expect(run.status).toBe(0);
    expect(run.stdout).toContain("2 vectors agree on Node");
  });

  it("passes a throw carrying the expected code", () => {
    const run = check(throwing("divByZero"), [vector({ ok: false, error: "divByZero" })]);
    expect(run.status).toBe(0);
  });

  it("calls with the objects written back to front and with a key no type declares", () => {
    const money = {
      t: "obj",
      key: "tag",
      ctor: "Money",
      fields: { amount: int53(1), currency: int53(2) },
    };
    const run = check('export function f(m) { return Object.keys(m).join(","); }', [
      vector({
        args: [money],
        shapes: ["reversed"],
        value: { t: "string", v: "currency,amount,tag" },
      }),
      vector({
        args: [money],
        shapes: ["extraKey"],
        value: { t: "string", v: "tag,amount,currency,not a field" },
      }),
    ]);
    expect(run.stdout).toContain("2 vectors agree");
  });
});

describe("a module that disagrees", () => {
  it("fails on a wrong value", () => {
    const run = check("export function f() { return 2; }", [vector()]);
    expect(run.status).toBe(1);
    expect(run.stdout).toContain("returned 2, expected 1");
  });

  it("fails on minus zero where eval says zero", () => {
    const run = check("export function f() { return -0; }", [vector({ value: int53(0) })]);
    expect(run.status).toBe(1);
    expect(run.stdout).toContain('returned "-0", expected 0');
  });

  it("fails on a wrong BigInt and still names it", () => {
    const run = check("export function f() { return 2n; }", [
      vector({ value: { t: "bigint", v: "1" } }),
    ]);
    expect(run.status).toBe(1);
    expect(run.stdout).toContain('returned "2n", expected "1n"');
  });

  it("fails on a missing export", () => {
    const run = check("export {};", [vector()]);
    expect(run.status).toBe(1);
    expect(run.stdout).toContain("f is not exported");
  });

  it("fails on a throw where a value was due", () => {
    const run = check(throwing("typeError"), [vector()]);
    expect(run.status).toBe(1);
    expect(run.stdout).toContain("threw typeError instead of returning");
  });

  it("fails on the wrong error code", () => {
    const run = check(throwing("typeError"), [vector({ ok: false, error: "divByZero" })]);
    expect(run.status).toBe(1);
    expect(run.stdout).toContain("expected divByZero");
  });

  it("fails on a value where a throw was due", () => {
    const run = check("export function f() { return 1; }", [
      vector({ ok: false, error: "divByZero" }),
    ]);
    expect(run.status).toBe(1);
    expect(run.stdout).toContain("instead of throwing divByZero");
  });

  it("fails when the module does not load", () => {
    const run = check('throw new Error("broken");', [vector()]);
    expect(run.status).not.toBe(0);
  });
});
