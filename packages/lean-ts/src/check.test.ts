import { fileURLToPath } from "node:url";
import { describe, expect, it } from "vitest";
import { checkArtifact, formatReport, runVectors } from "./check.js";
import type { Vector } from "./vectors.js";

const artifact = fileURLToPath(new URL("../../verified-example", import.meta.url));

describe("checking a shipped artifact", () => {
  it("finds every vector agreeing with the artifact this repository generates", async () => {
    const report = await checkArtifact(artifact);
    expect(report.failures).toEqual([]);
    expect(report.vectors).toBeGreaterThan(0);
    expect(report.manifest.axioms).toEqual(["Classical.choice", "Quot.sound", "propext"]);
  });

  it("summarises what the artifact claims", async () => {
    const report = await checkArtifact(artifact);
    expect(formatReport(report)).toContain("@leants/verified-example 0.1.0");
    expect(formatReport(report)).toContain(`${report.vectors} vectors agree`);
  });
});

describe("a disagreeing artifact", () => {
  const vector = (v: Partial<Vector> = {}): Vector =>
    ({
      fn: "f",
      args: [{ t: "int53", v: 1 }],
      ok: true,
      value: { t: "int53", v: 1 },
      ...v,
    }) as Vector;

  it("reports a wrong value", () => {
    const failures = runVectors({ f: () => 2 }, [vector()]);
    expect(failures).toHaveLength(1);
    expect(failures[0]).toContain("expected");
  });

  it("reports zero returned where the reference semantics says minus zero", () => {
    const failures = runVectors({ f: () => 0 }, [vector({ value: { t: "int53", v: -0 } })]);
    expect(failures).toHaveLength(1);
  });

  it("reports a missing export", () => {
    expect(runVectors({}, [vector()])).toHaveLength(1);
  });

  it("reports a throw where a value was due", () => {
    const failures = runVectors(
      {
        f: () => {
          throw Object.assign(new Error("boom"), { code: "typeError" });
        },
      },
      [vector()],
    );
    expect(failures[0]).toContain("threw typeError");
  });

  it("reports the wrong error code", () => {
    const failures = runVectors(
      {
        f: () => {
          throw Object.assign(new Error("boom"), { code: "typeError" });
        },
      },
      [vector({ ok: false, error: "divByZero" })],
    );
    expect(failures[0]).toContain("expected divByZero");
  });

  it("reports a value returned where a throw was due", () => {
    const failures = runVectors({ f: () => 1 }, [vector({ ok: false, error: "divByZero" })]);
    expect(failures[0]).toContain("instead of throwing");
  });
});
