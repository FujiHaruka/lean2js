import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { pathToFileURL } from "node:url";
import type { Vector } from "./vectors.js";
import { decode, decodeArgs, describeArgs, loadVectors } from "./vectors.js";

export type ProofManifest = {
  package: string;
  version: string;
  compiler: { name: string; version: string };
  lean: { version: string; githash: string };
  source: string;
  exports: { name: string; signature: string }[];
  theorems: { name: string; statement: string }[];
  axioms: string[];
};

export type Report = {
  manifest: ProofManifest;
  vectors: number;
  failures: string[];
};

/** `Object.is` rather than `===` so that a function returning `0` where the reference semantics says
 * `-0` is a failure: the two are the same number to `===`, and telling them apart is one of the things
 * the generated code is written to get right. */
function agrees(actual: unknown, expected: unknown): boolean {
  if (Object.is(actual, expected)) return true;
  if (Array.isArray(actual) && Array.isArray(expected)) {
    return actual.length === expected.length && actual.every((x, i) => agrees(x, expected[i]));
  }
  if (actual instanceof Map && expected instanceof Map) {
    if (actual.size !== expected.size) return false;
    return [...actual].every(
      ([key, value]) => expected.has(key) && agrees(value, expected.get(key)),
    );
  }
  if (typeof actual !== "object" || actual === null) return false;
  if (typeof expected !== "object" || expected === null) return false;
  const left = actual as Record<string, unknown>;
  const right = expected as Record<string, unknown>;
  const keys = Object.keys(left);
  if (keys.length !== Object.keys(right).length) return false;
  return keys.every((key) => key in right && agrees(left[key], right[key]));
}

function errorCode(thrown: unknown): string | undefined {
  if (typeof thrown !== "object" || thrown === null) return undefined;
  const code = (thrown as { code?: unknown }).code;
  return typeof code === "string" ? code : undefined;
}

export function runVectors(exported: Record<string, unknown>, vectors: Vector[]): string[] {
  const failures: string[] = [];
  for (const [index, vector] of vectors.entries()) {
    const call = `#${index} ${vector.fn}(${describeArgs(vector.args, vector.shapes)})`;
    const fn = exported[vector.fn];
    if (typeof fn !== "function") {
      failures.push(`${call}: ${vector.fn} is not exported`);
      continue;
    }
    let returned: unknown;
    try {
      returned = (fn as (...args: unknown[]) => unknown)(...decodeArgs(vector));
    } catch (thrown) {
      if (vector.ok) {
        failures.push(`${call}: threw ${errorCode(thrown) ?? String(thrown)} instead of returning`);
      } else if (errorCode(thrown) !== vector.error) {
        failures.push(
          `${call}: threw ${errorCode(thrown) ?? String(thrown)}, expected ${vector.error}`,
        );
      }
      continue;
    }
    if (!vector.ok) {
      failures.push(`${call}: returned instead of throwing ${vector.error}`);
    } else if (!agrees(returned, decode(vector.value))) {
      failures.push(
        `${call}: returned ${JSON.stringify(returned)}, expected ${JSON.stringify(vector.value)}`,
      );
    }
  }
  return failures;
}

export async function checkArtifact(dir: string): Promise<Report> {
  const root = resolve(dir);
  const manifest = JSON.parse(
    readFileSync(resolve(root, "proof-manifest.json"), "utf8"),
  ) as ProofManifest;
  const vectors = loadVectors(resolve(root, "vectors.json"));
  const exported = (await import(pathToFileURL(resolve(root, "index.js")).href)) as Record<
    string,
    unknown
  >;
  return { manifest, vectors: vectors.length, failures: runVectors(exported, vectors) };
}

const MAX_LISTED_FAILURES = 10;

export function formatReport(report: Report): string {
  const { manifest, vectors, failures } = report;
  const lines = [
    `${manifest.package} ${manifest.version}`,
    `compiled by ${manifest.compiler.name} ${manifest.compiler.version} from ${manifest.source} with Lean ${manifest.lean.version}`,
    `${manifest.exports.length} exports, ${manifest.theorems.length} theorems, axioms: ${manifest.axioms.join(", ")}`,
  ];
  if (failures.length === 0) {
    lines.push(`${vectors} vectors agree with the reference semantics`);
  } else {
    lines.push(`${failures.length} of ${vectors} vectors disagree with the reference semantics`);
    lines.push(...failures.slice(0, MAX_LISTED_FAILURES));
    if (failures.length > MAX_LISTED_FAILURES) {
      lines.push(`... and ${failures.length - MAX_LISTED_FAILURES} more`);
    }
  }
  return `${lines.join("\n")}\n`;
}
