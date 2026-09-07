import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { describe, expect, it } from "vitest";

const BASE64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

/** Lean 側のエンコーダとは独立な実装。共有すると同じ間違いを二度するだけになる。 */
function decodeVlq(segment: string): number[] {
  const values: number[] = [];
  let shift = 0;
  let accumulated = 0;
  for (const char of segment) {
    const digit = BASE64.indexOf(char);
    expect(digit, `unexpected base64 digit ${char}`).toBeGreaterThanOrEqual(0);
    accumulated += (digit & 31) << shift;
    if (digit & 32) {
      shift += 5;
      continue;
    }
    const negative = accumulated & 1;
    const magnitude = accumulated >> 1;
    values.push(negative ? -magnitude : magnitude);
    shift = 0;
    accumulated = 0;
  }
  return values;
}

function read(name: string): string {
  return readFileSync(
    fileURLToPath(new URL(`../../verified-example/${name}`, import.meta.url)),
    "utf8",
  );
}

type SourceMap = {
  version: number;
  sources: string[];
  sourcesContent: string[];
  mappings: string;
};

function decodeGeneratedLineToSourceLine(mappings: string): Map<number, number> {
  const out = new Map<number, number>();
  let sourceLine = 0;
  mappings.split(";").forEach((group, generatedLine) => {
    if (group === "") return;
    const [, , delta] = decodeVlq(group);
    expect(delta).toBeTypeOf("number");
    sourceLine += delta as number;
    out.set(generatedLine, sourceLine);
  });
  return out;
}

describe("source map は生成した関数を .leants の宣言に対応づける", () => {
  const map = JSON.parse(read("index.js.map")) as SourceMap;
  const generated = read("index.js").split("\n");
  const source = map.sourcesContent[0]?.split("\n") ?? [];

  it("v3 で、埋め込んだソースが配布物と一致する", () => {
    expect(map.version).toBe(3);
    expect(map.sources).toEqual(["example.leants"]);
    expect(map.sourcesContent[0]).toBe(read("example.leants"));
  });

  it("index.js が source map を指している", () => {
    expect(read("index.js")).toContain("//# sourceMappingURL=index.js.map");
  });

  it("対応づけた行はどちらも同じ関数を指す", () => {
    const entries = [...decodeGeneratedLineToSourceLine(map.mappings)];
    expect(entries.length).toBeGreaterThan(10);

    for (const [generatedLine, sourceLine] of entries) {
      const generatedText = generated[generatedLine] ?? "";
      const sourceText = source[sourceLine] ?? "";

      const name = /^export function (\w+)\(/.exec(generatedText)?.[1];
      expect(name, `line ${generatedLine} is not a function: ${generatedText}`).toBeTruthy();
      expect(sourceText, `source line ${sourceLine} should declare ${name}`).toMatch(
        new RegExp(`^def ${name}\\(`),
      );
    }
  });
});
