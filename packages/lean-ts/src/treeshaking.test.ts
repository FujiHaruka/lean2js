import { fileURLToPath } from "node:url";
import { build } from "esbuild";
import { describe, expect, it } from "vitest";

const entry = 'import { add } from "@leants/verified-example";\nconsole.log(add(1, 2));\n';
const resolveDir = fileURLToPath(new URL(".", import.meta.url));

async function bundle(): Promise<string> {
  const result = await build({
    stdin: { contents: entry, resolveDir, sourcefile: "entry.js", loader: "js" },
    bundle: true,
    format: "esm",
    minify: false,
    write: false,
    platform: "neutral",
  });
  return result.outputFiles[0]?.text ?? "";
}

describe("生成したパッケージは tree shaking できる", () => {
  it("使っていない export とヘルパは落ちる", async () => {
    const out = await bundle();

    expect(out).toContain("function add");
    for (const dropped of ["function ship", "function sumFrom", "__strcmp", "__at", "__eq"]) {
      expect(out, `${dropped} should have been shaken out`).not.toContain(dropped);
    }
  });
});
