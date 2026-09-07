import { describe, expect, it } from "vitest";
import { version } from "./index.js";

describe("version", () => {
  it("matches the package version", () => {
    expect(version).toBe("0.1.0");
  });
});
