#!/usr/bin/env node
import { checkArtifact, formatReport } from "./check.js";

const USAGE = "usage: npx @leants/check <dir>\n";

const [dir, ...rest] = process.argv.slice(2);
if (dir === undefined || dir.startsWith("-") || rest.length > 0) {
  process.stderr.write(USAGE);
  process.exit(1);
}

const report = await checkArtifact(dir);
process.stdout.write(formatReport(report));
process.exit(report.failures.length === 0 ? 0 : 1);
