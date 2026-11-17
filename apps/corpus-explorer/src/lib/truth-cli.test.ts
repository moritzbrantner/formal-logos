import { expect, test } from "bun:test";
import { spawnSync } from "node:child_process";
import { chmodSync, mkdtempSync, readdirSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";

test("JSON transport preserves large reports and cleans up on success and failure", () => {
  const directory = mkdtempSync(path.join(tmpdir(), "truth-transport-test-"));
  const executable = path.join(directory, "fixture");
  try {
    writeFileSync(executable, `#!${process.execPath}\nconst mode = process.argv.at(-1);\nif (mode === "failure") process.exit(7);\nif (mode === "invalid") process.stdout.write("invalid");\nelse process.stdout.write(JSON.stringify({ payload: "x".repeat(65 * 1024 * 1024), last: "retained" }));\n`);
    chmodSync(executable, 0o700);
    const modulePath = path.resolve("src/lib/truth-cli.ts");
    for (const mode of ["large", "failure", "invalid"]) {
      const script = `import { truthJson } from ${JSON.stringify(modulePath)};
        try {
          const result = truthJson([${JSON.stringify(mode)}]);
          if (result.payload.length !== 65 * 1024 * 1024 || result.last !== "retained") process.exit(2);
        } catch { process.exit(3); }`;
      const result = spawnSync(process.execPath, ["-e", script], {
        env: { ...process.env, TRUTH_CLI: executable, TMPDIR: directory },
        encoding: "utf8",
      });
      expect(result.error).toBeUndefined();
      expect(result.status).toBe(mode === "large" ? 0 : 3);
      expect(readdirSync(directory)).toEqual(["fixture"]);
    }
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
});
