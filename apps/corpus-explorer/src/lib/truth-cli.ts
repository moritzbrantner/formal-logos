import { execFileSync } from "node:child_process";
import path from "node:path";

/** The repository root: Next and `bun test` run in apps/corpus-explorer (bundled code has no stable import.meta.url). */
export const repositoryRoot = path.resolve(process.cwd(), "../..");

let binary: string | undefined;

/**
 * The repository's Rust `truth` CLI (truth/README.md). `TRUTH_CLI` names a
 * prebuilt binary; otherwise the release binary is built once per process,
 * which refreshes stale build inputs before the first query. The process
 * then reuses that executable; restart after changing CLI sources. An override
 * is used as supplied, without rebuilding or checking its freshness.
 */
function truthBinary(): string {
  if (!binary) {
    binary = process.env.TRUTH_CLI;
    if (!binary) {
      execFileSync("cargo", ["build", "--locked", "--release", "--quiet", "-p", "truth"], {
        cwd: repositoryRoot,
        stdio: ["ignore", "ignore", "inherit"],
      });
      binary = path.join(repositoryRoot, "target", "release", "truth");
    }
  }
  return binary;
}

/**
 * Run `truth <args>` on the repository and parse its JSON stdout. Closure,
 * statuses and dossiers stay owned by the CLI (#507); the explorer only reads
 * them. Frontier and single-dossier JSON include `input_identity`, which the explorer
 * ignores; dossier --all remains a plain map keyed by statement ID. `input`
 * is written to its stdin (`frontier --fixture -`).
 */
export function truthJson(args: string[], input?: string): unknown {
  return JSON.parse(
    execFileSync(truthBinary(), ["--json", ...args], {
      cwd: repositoryRoot,
      input,
      encoding: "utf8",
      maxBuffer: 64 * 1024 * 1024,
    }),
  );
}

/**
 * Run `truth <args>` on the repository for its exit status and text output
 * (for example `structure-report --check-input`); a failure throws.
 */
export function truthText(args: string[], timeout?: number): string {
  return execFileSync(truthBinary(), args, {
    cwd: repositoryRoot,
    encoding: "utf8",
    stdio: "pipe",
    timeout,
    maxBuffer: 64 * 1024 * 1024,
  });
}
