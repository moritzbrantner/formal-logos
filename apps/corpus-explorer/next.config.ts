import { availableParallelism } from "node:os";
import type { NextConfig } from "next";

const isGitHubPages = process.env.GITHUB_PAGES === "true";
const basePath = isGitHubPages ? "/formal-logos" : "";

const nextConfig: NextConfig = {
  output: "export",
  trailingSlash: true,
  basePath,
  // Use all four CI cores; cap larger hosts to bound per-worker corpus snapshots.
  experimental: { cpus: Math.min(4, availableParallelism()) },
  // Client fetches of the static /graph data buckets need the same prefix.
  env: { NEXT_PUBLIC_BASE_PATH: basePath },
};

export default nextConfig;
