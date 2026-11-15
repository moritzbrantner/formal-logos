import type { Metadata } from "next";
import { Suspense } from "react";

import { STATIC_TREE_OPTIONS, staticTreeIds } from "@/lib/argument-tree-data";
import { DEFAULT_ROOT_STATEMENT_ID } from "@/lib/proposition-graph";

import { TreeExplorer } from "./tree-explorer";

export const metadata: Metadata = {
  title: "Re-rooted argument tree — Truth Core",
  description: "Any proposition as the root: its supporting arguments below, its dependents above, and the definitions of every term in view.",
};

export default function TreePage() {
  return <article className="min-w-0">
    <header className="mb-6 border-b border-[var(--line)] pb-5">
      <p className="eyebrow">Truth Core / Research instruments</p>
      <h1 className="mt-2 font-serif text-4xl tracking-[-0.055em] sm:text-5xl">Re-rooted argument tree</h1>
      <p className="mt-3 max-w-3xl text-sm leading-6 text-[var(--muted)]">
        The selected proposition is the root. Arguments concluding it are alternatives (OR) below it, each with its premises
        as one bundle (AND); arguments using it lead up to their conclusions. Click any proposition to make it the root.
        Statuses come from <code>truth tree</code>, computed with the selected proposition as frontier root; this view closes nothing.
      </p>
    </header>
    <Suspense fallback={<p className="text-sm text-[var(--muted)]">Loading the argument tree…</p>}>
      <TreeExplorer prebuilt={staticTreeIds()} defaultRoot={DEFAULT_ROOT_STATEMENT_ID} options={STATIC_TREE_OPTIONS} />
    </Suspense>
  </article>;
}
