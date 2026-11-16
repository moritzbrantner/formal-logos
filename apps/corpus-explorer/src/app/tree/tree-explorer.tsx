"use client";

import Link from "next/link";
import { useSearchParams } from "next/navigation";
import { useEffect, useMemo, useRef, useState } from "react";

import {
  alternativesByConclusion,
  argumentKind,
  formalStatusLabel,
  layoutTree,
  parseArgumentTree,
  statusKind,
  statusLabel,
  treeHref,
  type ArgumentTree,
  type LayoutNode,
  type TreeArgument,
  type TreeEdge,
  type TreeStatement,
  type TreeTruncation,
} from "@/lib/argument-tree";

import styles from "./tree.module.css";

const basePath = process.env.NEXT_PUBLIC_BASE_PATH ?? "";

type Options = { down: number; up: number; budget: number };

function command(id: string) {
  return `target/release/truth tree ${id}`;
}

export function TreeExplorer({ prebuilt, defaultRoot, options }: { prebuilt: string[]; defaultRoot: string; options: Options }) {
  const params = useSearchParams();
  const id = params.get("id") || defaultRoot;
  const available = useMemo(() => new Set(prebuilt), [prebuilt]);
  const [loaded, setLoaded] = useState<{ id: string; tree?: ArgumentTree; error?: string } | null>(null);

  useEffect(() => {
    if (!available.has(id)) return;
    let live = true;
    fetch(`${basePath}/tree-data/${id}.json`)
      .then((response) => {
        if (!response.ok) throw new Error(`${response.status} tree-data/${id}.json`);
        return response.json();
      })
      .then((value) => live && setLoaded({ id, tree: parseArgumentTree(value) }))
      .catch((cause: Error) => live && setLoaded({ id, error: cause.message }));
    return () => { live = false; };
  }, [id, available]);

  if (!available.has(id)) return <NotPrebuilt id={id} options={options} />;
  if (!loaded || loaded.id !== id) return <p className="text-sm text-[var(--muted)]">Loading the tree of {id}…</p>;
  if (loaded.error || !loaded.tree) return <p role="alert">The tree could not be loaded: {loaded.error}</p>;
  return <TreeView tree={loaded.tree} available={available} />;
}

function NotPrebuilt({ id, options }: { id: string; options: Options }) {
  return <section className={styles.notice} aria-labelledby="tree-local">
    <h2 id="tree-local" className="font-serif text-2xl">This tree is generated locally</h2>
    <p className="mt-3 text-sm leading-6">
      The static site prebuilds the trees of the case root and its route nodes (down {options.down}, up {options.up}, at most{" "}
      {options.budget} nodes). The tree of <code className="break-all">{id}</code> is not among them. Generate it from a checkout:
    </p>
    <pre className={styles.command}>{command(id)}</pre>
    <p className="mt-3 text-sm">
      Add <code>--json</code> for the data this page renders, or <code>--down N --up N --budget N</code> to widen it.
    </p>
    <p className="mt-3 text-sm">
      <Link className="link-quiet" href={`/statements/${id}`}>Statement and proof context</Link>
      {" · "}
      <Link className="link-quiet" href={`/dossiers/${id}`}>Premise dossier</Link>
      {" · "}
      <Link className="link-quiet" href="/tree">Tree of the case root</Link>
    </p>
  </section>;
}

function TreeView({ tree, available }: { tree: ArgumentTree; available: Set<string> }) {
  const layout = useMemo(() => layoutTree(tree), [tree]);
  const statements = useMemo(() => new Map(tree.statements.map((entry) => [entry.id, entry])), [tree]);
  const argumentsById = useMemo(() => new Map(tree.arguments.map((entry) => [entry.id, entry])), [tree]);
  const alternatives = useMemo(() => alternativesByConclusion(tree), [tree]);
  const truncations = useMemo(() => {
    const map = new Map<string, TreeTruncation[]>();
    for (const entry of tree.truncated) map.set(entry.statement_id, [...(map.get(entry.statement_id) ?? []), entry]);
    return map;
  }, [tree]);
  const cycleArguments = useMemo(() => new Set(tree.edges.filter((edge) => edge.cycle).map((edge) => edge.argument_id ?? edge.from)), [tree]);
  const root = statements.get(tree.root)!;
  const scroller = useRef<HTMLDivElement>(null);
  // Open with the root in the middle of the scrolled canvas.
  useEffect(() => {
    const node = layout.byId.get(tree.root);
    const element = scroller.current;
    if (!node || !element) return;
    element.scrollLeft = Math.max(0, node.x + node.width / 2 - element.clientWidth / 2);
    element.scrollTop = Math.max(0, node.y + node.height / 2 - element.clientHeight / 2);
  }, [layout, tree.root]);
  const support = tree.arguments.filter((entry) => entry.sides.includes("down")).length;
  const dependents = tree.arguments.filter((entry) => entry.sides.includes("up")).length;

  return <div className={styles.page}>
    <section className={styles.summary} aria-labelledby="tree-root">
      <p className="eyebrow">Root</p>
      <h2 id="tree-root" className="mt-2 font-serif text-2xl leading-snug" data-root-id={root.id}>{root.label ?? root.id}</h2>
      <p className="mt-2 text-sm"><StatusBadge statement={root} /> {root.is_case_root ? <span className={styles.badge}>case root</span> : null}</p>
      <p className="mt-2 font-mono text-xs break-all text-[var(--muted)]">{root.legacy_id ? `${root.legacy_id} · ` : ""}{root.id}</p>
      {root.lean_declaration ? <p className="mt-1 font-mono text-xs break-all">{root.lean_declaration}</p> : null}
      <p className="mt-3 text-sm">
        {support} supporting and {dependents} dependent argument(s) in view · {tree.node_count} nodes ·{" "}
        down {tree.options.down}, up {tree.options.up}, budget {tree.options.budget}
        {tree.truncated.length ? <> · <span className={styles.truncation}>{tree.truncated.length} truncation marker(s)</span></> : null}
      </p>
      <p className="mt-2 text-sm">
        <Link className="link-quiet" href={`/statements/${root.id}`}>Statement and proof context</Link>
        {" · "}
        <Link className="link-quiet" href={`/dossiers/${root.id}`}>Premise dossier</Link>
        {tree.root !== tree.case_root ? <>{" · "}<Link className="link-quiet" href={treeHref(tree.case_root)}>Re-root on the case root</Link></> : null}
      </p>
      <p className="mt-2 text-xs text-[var(--muted)]">Wider view: <code className="break-all">{command(root.legacy_id ?? root.id)} --budget 400</code></p>
      <Legend />
    </section>
    <div className={styles.body}>
      <div ref={scroller} className={styles.canvasScroll} role="region" aria-label="Argument graph" tabIndex={0}>
        <div className={styles.canvas} style={{ width: layout.width, height: layout.height }}>
          <svg className={styles.edges} width={layout.width} height={layout.height} aria-hidden="true">
            <defs>
              {["supports", "uses", "strengthens", "cycle"].map((kind) => <marker key={kind} id={`tree-arrow-${kind}`} viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
                <path d="M 0 0 L 10 5 L 0 10 z" className={styles[`arrow_${kind}`]} />
              </marker>)}
            </defs>
            {tree.edges.map((edge, index) => <EdgePath key={index} edge={edge} layout={layout.byId} />)}
          </svg>
          {layout.nodes.map((node) => node.kind === "statement"
            ? <StatementNode key={node.id} node={node} statement={statements.get(node.id)!} root={tree.root}
              prebuilt={available.has(node.id)} alternatives={alternatives.get(node.id)?.length ?? 0} truncations={truncations.get(node.id) ?? []} />
            : <ArgumentNode key={node.id} node={node} argument={argumentsById.get(node.id)!}
              alternatives={alternatives.get(argumentsById.get(node.id)!.conclusion_statement_id) ?? []} cycle={cycleArguments.has(node.id)} />)}
        </div>
      </div>
      <TermPanel tree={tree} />
    </div>
  </div>;
}

function Legend() {
  return <ul className={styles.legend} aria-label="Legend">
    <li><span className={`${styles.dot} ${styles.status_established}`} /> established</li>
    <li><span className={`${styles.dot} ${styles.status_closed}`} /> closed, not established</li>
    <li><span className={`${styles.dot} ${styles.status_open}`} /> open (stated or supported)</li>
    <li><span className={`${styles.dot} ${styles.status_bare}`} /> open, bare</li>
    <li><span className={styles.lineSupports} /> argument → conclusion</li>
    <li><span className={styles.lineUses} /> premise → argument</li>
    <li><span className={styles.lineStrengthens} /> stronger ⇒ weaker</li>
    <li><span className={styles.lineCycle} /> cycle (not followed)</li>
  </ul>;
}

function StatusBadge({ statement }: { statement: TreeStatement }) {
  return <span className={`${styles.status} ${styles[`status_${statusKind(statement)}`]}`} title={typeof statement.status === "string" ? `frontier status: ${statement.status}` : undefined}>
    {statusLabel(statement)}
  </span>;
}

function place(node: LayoutNode) {
  return { left: node.x, top: node.y, width: node.width, height: node.height };
}

function StatementNode({ node, statement, root, prebuilt, alternatives, truncations }: {
  node: LayoutNode; statement: TreeStatement; root: string; prebuilt: boolean; alternatives: number; truncations: TreeTruncation[];
}) {
  const isRoot = statement.id === root;
  return <div className={`${styles.statement} ${styles[`frame_${statusKind(statement)}`]} ${isRoot ? styles.rootNode : ""}`} style={place(node)}>
    <Link
      href={treeHref(statement.id)}
      className={styles.statementLink}
      data-testid="tree-statement"
      data-statement-id={statement.id}
      data-role={statement.role}
      data-prebuilt={prebuilt ? "true" : "false"}
      title={`${statement.label ?? statement.id}\n${statusLabel(statement)} · ${statement.role.replaceAll("_", " ")}${prebuilt ? "" : "\nNot prebuilt: opens the local command"}`}
      aria-current={isRoot ? "page" : undefined}
    >
      <span className={styles.statementLabel}>{statement.label ?? statement.id}</span>
    </Link>
    <span className={styles.nodeMeta}>
      <StatusBadge statement={statement} />
      {alternatives > 1 ? <span className={styles.badge} title="Alternative arguments conclude this statement">OR · {alternatives}</span> : null}
      {statement.role === "co_premise" ? <span className={styles.badge} title="Another premise of a dependent argument; not expanded">co-premise</span> : null}
      {statement.role === "strength_neighbor" ? <span className={styles.badge} title="The other end of a strength order; not expanded">strength</span> : null}
      {truncations.map((entry) => <span key={entry.side} className={`${styles.badge} ${styles.truncation}`} data-testid="tree-truncation"
        title={`${entry.omitted_arguments} more argument(s) on the ${entry.side} side not shown (${entry.reason} limit)`}>
        … {entry.omitted_arguments} more {entry.side === "down" ? "↓" : "↑"} ({entry.reason})
      </span>)}
    </span>
  </div>;
}

function ArgumentNode({ node, argument, alternatives, cycle }: { node: LayoutNode; argument: TreeArgument; alternatives: string[]; cycle: boolean }) {
  const kind = argumentKind(argument);
  const transcriptionKinds = [...new Set(argument.results.map((result) => result.transcription).filter(Boolean))].join(", ");
  const position = alternatives.indexOf(argument.id);
  const result = argument.results.find((entry) => !entry.transcription) ?? argument.results[0];
  return <div className={`${styles.argument} ${styles[`argument_${kind}`]}`} style={place(node)} data-testid="tree-argument" data-argument-id={argument.id}
    title={argument.label ?? argument.id}>
    <span className={styles.argumentLabel}>{argument.label ?? argument.id}</span>
    <span className={styles.nodeMeta}>
      <span className={styles.badge}>{kind === "transcription" ? `transcription${transcriptionKinds ? ` (${transcriptionKinds})` : ""}` : kind === "verified" ? "verified" : "no result"}</span>
      <span className={styles.badge} title="All premises of one argument are needed together">AND · {argument.premise_statement_ids.length}</span>
      {alternatives.length > 1 && position >= 0 ? <span className={styles.badge} title="One of several alternative arguments">OR {position + 1}/{alternatives.length}</span> : null}
      {argument.route ? <span className={styles.badge} title="Open leaves of this route to the root">route cost {argument.route.cost}{argument.route.cheapest ? " · cheapest" : ""}</span> : null}
      {cycle ? <span className={`${styles.badge} ${styles.cycleBadge}`}>↺ cycle</span> : null}
      {result ? <Link className="link-quiet" href={`/results/${result.id}`}>result</Link> : null}
    </span>
  </div>;
}

function EdgePath({ edge, layout }: { edge: TreeEdge; layout: Map<string, LayoutNode> }) {
  // Draw in the direction of inference: premise → argument → conclusion; stronger ⇒ weaker.
  const [sourceId, targetId] = edge.kind === "uses" ? [edge.to, edge.from] : [edge.from, edge.to];
  const source = layout.get(sourceId);
  const target = layout.get(targetId);
  if (!source || !target) return null;
  const kind = edge.cycle ? "cycle" : edge.kind;
  const centre = (node: LayoutNode) => node.x + node.width / 2;
  let d: string;
  if (Math.abs(source.y - target.y) < 1) {
    const y = source.y;
    d = `M ${centre(source)} ${y} C ${centre(source)} ${y - 40}, ${centre(target)} ${y - 40}, ${centre(target)} ${y}`;
  } else {
    const down = source.y < target.y;
    const y1 = down ? source.y + source.height : source.y;
    const y2 = down ? target.y : target.y + target.height;
    const middle = (y1 + y2) / 2;
    d = `M ${centre(source)} ${y1} C ${centre(source)} ${middle}, ${centre(target)} ${middle}, ${centre(target)} ${y2}`;
  }
  return <path d={d} className={`${styles.edge} ${styles[`edge_${kind}`] ?? ""}`} markerEnd={`url(#tree-arrow-${kind in { supports: 1, uses: 1, strengthens: 1, cycle: 1 } ? kind : "uses"})`}
    data-edge-kind={edge.kind} data-cycle={edge.cycle ? "true" : "false"} />;
}

function TermPanel({ tree }: { tree: ArgumentTree }) {
  const definitions = [...tree.definitions].sort((a, b) =>
    Number(b.used_by.includes(tree.root)) - Number(a.used_by.includes(tree.root)) || b.used_by.length - a.used_by.length || (a.term ?? a.label ?? a.id).localeCompare(b.term ?? b.label ?? b.id));
  const disambiguations = [...tree.disambiguations].sort((a, b) => b.used_by.length - a.used_by.length || (a.label ?? a.id).localeCompare(b.label ?? b.id));
  return <aside className={styles.terms} aria-labelledby="tree-terms">
    <h2 id="tree-terms" className="eyebrow">Terms in view</h2>
    <p className="mt-2 text-xs text-[var(--muted)]">Definitions and disambiguations linked by the statements shown, the root’s first.</p>
    <h3 className="mt-4 font-medium">Definitions ({definitions.length})</h3>
    {definitions.length ? <ul className="mt-2 grid gap-3" data-testid="tree-definitions">{definitions.map((definition) => <li key={definition.id} className={styles.term}>
      <Link className="link-quiet font-medium" href={`/definitions/${definition.id}`}>{definition.term ?? definition.label ?? definition.id}</Link>
      {definition.used_by.includes(tree.root) ? <span className={styles.badge}>root</span> : null}
      {definition.senses.length ? <p className="mt-1">{definition.senses.map((sense) => <span key={`${sense.disambiguation_id}-${sense.sense_id}`} className={styles.sense}>{sense.sense_label ?? "unlabelled sense"}</span>)}</p> : null}
      <p className="mt-1 font-mono text-xs break-all text-[var(--muted)]">{definition.lean_declaration ?? "no Lean declaration"}</p>
      <p className="mt-1 text-xs" data-testid="tree-formal-status">{formalStatusLabel(definition)} · {definition.basis ?? "basis not recorded"} · used by {definition.used_by.length} in view</p>
    </li>)}</ul> : <p className="mt-2 text-sm">No statement in view links a definition.</p>}
    <h3 className="mt-5 font-medium">Disambiguations ({disambiguations.length})</h3>
    {disambiguations.length ? <ul className="mt-2 grid gap-3">{disambiguations.map((entry) => <li key={entry.id} className={styles.term}>
      <span className="font-medium">{entry.label ?? entry.term_label ?? entry.id}</span>
      <p className="mt-1">{entry.senses.map((sense, index) => <span key={sense.id ?? index} className={styles.sense}>{sense.label ?? sense.definition_id ?? "sense"}</span>)}</p>
      <p className="mt-1 text-xs text-[var(--muted)]">used by {entry.used_by.length} in view</p>
    </li>)}</ul> : <p className="mt-2 text-sm">No statement in view links a disambiguation.</p>}
  </aside>;
}
