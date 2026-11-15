import { getStaticTrees } from "@/lib/argument-tree-data";

/** Static `truth tree` JSON of each prebuilt statement (#1674), fetched by /tree. */
export const dynamic = "force-static";
export const dynamicParams = false;

export function generateStaticParams() {
  return [...getStaticTrees().keys()].map((id) => ({ file: `${id}.json` }));
}

export async function GET(_request: Request, { params }: { params: Promise<{ file: string }> }) {
  const { file } = await params;
  const tree = getStaticTrees().get(file.replace(/\.json$/, ""));
  return tree ? Response.json(tree) : new Response("Not found", { status: 404 });
}
