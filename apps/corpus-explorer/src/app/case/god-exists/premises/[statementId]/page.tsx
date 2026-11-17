import { notFound } from "next/navigation";
import { getCurrentCase } from "@/lib/current-case-data";
import { CasePremiseDetail } from "../../content";

export function generateStaticParams() {
  return getCurrentCase().premises.map((premise) => ({ statementId: premise.statement.id }));
}

export default async function CasePremisePage({ params }: { params: Promise<{ statementId: string }> }) {
  const { statementId } = await params;
  const view = getCurrentCase();
  const premise = view.premises.find((entry) => entry.statement.id === statementId);
  if (!premise) {
    notFound();
  }
  return <CasePremiseDetail view={view} premise={premise} />;
}
