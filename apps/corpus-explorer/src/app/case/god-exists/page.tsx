import { getCurrentCase } from "@/lib/current-case-data";
import { CaseOverview } from "./content";

export default function GodExistsPage() {
  return <CaseOverview view={getCurrentCase()} />;
}
