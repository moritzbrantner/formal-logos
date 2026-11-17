import type { ArgumentProjectionCorpus } from "./argument-projection";
import { argumentsConcludingStatement, type Corpus, type CorpusArgument } from "./corpus";

// Like the corpus query indexes, ordering belongs to an immutable corpus
// snapshot. A fresh development snapshot gets its own ordering.
const argumentOrders = new WeakMap<Corpus, Map<CorpusArgument, number>>();

function argumentOrder(corpus: Corpus) {
  let order = argumentOrders.get(corpus);
  if (!order) {
    order = new Map();
    for (const [position, argument] of corpus.arguments.entries()) {
      if (!order.has(argument)) {
        order.set(argument, position);
      }
    }
    argumentOrders.set(corpus, order);
  }
  return order;
}

/**
 * The result page ships only arguments supporting this argument's premises,
 * transitively. Inclusion is independent of verification; the client uses the
 * separate verified IDs when deciding which arguments it may expand.
 */
export function resultProjectionCorpus(corpus: Corpus, argument: CorpusArgument): ArgumentProjectionCorpus {
  const order = argumentOrder(corpus);
  const reachable = new Map([[argument.id, argument]]);
  for (const current of reachable.values()) {
    const candidates = [...new Set(current.premise_statement_ids.flatMap(
      (id) => argumentsConcludingStatement(corpus, id),
    ))];
    // Preserve the original full scan's corpus order, not premise order.
    candidates.sort((left, right) => order.get(left)! - order.get(right)!);
    for (const candidate of candidates) {
      if (!reachable.has(candidate.id)) {
        reachable.set(candidate.id, candidate);
      }
    }
  }

  const projectionArguments = [...reachable.values()];
  const inferenceIds = new Set(projectionArguments.flatMap((entry) => entry.inference_ids));
  const projectionInferences = corpus.inferences.filter((inference) => inferenceIds.has(inference.id));
  const statementIds = new Set([
    ...projectionArguments.flatMap((entry) => [...entry.premise_statement_ids, entry.conclusion_statement_id]),
    ...projectionInferences.flatMap((inference) => [...inference.input_statement_ids, inference.output_statement_id]),
  ]);
  return {
    statements: corpus.statements.filter((statement) => statementIds.has(statement.id)).map(({ id, paraphrase }) => ({ id, paraphrase })),
    // The client needs the projection shape, not each record's source, term,
    // and proof metadata repeated in every consuming result page.
    inferences: projectionInferences.map(({ id, input_statement_ids, output_statement_id, rule, meaning }) => ({
      id, input_statement_ids, output_statement_id, rule, meaning,
    })),
    arguments: projectionArguments.map(({ id, premise_statement_ids, conclusion_statement_id, inference_ids, meaning }) => ({
      id, premise_statement_ids, conclusion_statement_id, inference_ids, meaning,
    })),
    verified_argument_ids: corpus.results.map((entry) => entry.argument_id).filter((id) => reachable.has(id)),
  };
}
