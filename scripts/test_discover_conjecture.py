"""Offline tests for scripts/discover_conjecture.py (#1834).

No Lean run: the rendered certification file is checked as text, and Lean's
`#print axioms` output is synthesized per check, so the filters and the
outcome classes are exercised on the acceptance fixtures of #1834:
a true multi-premise consequence survives with every assumption; a known
implication is rejected as old; a contradictory pair is not support; a
name-only cross-domain identification is rejected; a failed proof stays
unresolved unless a model is certified."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import discover_conjecture as dc  # noqa: E402

NS = "TruthCore.ConjecturePilot"


def statement(sid, decl):
    return {"id": sid, "label": sid, "lean_declaration": decl}


def corpus(tags=None, arguments=(), relations=()):
    stmts = [
        statement("S-A", "M1.A"), statement("S-B", "M1.B"), statement("S-C", "M2.C"),
        statement("S-D", "M2.D"), statement("S-E", "M3.E"), statement("S-NOT-A", "M1.NotA"),
    ]
    disamb = [{"senses": [{"label": label, "lean_parameters": [{"declaration": d, "parameter": p}]}]}
              for (d, p), label in (tags or {}).items()]
    args = list(arguments)
    results = [{"argument_id": a["id"]} for a in args]
    return dc.Corpus(stmts, args, results, list(relations), disamb)


# Declaration binders as `DiscoverBinders.lean` prints them: [name, carrier, instance].
BINDERS = {
    "M1.A": {"module": "Mod1", "binders": [["B", True, False], ["P", False, False], ["Q", False, False]]},
    "M1.B": {"module": "Mod1", "binders": [["B", True, False], ["Q", False, False], ["S", False, False]]},
    "M1.NotA": {"module": "Mod1", "binders": [["B", True, False], ["P", False, False], ["Q", False, False]]},
    "M2.C": {"module": "Mod2", "binders": [["B", True, False], ["P", False, False], ["S", False, False]]},
    "M2.D": {"module": "Mod2", "binders": [["B", True, False], ["S", False, False], ["T", False, False]]},
    "M3.E": {"module": "Mod3", "binders": [["B", True, False], ["S", False, False], ["T", False, False]]},
}

FAMILIES = {"left": {"statements": ["S-A", "S-NOT-A"]}, "right": {"statements": ["S-B", "S-C", "S-D", "S-E"]}}


def config(*candidates):
    return {"run": {"namespace": NS}, "families": FAMILIES, "candidate": list(candidates)}


BINDS = [["B", "Type"], ["P", "B → Prop"], ["Q", "B → Prop"], ["S", "B → Prop"], ["T", "B → Prop"]]


def lean_output(spans, proved=(), axioms=("propext", "Classical.choice", "Quot.sound")):
    """Synthesized `#print axioms` lines: the checks whose suffix is in
    `proved` print the axioms, every other check prints `sorryAx`."""
    out = []
    for name, span in spans.items():
        suffix = name.split("_", 1)[1]
        if suffix in proved:
            out.append(f"'{name}' depends on axioms: [{', '.join(axioms)}]")
        else:
            out.append(f"'{name}' depends on axioms: [sorryAx]")
    return "\n".join(out)


def run(cfg, crp, proved=(), axioms=("propext", "Classical.choice", "Quot.sound")):
    _, spans = dc.render(cfg, crp, BINDERS)
    status = dc.parse_lean(lean_output(spans, proved, axioms), spans)
    return dc.classify(cfg, crp, BINDERS, status, spans)[0]


# A -> P to Q (Mod1), B -> Q to S (Mod1), C -> P to S (Mod2): A, B |- C by chaining.
CHAIN = {
    "id": "K1", "binders": BINDS[:4],
    "premise": [
        {"statement": "S-A", "args": {"B": "B", "P": "P", "Q": "Q"}},
        {"statement": "S-B", "args": {"B": "B", "Q": "Q", "S": "S"}},
    ],
    "conclusion": {"lean": "∀ x, P x → S x"},
    "witness": {"assign": {"B": "Unit", "P": "fun _ => True", "Q": "fun _ => True", "S": "fun _ => True"},
                "instance": "∃ x, P x"},
}


class Render(unittest.TestCase):
    def test_named_arguments_and_checks(self):
        text, spans = dc.render(config(CHAIN), corpus(), BINDERS)
        self.assertIn("(M1.A (B := B) (P := P) (Q := Q))", text)
        self.assertIn("conjecture_unfold; duper [*]", text)
        checks = {s["check"] for s in spans.values()}
        self.assertTrue({"main", "vac", "none", "probe", "drop", "vacdrop", "litneg"} <= checks)

    def test_unmapped_parameter_is_an_error(self):
        bad = dict(CHAIN, premise=[{"statement": "S-A", "args": {"B": "B", "P": "P"}}])
        with self.assertRaises(dc.ConfigError):
            dc.render(config(bad), corpus(), BINDERS)

    def test_model_is_the_claim_applied_to_typed_values(self):
        cand = dict(CHAIN, countermodel=[{"assign": {"B": "Bool", "P": "fun _ => True", "Q": "fun _ => True", "S": "fun _ => False"}}])
        text, _ = dc.render(config(cand), corpus(), BINDERS)
        self.assertIn("(fun (B : Type) (P : B → Prop) (Q : B → Prop) (S : B → Prop) => "
                      "(M1.A (B := B) (P := P) (Q := Q)) ∧ (M1.B (B := B) (Q := Q) (S := S)) ∧ ¬ (∀ x, P x → S x)) "
                      "(Bool) (fun _ => True) (fun _ => True) (fun _ => False)", text)

    def test_spans_count_prelude_lines(self):
        text, spans = dc.render(config(CHAIN), corpus(), BINDERS)
        lines = text.splitlines()
        for name, span in spans.items():
            short = name.rsplit(".", 1)[1]
            self.assertTrue(any(f"theorem {short} " in lines[i - 1] for i in range(span["lines"][0], span["lines"][1] + 1)))


class Acceptance(unittest.TestCase):
    def test_true_multi_premise_consequence_survives_with_all_assumptions(self):
        r = run(config(CHAIN), corpus(), proved={"main", "wit"})
        self.assertEqual(r["outcome"], "verified_conditional_implication")
        self.assertEqual(r["minimal_premises"], ["S-A", "S-B"])
        self.assertEqual(r["dropped_premises"], [])
        self.assertTrue(r["support"])
        self.assertTrue(all(v.startswith("not dropped") for v in r["premise_status"].values()))

    def test_support_needs_a_certified_witness(self):
        r = run(config(CHAIN), corpus(), proved={"main"})
        self.assertEqual(r["outcome"], "verified_conditional_implication")
        self.assertFalse(r["support"])
        self.assertTrue(any("not support" in f for f in r["flags"]))
        text, _ = dc.render(config(CHAIN), corpus(), BINDERS)
        self.assertIn("∧ (∃ x, P x)) (Unit)", text)

    def test_single_family_consequence_is_not_cross_family(self):
        # both premises in one family and a new conclusion: not cross-family
        cfg = config(CHAIN)
        cfg["families"] = {"left": {"statements": ["S-A", "S-B"]}, "right": {"statements": ["S-C"]}}
        r = run(cfg, corpus(), proved={"main"})
        self.assertEqual(r["outcome"], "rejected")
        self.assertIn("single_family", r["filters"])

    def test_redundant_premise_is_reported_and_dropped(self):
        r = run(config(CHAIN), corpus(), proved={"main", "drop1"})
        self.assertEqual(r["minimal_premises"], ["S-A"])
        self.assertEqual(r["dropped_premises"], ["S-B"])

    def test_two_independent_deletions_do_not_drop_both(self):
        r = run(config(CHAIN), corpus(), proved={"main", "drop0", "drop1"})
        self.assertEqual(r["minimal_premises"], ["S-A", "S-B"])
        self.assertTrue(any("not minimized" in f for f in r["flags"]))
        self.assertTrue(all(v.startswith("kept: several single deletions") for v in r["premise_status"].values()))

    def test_error_inside_the_goal_still_classifies_models(self):
        cand = dict(CHAIN, countermodel=[{"assign": {"B": "Bool", "P": "fun _ => True", "Q": "fun _ => True", "S": "fun _ => False"}}])
        cfg = config(cand)
        _, spans = dc.render(cfg, corpus(), BINDERS)
        main = next(n for n, s in spans.items() if s["check"] == "main")
        out = lean_output(spans, {"cm0"}) + f"\nConjectures.lean:{spans[main]['lines'][0] + 1}:2: error: (deterministic) timeout"
        r = dc.classify(cfg, corpus(), BINDERS, dc.parse_lean(out, spans), spans)[0]
        self.assertEqual(r["outcome"], "certified_non_implication")
        # no declaration at all: an error
        out = "\n".join(l for l in lean_output(spans, {"cm0"}).splitlines() if not l.startswith(f"'{main}'"))
        r = dc.classify(cfg, corpus(), BINDERS, dc.parse_lean(out, spans), spans)[0]
        self.assertEqual(r["outcome"], "error")

    def test_needed_only_with_a_certified_omission_model(self):
        cand = dict(CHAIN, countermodel=[{"omit": ["S-B"], "assign": {"B": "Bool", "P": "fun _ => True", "Q": "fun _ => True", "S": "fun _ => False"}}])
        r = run(config(cand), corpus(), proved={"main", "cm0"})
        self.assertEqual(r["premise_status"]["S-B"], "needed (omission model certified)")
        self.assertTrue(r["premise_status"]["S-A"].startswith("not dropped (unresolved"))

    def test_known_implication_is_rejected_as_old(self):
        cand = {"id": "K2", "binders": BINDS[:4],
                "premise": [{"statement": "S-A", "args": {"B": "B", "P": "P", "Q": "Q"}},
                            {"statement": "S-B", "args": {"B": "B", "Q": "Q", "S": "S"}}],
                "conclusion": {"statement": "S-C", "args": {"B": "B", "P": "P", "S": "S"}}}
        crp = corpus(tags={("M1.A", "P"): "P_1", ("M2.C", "P"): "P_1", ("M1.B", "S"): "S_1", ("M2.C", "S"): "S_1"},
                     arguments=[{"id": "ARG-OLD", "premise_statement_ids": ["S-A", "S-B"], "conclusion_statement_id": "S-C"}])
        r = run(config(cand), crp, proved={"main"})
        self.assertEqual(r["outcome"], "rejected")
        self.assertIn("known", r["filters"])
        # by forward-chaining closure through an intermediate statement as well
        crp = corpus(tags={("M1.A", "P"): "P_1", ("M2.C", "P"): "P_1", ("M1.B", "S"): "S_1", ("M2.C", "S"): "S_1"},
                     arguments=[{"id": "X1", "premise_statement_ids": ["S-A"], "conclusion_statement_id": "S-D"},
                                {"id": "X2", "premise_statement_ids": ["S-D", "S-B"], "conclusion_statement_id": "S-C"}])
        r = run(config(cand), crp, proved={"main"})
        self.assertIn("known", r["filters"])
        self.assertIn("closure", r["reason"])

    def test_contradictory_pair_is_not_support(self):
        cand = {"id": "K3", "binders": BINDS[:3],
                "premise": [{"statement": "S-A", "args": {"B": "B", "P": "P", "Q": "Q"}},
                            {"statement": "S-NOT-A", "args": {"B": "B", "P": "P", "Q": "Q"}}],
                "conclusion": {"lean": "∀ x, P x"}}
        # literal P / not P: rejected, neither support nor an incompatibility
        r = run(config(cand), corpus(), proved={"main", "vac", "litneg1_0"})
        self.assertEqual(r["outcome"], "rejected")
        self.assertIn("literal_negation", r["filters"])
        self.assertFalse(r["support"])
        # a contradiction that takes logic to find: an incompatibility, never support
        r = run(config(cand), corpus(), proved={"main", "vac"})
        self.assertEqual(r["outcome"], "incompatibility")
        self.assertEqual(r["inconsistent_core"], ["S-A", "S-NOT-A"])
        self.assertFalse(r["support"])

    def test_same_module_needs_the_same_parameter_name(self):
        # A.P (Mod1) and B.S (Mod1) on one binder: same module, different names
        cand = {"id": "K5", "binders": [["B", "Type"], ["P", "B → Prop"], ["Q", "B → Prop"]],
                "premise": [{"statement": "S-A", "args": {"B": "B", "P": "P", "Q": "Q"}},
                            {"statement": "S-B", "args": {"B": "B", "Q": "Q", "S": "P"}}],
                "conclusion": {"lean": "∀ x, P x → P x"}}
        r = run(config(cand), corpus(), proved={"main"})
        self.assertEqual(r["outcome"], "open_bridge")
        self.assertIn("P", {ob["binder"] for ob in r["identification"]["obligations"]})

    def test_two_parameters_of_one_occurrence_are_an_obligation(self):
        cand = {"id": "K6", "binders": [["B", "Type"], ["P", "B → Prop"], ["S", "B → Prop"]],
                "premise": [{"statement": "S-A", "args": {"B": "B", "P": "P", "Q": "P"}},
                            {"statement": "S-B", "args": {"B": "B", "Q": "P", "S": "S"}}],
                "conclusion": {"lean": "∀ x, P x → S x"}}
        r = run(config(cand), corpus(), proved={"main"})
        obs = {ob["binder"]: ob for ob in r["identification"]["obligations"]}
        self.assertIn("P", obs)
        self.assertEqual(obs["P"]["same_declaration"], ["M1.A"])
        self.assertFalse(r["support"])

    def test_name_only_cross_domain_match_is_rejected(self):
        # C (Mod2) and E (Mod3) share T by name only: no module, no tag
        cand = {"id": "K4", "binders": [["B", "Type"], ["S", "B → Prop"], ["T", "B → Prop"]],
                "premise": [{"statement": "S-D", "args": {"B": "B", "S": "S", "T": "T"}},
                            {"statement": "S-E", "args": {"B": "B", "S": "S", "T": "T"}}],
                "conclusion": {"lean": "∀ x, S x → T x"}}
        cfg = config(cand)
        cfg["families"] = {"left": {"statements": ["S-D"]}, "right": {"statements": ["S-E"]}}
        r = run(cfg, corpus(), proved={"main"})
        self.assertEqual(r["outcome"], "open_bridge")
        self.assertIn("name_only_identification", r["filters"])
        self.assertFalse(r["support"])
        binders = {ob["binder"] for ob in r["identification"]["obligations"]}
        self.assertEqual(binders, {"B", "S", "T"})
        # one shared tag on S admits S and forces the carrier B; T stays open
        r = run(cfg, corpus(tags={("M2.D", "S"): "S_1", ("M3.E", "S"): "S_1"}), proved={"main"})
        self.assertEqual({ob["binder"] for ob in r["identification"]["obligations"]}, {"T"})
        # with every relation tagged alike the identification is admissible
        tags = {("M2.D", "S"): "S_1", ("M3.E", "S"): "S_1", ("M2.D", "T"): "T_1", ("M3.E", "T"): "T_1"}
        r = run(cfg, corpus(tags=tags), proved={"main"})
        self.assertEqual(r["identification"]["obligations"], [])
        self.assertEqual(r["outcome"], "verified_conditional_implication")
        # different senses of one term: rejected as a sense mismatch
        tags[("M3.E", "T")] = "T_2"
        r = run(cfg, corpus(tags=tags), proved={"main"})
        self.assertIn("senses", r["filters"])

    def test_failed_proof_stays_unresolved_without_a_model(self):
        r = run(config(CHAIN), corpus(), proved=())
        self.assertEqual(r["outcome"], "unresolved")
        self.assertFalse(r["support"])
        cand = dict(CHAIN, countermodel=[{"assign": {"B": "Bool", "P": "fun _ => True", "Q": "fun _ => True", "S": "fun _ => False"}}])
        # an uncertified model does not refute
        r = run(config(cand), corpus(), proved=())
        self.assertEqual(r["outcome"], "unresolved")
        # a certified model is a non-implication in that model only
        r = run(config(cand), corpus(), proved={"cm0"})
        self.assertEqual(r["outcome"], "certified_non_implication")
        # an omission model certifies only that the omitted premise is needed there
        cand = dict(CHAIN, countermodel=[{"omit": ["S-B"], "assign": {"B": "Bool", "P": "fun _ => True", "Q": "fun _ => True", "S": "fun _ => False"}}])
        r = run(config(cand), corpus(), proved={"cm0"})
        self.assertEqual(r["outcome"], "unresolved")
        self.assertEqual(r["omission_models"][0]["omit"], ["S-B"])


class RealConfiguration(unittest.TestCase):
    def test_pilot_candidates_resolve(self):
        path = Path(__file__).resolve().parent.parent / "explorations" / "conjectures" / "actualization-grades-1834.toml"
        cfg = dc.load_config(path)
        crp = dc.Corpus.load(dc.ROOT)
        owner = dc.family_of(cfg, crp)
        self.assertEqual(len(cfg["candidate"]), 15)
        for cand in cfg["candidate"]:
            items = list(cand.get("premise", [])) + ([cand["conclusion"]] if "statement" in cand["conclusion"] else [])
            for item in items:
                sid = crp.resolve(item["statement"])
                self.assertTrue(crp.declaration(sid))
                self.assertTrue(sid in owner or crp.resolve("STMT-FIRST-UNMOVED-MOVER-IS-MAXIME-ENS") == sid, cand["id"])
            names = {n for n, _ in cand["binders"]}
            for model in cand.get("countermodel", []) + ([cand["witness"]] if "witness" in cand else []):
                self.assertEqual(set(model["assign"]), names, cand["id"])
        self.assertTrue(dc.declarations(cfg, crp))


class Filters(unittest.TestCase):
    def test_transcription_and_tautology(self):
        r = run(config(CHAIN), corpus(), proved={"main", "probe"})
        self.assertIn("transcription", r["filters"])
        r = run(config(CHAIN), corpus(), proved={"main", "none"})
        self.assertIn("tautology", r["filters"])

    def test_axioms_outside_the_three_are_rejected(self):
        r = run(config(CHAIN), corpus(), proved={"main"}, axioms=("propext", "Lean.ofReduceBool"))
        self.assertIn("axioms", r["filters"])

    def test_axioms_apply_to_every_check(self):
        cand = {"id": "K7", "binders": BINDS[:3],
                "premise": [{"statement": "S-A", "args": {"B": "B", "P": "P", "Q": "Q"}},
                            {"statement": "S-NOT-A", "args": {"B": "B", "P": "P", "Q": "Q"}}],
                "conclusion": {"lean": "∀ x, P x"}}
        r = run(config(cand), corpus(), proved={"vac"}, axioms=("Lean.ofReduceBool",))
        self.assertNotEqual(r["outcome"], "incompatibility")
        self.assertTrue(any("outside the allowed" in f for f in r["flags"]))

    def test_open_bridge_wording_under_obligations(self):
        cand = {"id": "K8", "binders": [["B", "Type"], ["S", "B → Prop"], ["T", "B → Prop"]],
                "premise": [{"statement": "S-D", "args": {"B": "B", "S": "S", "T": "T"}},
                            {"statement": "S-E", "args": {"B": "B", "S": "S", "T": "T"}}],
                "conclusion": {"lean": "∀ x, S x → T x"}, "bridge": {"lean": "∀ x, S x → T x"}}
        r = run(config(cand), corpus(), proved={"bridge"})
        self.assertIn("under the listed identifications", r["bridge"]["verified"])
        self.assertIn("not shown to be weakest", r["bridge"]["verified"])

    def test_open_bridge_needs_bridge_without_restating(self):
        cand = dict(CHAIN, bridge={"lean": "∀ x, Q x → S x"})
        r = run(config(cand), corpus(), proved={"bridge"})
        self.assertEqual(r["outcome"], "open_bridge")
        r = run(config(cand), corpus(), proved={"bridge", "bridge_alone"})
        self.assertEqual(r["outcome"], "unresolved")

    def test_error_in_a_check_is_not_a_proof(self):
        _, spans = dc.render(config(CHAIN), corpus(), BINDERS)
        main = next(n for n, s in spans.items() if s["check"] == "main")
        line = spans[main]["lines"][0] + 1
        out = lean_output(spans, {"main"}) + f"\nConjectures.lean:{line}:2: error: unknown identifier"
        status = dc.parse_lean(out, spans)
        self.assertFalse(status[main]["proved"])


if __name__ == "__main__":
    unittest.main()
