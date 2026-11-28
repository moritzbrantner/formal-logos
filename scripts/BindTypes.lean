/-
Emit the binder structure of advertised result theorems as JSON (#162).

Usage, after `lake build`:

    lake env lean --run scripts/BindTypes.lean <input.json>

`<input.json>` is `{"modules": [...], "theorems": [...]}`. The tool imports the
modules, reads each theorem's type with `forallTelescope` (no reduction), and
prints one JSON object per theorem: every binder with its name, whether its
type lives in `Prop` (a propositional hypothesis) or not (a type or vocabulary
parameter), and the head constant of that type; then the same for the result
type. `truth bind-check` compares this with the corpus records.

Head constants are read syntactically (`getAppFn` after stripping metadata).
Nothing is unfolded, so a `…Reading` definition applied to arguments reports
that definition. Logical wrappers the corpus may use around a declaration are
peeled and listed separately: `¬` (`Not`) and `∃` (`Exists`).

Theory bundles (#160). The input may list `bundle_prefixes`, namespaces of
theory definitions (for example `TruthCore.Comparison.`). A propositional
binder whose head is such a definition is additionally unfolded exactly one
step and split on `∧`; its conjuncts are listed under `bundle`. They are not
unfolded further, so a conjunct that is itself a theory definition stays one
item. For the result type, a theory definition is unfolded one step, leading
`∃` binders are opened, the body is split on `∧`, and each conjunct that is a
theory definition is unfolded one step and split again: this lists the
commitments of a consistency claim such as `∃ s, Background s ∧ Catholic s`.

Sense constants (owner direction 2026-11-07, docs/corpus-model.md "Sense-indexed
terms"). The input may list `sense_constants`, the Lean declarations of every
disambiguation sense, and `sense_theorems`. For each binder and the result of a
listed theorem, `senses` names the sense constants the type reaches: constants
occurring in the elaborated type, and in the values of project (`TruthCore.`)
definitions it uses, unfolded transitively. A sense constant is reported and
not unfolded further; library constants are boundaries. When `sense_constants`
is given, one extra array element `{"sense_aliases": {name: canonical}}` maps
each sense constant present in the environment to the constant it is an alias
of (a definition whose eta-reduced value is a bare constant, followed through).

Restating lemmas (#2190). The input may list `restating`, objects
`{"lemma": name, "dischargers": [[hypothesis, name], ...]}` taken from results that
declare `restates_conclusion`. For each, one extra array element
`{"restating_lemma": name, ...}` describes the lemma: its axioms
(`collectAxioms`), every binder (name, `prop`, head, `core_head`, and for a
propositional binder its type), and the body after `forallTelescope` (no
reduction). An `Iff` body lists both `sides`, any other body one `side`. A
side gives its head, the constants it mentions (`getUsedConstants`,
syntactic), the number of leading `∃` binders and how many of them occur in
the matrix. For each named discharger of a propositional binder, the tool
instantiates the discharger's trailing binders with metavariables and asks
`isDefEq` whether its conclusion is the binder's type; it reports the
discharger's axioms and the hypotheses left over. `truth bind-check` compares
this with the corpus records; it decides nothing about what the lemma means.
-/
import Lean

open Lean Meta

/-- Closed expression encoding for a reviewed migration contract. Binder names and
metadata are ignored; argument order, binder kinds, universe parameters and every
dependent domain remain explicit. This is deliberately stricter than defeq. -/
partial def contractLevel (params : List Name) : Level → Json
  | .zero => toJson (["zero"] : List String)
  | .succ l => toJson #[Json.str "succ", contractLevel params l]
  | .max a b => toJson #[Json.str "max", contractLevel params a, contractLevel params b]
  | .imax a b => toJson #[Json.str "imax", contractLevel params a, contractLevel params b]
  | .param n => toJson #[Json.str "param", toJson (params.idxOf? n), Json.str (if params.contains n then "" else n.toString)]
  | .mvar _ => Json.str "unsupported-level-metavariable"

partial def contractExpr (params : List Name) : Expr → Json
  | .bvar i => toJson #[Json.str "bound", toJson i]
  | .fvar _ => Json.str "unsupported-free-variable"
  | .mvar _ => Json.str "unsupported-expression-metavariable"
  | .sort l => toJson #[Json.str "sort", contractLevel params l]
  | .const n ls => toJson #[Json.str "constant", Json.str n.toString, toJson (ls.map (contractLevel params))]
  | .app f a => toJson #[Json.str "application", contractExpr params f, contractExpr params a]
  | .lam _ d b bi => toJson #[Json.str "lambda", Json.str (reprStr bi), contractExpr params d, contractExpr params b]
  | .forallE _ d b bi => toJson #[Json.str "forall", Json.str (reprStr bi), contractExpr params d, contractExpr params b]
  | .letE _ t v b nondep => toJson #[Json.str "let", contractExpr params t, contractExpr params v, contractExpr params b, toJson nondep]
  | .lit l => toJson #[Json.str "literal", Json.str (reprStr l)]
  | .mdata _ e => contractExpr params e
  | .proj n i e => toJson #[Json.str "projection", Json.str n.toString, toJson i, contractExpr params e]

/-- Project definition bodies and declaration types determine interpretation;
theorem proof bodies are verified by the existing result pipeline instead.
Constructor types expose structure laws, including requirements received via
non-Prop structure/typeclass parameters. Library declarations stay boundaries. -/
def expressionContract (info : ConstantInfo) : MetaM Json := do
  let env ← getEnv
  let mut pending := info.type.getUsedConstants
  let mut visited : NameSet := {}
  let mut dependencies : Array Json := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if visited.contains n || !("TruthCore.".isPrefixOf n.toString) then continue
    visited := visited.insert n
    let some ci := env.find? n | throwError "contract dependency unavailable: {n}"
    pending := pending ++ ci.type.getUsedConstants
    let mut item := Json.mkObj [("declaration", Json.str n.toString),
      ("universe_parameters", toJson ci.levelParams.length),
      ("type", contractExpr ci.levelParams ci.type)]
    match ci with
    | .defnInfo d =>
      pending := pending ++ d.value.getUsedConstants
      item := item.mergeObj (Json.mkObj [("kind", Json.str "definition"),
        ("value", contractExpr ci.levelParams d.value)])
    | .inductInfo d =>
      pending := pending ++ d.ctors.toArray
      item := item.mergeObj (Json.mkObj [("kind", Json.str "inductive"), ("constructors", toJson (d.ctors.map Name.toString))])
    | .ctorInfo _ => item := item.mergeObj (Json.mkObj [("kind", Json.str "constructor")])
    | .thmInfo _ => item := item.mergeObj (Json.mkObj [("kind", Json.str "theorem-type")])
    | .axiomInfo _ => item := item.mergeObj (Json.mkObj [("kind", Json.str "axiom-type")])
    | .opaqueInfo _ => item := item.mergeObj (Json.mkObj [("kind", Json.str "opaque-type")])
    | _ => item := item.mergeObj (Json.mkObj [("kind", Json.str "declaration-type")])
    dependencies := dependencies.push item
  return Json.mkObj [("encoding", Json.str "closed-expression-v1"),
    ("universe_parameters", toJson info.levelParams.length),
    ("type", contractExpr info.levelParams info.type), ("dependencies", Json.arr dependencies)]

/-- Strip metadata and return the head constant of `e`, if any. -/
def headConst? (e : Expr) : Option Name :=
  match e.consumeMData.getAppFn.consumeMData with
  | .const n _ => some n
  | _ => none

/-- Peel `Not` and `Exists` wrappers. Returns the wrappers (outermost first)
and the head constant of the innermost proposition. -/
partial def peel (e : Expr) (acc : Array String) : MetaM (Array String × Option Name) := do
  let e := e.consumeMData
  if e.isAppOfArity ``Not 1 then
    peel e.appArg! (acc.push "Not")
  else if e.isAppOfArity ``Exists 2 then
    match e.appArg!.consumeMData with
    | .lam n ty body bi =>
      withLocalDecl n bi ty fun x => peel (body.instantiate1 x) (acc.push "Exists")
    | _ => return (acc.push "Exists", none)
  else
    return (acc, headConst? e)

def nameJson : Option Name → Json
  | some n => Json.str n.toString
  | none => Json.null

/-- Describe one type: its sort class, raw head, peeled wrappers and core head. -/
def describeType (ty : Expr) : MetaM Json := do
  let ty ← instantiateMVars ty
  let sort ← whnf (← inferType ty)
  let isProp := sort.isProp
  let (wrappers, core) ← peel ty #[]
  let pp ← ppExpr ty
  return Json.mkObj [
    ("prop", Json.bool isProp),
    ("head", nameJson (headConst? ty)),
    ("wrappers", toJson wrappers),
    ("core_head", nameJson core),
    ("type", Json.str (toString pp))
  ]

def isBundle (prefixes : Array String) (e : Expr) : Bool :=
  match headConst? e with
  | some n => prefixes.any fun p => p.isPrefixOf n.toString
  | none => false

/-- Split a right-nested conjunction into its conjuncts. -/
partial def splitAnd (e : Expr) : Array Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``And 2 then splitAnd e.appFn!.appArg! ++ splitAnd e.appArg! else #[e]

/-- Unfold the head definition of `e` exactly one step and beta-reduce. -/
def unfoldOnce (e : Expr) : MetaM (Option Expr) := do
  match ← unfoldDefinition? e.consumeMData with
  | some e' => return some (← instantiateMVars e').headBeta
  | none => return none

/-- The conjuncts of a theory bundle, one unfolding step deep. -/
def bundleConjuncts (e : Expr) : MetaM (Option (Array Expr)) := do
  return (← unfoldOnce e).map splitAnd

/-- Open leading `∃` binders and continue with the body. -/
partial def openExists (e : Expr) (k : Expr → MetaM Json) : MetaM Json := do
  let e := e.consumeMData
  if e.isAppOfArity ``Exists 2 then
    match e.appArg!.consumeMData with
    | .lam n ty body bi => withLocalDecl n bi ty fun x => openExists (body.instantiate1 x) k
    | _ => k e
  else k e

def describeConjuncts (cs : Array Expr) : MetaM Json := do
  return Json.arr (← cs.mapM describeType)

/-- Bundle description of a hypothesis type, if its head is a theory definition. -/
def hypothesisBundle (prefixes : Array String) (ty : Expr) : MetaM (Option Json) := do
  if !isBundle prefixes ty then return none
  match ← bundleConjuncts ty with
  | some cs => return some (← describeConjuncts cs)
  | none => return some (Json.str "cannot unfold")

/-- Commitments of a result type whose head is a theory definition. -/
def resultBundle (prefixes : Array String) (ty : Expr) : MetaM (Option Json) := do
  if !isBundle prefixes ty then return none
  let some body ← unfoldOnce ty | return some (Json.str "cannot unfold")
  let items ← openExists body fun inner => do
    let mut out : Array Expr := #[]
    for c in splitAnd inner do
      if isBundle prefixes c then
        match ← bundleConjuncts c with
        | some cs => out := out ++ cs
        | none => out := out.push c
      else
        out := out.push c
    describeConjuncts out
  return some items

/-- Sense constants reached from `e` (see the module docstring). -/
def senseConstants (senses : NameSet) (e : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let mut pending := e.getUsedConstants
  let mut visited : NameSet := {}
  let mut found : Array Name := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if visited.contains n then continue
    visited := visited.insert n
    if senses.contains n then
      found := found.push n
      continue
    if !("TruthCore.".isPrefixOf n.toString) then continue
    if let some (.defnInfo d) := env.find? n then
      pending := pending ++ d.value.getUsedConstants
  return found.qsort (fun a b => a.toString < b.toString)

def sensesJson (senses : NameSet) (e : Expr) : MetaM Json := do
  return toJson ((← senseConstants senses e).map Name.toString)

/-- The constant `n` is an alias of: a definition whose eta-reduced value is a
bare constant is followed (at most `fuel` steps). -/
def aliasOf (env : Environment) : Nat → Name → Name
  | 0, n => n
  | fuel + 1, n =>
    match env.find? n with
    | some (.defnInfo d) =>
      match d.value.eta.consumeMData with
      | .const m _ => aliasOf env fuel m
      | _ => n
    | _ => n

def describeTheorem (prefixes : Array String) (contracts : Array String) (senses : NameSet)
    (senseTheorems : Array String) (thm : Name) : MetaM Json := do
  let some info := (← getEnv).find? thm
    | return Json.mkObj [("theorem", Json.str thm.toString), ("error", Json.str "unknown constant")]
  forallTelescope info.type fun xs body => do
    let mut binders : Array Json := #[]
    for x in xs do
      let decl ← x.fvarId!.getDecl
      let mut d ← describeType decl.type
      if ← isProp decl.type then
        if let some b ← hypothesisBundle prefixes decl.type then
          d := d.mergeObj (Json.mkObj [("bundle", b)])
      if senseTheorems.contains thm.toString then
        d := d.mergeObj (Json.mkObj [("senses", ← sensesJson senses decl.type)])
      binders := binders.push (d.mergeObj (Json.mkObj [("name", Json.str decl.userName.eraseMacroScopes.toString)]))
    let mut result ← describeType body
    if senseTheorems.contains thm.toString then
      result := result.mergeObj (Json.mkObj [("senses", ← sensesJson senses body)])
    if let some b ← resultBundle prefixes body then
      result := result.mergeObj (Json.mkObj [("bundle", b)])
    let mut out := Json.mkObj [
      ("theorem", Json.str thm.toString),
      ("binders", Json.arr binders),
      ("result", result)
    ]
    if contracts.contains thm.toString then
      out := out.mergeObj (Json.mkObj [("expression_contract", ← expressionContract info)])
    return out

/-- Sorted names of the constants `e` mentions (syntactic, nothing unfolded). -/
def usedConstantsJson (e : Expr) : Json :=
  toJson ((e.getUsedConstants.map Name.toString).qsort (· < ·))

/-- Peel leading `∃` binders: their number, how many of them occur in the
rest of the proposition, and the description of the innermost matrix. -/
partial def peelExists (e : Expr) : MetaM (Nat × Nat × Json) := do
  let e := e.consumeMData
  if e.isAppOfArity ``Exists 2 then
    match e.appArg!.consumeMData with
    | .lam n ty body bi =>
      let used := if body.hasLooseBVar 0 then 1 else 0
      withLocalDecl n bi ty fun x => do
        let (count, occurring, matrix) ← peelExists (body.instantiate1 x)
        return (count + 1, occurring + used, matrix)
    | _ => return (0, 0, Json.null)
  else
    return (0, 0, Json.mkObj [("head", nameJson (headConst? e)),
      ("used_constants", usedConstantsJson e)])

/-- One side of a restating lemma's body. -/
def describeSide (e : Expr) : MetaM Json := do
  let e ← instantiateMVars e
  let (count, occurring, matrix) ← peelExists e
  return Json.mkObj [
    ("head", nameJson (headConst? e)),
    ("used_constants", usedConstantsJson e),
    ("exists_binders", toJson count),
    ("exists_used", toJson occurring),
    ("matrix", matrix),
    ("type", Json.str (toString (← ppExpr e)))
  ]

/-- Whether the declaration `d` concludes `target` once its trailing binders
(as many as `d` has beyond `target`'s own) are metavariables. -/
def describeDischarger (target : Expr) (d : Name) : MetaM Json := do
  let some info := (← getEnv).find? d
    | return Json.mkObj [("declaration", Json.str d.toString), ("error", Json.str "unknown constant")]
  let axioms ← collectAxioms d
  let levels ← info.levelParams.mapM fun _ => mkFreshLevelMVar
  let dType := info.instantiateTypeLevelParams levels
  let nTarget ← forallTelescope target fun ys _ => pure ys.size
  let nDischarger ← forallTelescope dType fun ys _ => pure ys.size
  let base := Json.mkObj [("declaration", Json.str d.toString),
    ("axioms", toJson (axioms.map Name.toString))]
  if nDischarger < nTarget then
    return base.mergeObj (Json.mkObj [("matches", Json.bool false)])
  let (mvars, _, conclusion) ← forallMetaBoundedTelescope dType (nDischarger - nTarget)
  let unified ← isDefEq conclusion target
  let mut remaining : Array Json := #[]
  for m in mvars do
    let ty ← instantiateMVars (← inferType m)
    if !(← m.mvarId!.isAssigned) && (← isProp ty) then
      remaining := remaining.push (Json.str (toString (← ppExpr ty)))
  return base.mergeObj (Json.mkObj [("matches", Json.bool unified),
    ("remaining_hypotheses", Json.arr remaining)])

/-- Describe a restating lemma (see the module docstring). -/
def describeRestating (lemma : Name) (dischargers : List (String × Name)) : MetaM Json := do
  let some info := (← getEnv).find? lemma
    | return Json.mkObj [("restating_lemma", Json.str lemma.toString),
        ("error", Json.str "unknown constant")]
  let kind := match info with
    | .thmInfo _ => "theorem"
    | .defnInfo _ => "definition"
    | .axiomInfo _ => "axiom"
    | .opaqueInfo _ => "opaque"
    | _ => "other"
  let axioms ← collectAxioms lemma
  forallTelescope info.type fun xs body => do
    let mut binders : Array Json := #[]
    let mut discharged : Array (String × Json) := #[]
    for x in xs do
      let decl ← x.fvarId!.getDecl
      let name := decl.userName.eraseMacroScopes.toString
      let ty ← instantiateMVars decl.type
      let prop ← isProp ty
      let (_, core) ← peel ty #[]
      let mut d := Json.mkObj [("name", Json.str name), ("prop", Json.bool prop),
        ("head", nameJson (headConst? ty)), ("core_head", nameJson core)]
      if prop then
        d := d.mergeObj (Json.mkObj [("type", Json.str (toString (← ppExpr ty)))])
        for (hypothesis, discharger) in dischargers do
          if hypothesis == name then
            let described ← describeDischarger ty discharger
            discharged := discharged.push (hypothesis, described)
      binders := binders.push d
    let body ← instantiateMVars body
    let b := body.consumeMData
    let shape ← if b.isAppOfArity ``Iff 2 then do
        let left ← describeSide b.appFn!.appArg!
        let right ← describeSide b.appArg!
        pure (Json.mkObj [("body_head", Json.str "Iff"), ("sides", Json.arr #[left, right])])
      else do
        let side ← describeSide body
        pure (Json.mkObj [("body_head", nameJson (headConst? body)), ("side", side)])
    return (Json.mkObj [("restating_lemma", Json.str lemma.toString),
      ("kind", Json.str kind), ("axioms", toJson (axioms.map Name.toString)),
      ("binders", Json.arr binders), ("dischargers", Json.mkObj discharged.toList)]).mergeObj shape

/-- The `restating` input entries: lemma names with their dischargers. -/
def restatingInput (input : Json) : Except String (Array (Name × List (String × Name))) := do
  let items := (input.getObjValAs? (Array Json) "restating").toOption.getD #[]
  items.mapM fun item => do
    let lemma ← item.getObjValAs? String "lemma"
    let pairs := (item.getObjValAs? (Array (Array String)) "dischargers").toOption.getD #[]
    let dischargers := pairs.toList.filterMap fun pair =>
      match pair.toList with
      | [hypothesis, d] => some (hypothesis, d.toName)
      | _ => none
    return (lemma.toName, dischargers)

unsafe def main (args : List String) : IO UInt32 := do
  let [path] := args
    | IO.eprintln "usage: lean --run scripts/BindTypes.lean <input.json>"; return 2
  let input ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let modules ← IO.ofExcept (input.getObjValAs? (Array String) "modules")
  let theorems ← IO.ofExcept (input.getObjValAs? (Array String) "theorems")
  let prefixes := (input.getObjValAs? (Array String) "bundle_prefixes").toOption.getD #[]
  let contracts := (input.getObjValAs? (Array String) "contract_theorems").toOption.getD #[]
  let senseNames := ((input.getObjValAs? (Array String) "sense_constants").toOption.getD #[]).map String.toName
  let senseTheorems := (input.getObjValAs? (Array String) "sense_theorems").toOption.getD #[]
  let senses : NameSet := senseNames.foldl (fun s n => s.insert n) {}
  let restating ← IO.ofExcept (restatingInput input)
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (modules.map fun m => { module := m.toName }) {}
    (trustLevel := 1024) (loadExts := true)
  let ctx : Core.Context := { fileName := "<bind-types>", fileMap := default, maxHeartbeats := 0 }
  let state : Core.State := { env }
  let (out, _) ← (MetaM.run' (theorems.mapM fun t =>
    describeTheorem prefixes contracts senses senseTheorems t.toName)).toIO ctx state
  let (restated, _) ← (MetaM.run' (restating.mapM fun (lemma, dischargers) =>
    describeRestating lemma dischargers)).toIO ctx state
  let mut out := out ++ restated
  if !senseNames.isEmpty then
    let aliases := senseNames.toList.filterMap fun n =>
      if env.contains n then some (n.toString, Json.str (aliasOf env 32 n).toString) else none
    out := out.push (Json.mkObj [("sense_aliases", Json.mkObj aliases)])
  IO.println (Json.arr out).compress
  return 0
