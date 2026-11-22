import Lean
import Duper
/-!
Proof search for `truth discover` (docs/discover.md, `truth/src/discover.rs`).

`truth discover` does not run this file on its own: it writes a scratch file
that imports the statements' modules and `Duper`, then this file's body (its
own `import` lines are hoisted), then the `prove_sweep_probe` tactic of
`truth prove-sweep`, then one command per target:

    #discover "label" HEARTBEATS "ZIPPERPOSITION" Target from P₁ … Pₙ

The command builds the goal

    ∀ binders, P₁ args → … → Pₙ args → Target args

over the target's binders. Each premise declaration is applied to an
in-scope binder of the same name and definitionally equal type (an instance
binder by type, or by instance synthesis). A premise binder that matches none
becomes a new outer binder (renamed when its name is taken): the goal stays
universally quantified over every parameter, as a result theorem's binders
are. No premise binder is ever generalized inside a hypothesis, and nothing
but the named statement declarations becomes a hypothesis.

Search. The goal's hypotheses and conclusion are delta-expanded through every
project (`TruthCore.`) definition whose type ends in `Prop` and that is not a
projection or instance, transitively; this is definitional, so the kernel
accepts a proof of the expanded goal for the original one. `duper [*]` runs
under `maxHeartbeats` HEARTBEATS (thousands). When ZIPPERPOSITION names an
executable, lean-auto is tried next with Zipperposition as premise selector
(`auto.tptp.premiseSelection`) and Duper as its native prover, so its proof
is again reconstructed in Lean and kernel-checked; the external prover is
never trusted (`auto.tptp.trust` stays false). Every closed attempt is added
as a kernel-checked auxiliary theorem and its axioms are collected.

Per target the command reports, as one `DISCOVER-JSON` info line:

* `alone`: whether the target follows from no premise (a theorem of its
  vocabulary);
* `closed`: whether all premises together prove it, and by which prover;
* `minimal`: the premises the proof uses, then pruned by deleting each in
  turn and searching again (Duper only), with the outcome of each deletion;
* `vacuous`: whether `False` follows from the minimal premises (an
  incompatibility, never support);
* `probe`: whether the minimal goal closes by one premise application
  (`prove_sweep_probe`, the transcription heuristic of `truth prove-sweep`);
* `signature`, `unfold`: the minimal theorem's binders and statement, and the
  definitions to delta-expand, from which `truth discover` writes the
  certification file and the Solution draft.

Every outcome is a search result. `truth discover` re-elaborates the rendered
theorem text in a separate Lean run and checks its axioms before it reports a
discovery; a failed search is unresolved, never a refutation.
-/
open Lean Elab Command Term Meta

namespace Discover

@[rebind Auto.Native.solverFunc]
meta def duperNative (lemmas : Auto.NativeInterface Auto.Lemma) : MetaM Expr := do
  let (formulas, extraFormulas) ← Duper.autoLemmasToFormulas lemmas.valids
  let formulas := formulas.map (fun f => (f.1, f.2.1, f.2.2.1, f.2.2.2, none))
  let extraFormulas := extraFormulas.map (fun f => (f.1, f.2.1, f.2.2.1, f.2.2.2, none))
  Duper.runDuperPortfolioMode formulas extraFormulas .none
    { portfolioMode := true, portfolioInstance := none, inhabitationReasoning := none,
      preprocessing := Duper.PreprocessingOption.NoPreprocessing,
      includeExpensiveRules := none, selFunction := none } .none

/-- A name not used by any binder in `xs`: `n`, else `n_2`, `n_3`, … -/
def freshUserName (xs : Array Expr) (n : Name) : MetaM Name := do
  let base := n.eraseMacroScopes
  let base := if base.isAnonymous then `x else base
  let used ← xs.mapM fun x => x.fvarId!.getUserName
  if !used.contains base then return base
  let mut i := 2
  while used.contains (base.appendAfter s!"_{i}") do i := i + 1
  return base.appendAfter s!"_{i}"

/-! ### Binding policy

Every outer binder remembers its origin: the declaration and binder it came
from, that declaration's module, and the sense its parameter is tagged with
(`senses[].lean_parameters` of a disambiguation, passed in by `truth
discover`). A premise binder is identified with an outer binder of
definitionally equal type when

* it is an instance: by type, or by synthesis;
* otherwise (a carrier `B : Type`, a structure bundle such as
  `History W B T`, a predicate, relation, function or element): same name
  *and* both declared in the same module (that module's authored convention),
  or both tagged with the same sense id *as whole binders*.

A tag with fixed arguments (`CausesIn _ _ esse`, key `sense|_ _ esse`, see
`tag_key` in `truth/src/discover.rs`) describes only that partial application,
not the binder at every argument: two such binders are never identified by
their tags, since that would equate the full relations outside the tagged
slice, an identification no record states. They stay separate outer binders
(still identified by the same-module name convention when that applies); a
connection between their tagged slices needs an explicit bridge premise.

Nothing is identified by name across modules as such. One fallback, which the
configuration can switch off (`"strict_domains": true`): a carrier or
structure bundle with the same name and type in another module is identified
and reported in `domain_identified_by_name`, because without it no
cross-module goal can be stated until carriers are tagged. `truth discover`
keeps such goals out of spec drafts and lists them as needing a tag or a
bridge. Every other binder becomes a new outer binder, so the goal stays
universally quantified. -/

structure Origin where
  decl : Name
  binder : Name
  module : Name
  sense : Option String
  deriving Inhabited

/-- How one declaration's binder joined an outer binder: the declaration, its
binder name and module, the outer binder's origin, and whether the match was
the cross-module name fallback. A binder a declaration introduces is its own
member (`byName := false`). Every non-instance match is recorded, so a name
identification can be recomputed among any subset of declarations. -/
structure Membership where
  decl : Name
  binder : Name
  module : Name
  originDecl : Name
  originBinder : Name
  byName : Bool
  deriving Inhabited

def Membership.text (m : Membership) (decl binder : Name) : String :=
  s!"{m.decl}.{m.binder} = {decl}.{binder}"

def moduleOf (n : Name) : MetaM Name := do
  let env ← getEnv
  match env.getModuleIdxFor? n with
  | some idx => return env.header.moduleNames[idx.toNat]!
  | none => return .anonymous

def senseOf (tags : Array (Name × Name × String)) (decl binder : Name) : Option String :=
  (tags.find? fun (d, b, _) => d == decl && b == binder.eraseMacroScopes).map (·.2.2)

/-- Whether a tag key names the whole binder (no fixed arguments). A
partial-application key contains `|` (`tag_key` in `truth/src/discover.rs`). -/
def wholeBinderTag (key : String) : Bool := !key.contains '|'

def isStructureType (d : Expr) : MetaM Bool := do
  let d ← whnfR d
  match d.getAppFn with
  | .const c _ => return isStructure (← getEnv) c
  | _ => return false

partial def bind (tags : Array (Name × Name × String)) (strict : Bool)
    (byName : IO.Ref (Array Membership)) (decl : Name) (module : Name)
    (xs : Array Expr) (origins : Array Origin) (e : Expr)
    (k : Array Expr → Array Origin → Expr → TermElabM α) : TermElabM α := do
  let ty ← instantiateMVars (← inferType e)
  match ty with
  | .forallE n d _ bi =>
    let sense := senseOf tags decl n
    let carrier := d.isSort
    let bundle ← isStructureType d
    for (x, o) in xs.zip origins do
      let xbi ← x.fvarId!.getBinderInfo
      let sameName := (← x.fvarId!.getUserName).eraseMacroScopes == n.eraseMacroScopes
      let authored := (sameName && o.module == module) || (sense.any wholeBinderTag && o.sense == sense)
      let fallback := !strict && (carrier || bundle) && sameName && !authored
      let allowed := if bi.isInstImplicit then xbi.isInstImplicit else authored || fallback
      if allowed then
        if ← isDefEq (← inferType x) d then
          unless bi.isInstImplicit do
            -- decl, binder, module, origin declaration and binder, by name
            let m : Membership := ⟨decl, n, module, o.decl, o.binder, fallback⟩
            byName.modify (·.push m)
          return ← bind tags strict byName decl module xs origins (mkApp e x) k
    if bi.isInstImplicit then
      if let some inst ← (try synthInstance? d catch _ => pure none) then
        return ← bind tags strict byName decl module xs origins (mkApp e inst) k
    let n' ← freshUserName xs n
    unless bi.isInstImplicit do
      let m : Membership := ⟨decl, n, module, decl, n, false⟩
      byName.modify (·.push m)
    withLocalDecl n' bi (← instantiateMVars d) fun y =>
      bind tags strict byName decl module (xs.push y) (origins.push { decl, binder := n, module, sense })
        (mkApp e y) k
  | _ => k xs origins e

/-- `bind` for every name in turn: the target first, then the premises. -/
partial def bindAll (tags : Array (Name × Name × String)) (strict : Bool)
    (byName : IO.Ref (Array Membership))
    (xs : Array Expr) (origins : Array Origin) (names : List Name) (acc : Array Expr)
    (k : Array Expr → Array Origin → Array Expr → TermElabM α) : TermElabM α := do
  match names with
  | [] => k xs origins acc
  | n :: rest =>
    let e ← mkConstWithFreshMVarLevels n
    bind tags strict byName n (← moduleOf n) xs origins e fun xs' os p =>
      bindAll tags strict byName xs' os rest (acc.push p) k

/-- The definitions a goal is normalized through: `delta`, the Prop-valued
ones, delta-expanded; `eqns`, the definitions of values (not propositions or
types), rewritten by their defining equations (`simp only`) after the delta
pass, so that a closed computed term such as `convergenceFormula 1 0 1 1`,
built by recursion, reaches the prover in constructor form (#1845). -/
structure Unfolding where
  delta : NameSet := {}
  eqns : NameSet := {}

/-- Project definitions reached transitively from `roots`, through the values
of the definitions collected: `TruthCore.` definitions, not projections,
instances, matchers or auxiliary recursors. One whose type ends in `Prop` is
delta-expanded; one whose type ends in a value type (`Formula Unit`, not a
`Sort`: `def Pred B := B → Prop` stays) is rewritten by its equations, which
evaluate it on constructor arguments only (`iterBox (n + 1) φ`) and unfold a
non-recursive one everywhere, both definitionally sound. -/
partial def unfoldSet (roots : Array Name) : MetaM Unfolding := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo := roots.toList
  let mut out : Unfolding := {}
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    unless (`TruthCore).isPrefixOf n do continue
    let some info := env.find? n | continue
    let .defnInfo d := info | continue
    if (env.getProjectionFnInfo? n).isSome then continue
    if (← isInstance n) then continue
    if n.isInternal then continue
    if isMatcherCore env n || isAuxRecursor env n || isNoConfusion env n then continue
    let isPred ← forallTelescopeReducing d.type fun _ body => return body.isProp
    let isValue ← forallTelescopeReducing d.type fun _ body => return !body.isSort
    if isPred then
      out := { out with delta := out.delta.insert n }
    else if isValue then
      out := { out with eqns := out.eqns.insert n }
    else continue
    for c in d.value.getUsedConstants do
      unless seen.contains c do todo := c :: todo
  return out

def expand (u : Unfolding) (e : Expr) : MetaM Expr := do
  deltaExpand (← instantiateMVars e) u.delta.contains

def identsOf (ns : NameSet) : Array Ident :=
  (ns.toArray.qsort Name.lt).map mkIdent

/-- `simp` arguments naming each definition of `ns` (its equations). -/
def simpArgs (ns : NameSet) : MetaM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :=
  (identsOf ns).mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)

/-- The fallback prover tactic over the delta-expanded goal, tried after the
plain prover fails when the goal reaches definitions of values
(`Unfolding.eqns`): `simp only` with their equations, then the prover.
Delta-expansion leaves `convergenceFormula 1 0 1 1` a closed but unevaluated
term that no prover reads; its equations evaluate it. The certification text
runs the same steps when this variant closed the goal (`proof_text` in
`truth/src/discover.rs`). -/
def proverTactic (u : Unfolding) (prover : TSyntax `tactic) : TermElabM (TSyntax `tactic) := do
  if u.eqns.isEmpty then return prover
  let eqs ← simpArgs u.eqns
  `(tactic| ((try simp only [$eqs,*] at *); all_goals ($prover:tactic)))

structure Proved where
  prover : String
  used : Array Nat
  axioms : Array Name

/-- Adds the closed proof as a theorem (synchronously, outside any search
budget) and returns its axioms; `none` when the kernel rejects it. -/
def kernelCheck (prover : String) (used : Array Nat) (stmt value : Expr) :
    TermElabM (Option Proved) := do
  let check : TermElabM Proved := do
    let aux ← mkFreshUserName `_discover
    withOptions (fun o => o.set `Elab.async false |>.set `maxHeartbeats (0 : Nat)) <|
      withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) <|
        addDecl (.thmDecl { name := aux, levelParams := [], type := stmt, value })
    let axioms ← collectAxioms aux
    return { prover, used, axioms := axioms.qsort Name.lt }
  tryCatchRuntimeEx (some <$> check) (fun _ => pure none)

/-- Tries to prove `concl` from `hyps` (indices into the premise list) in the
context of `xs`, with the expanded types; returns the prover, the hypotheses the
kernel-checked proof uses, and its axioms. -/
def prove (xs : Array Expr) (hyps : Array (Nat × Expr)) (concl : Expr) (u : Unfolding)
    (heartbeats : Nat) (zip : String) (duperOnly : Bool := false) : TermElabM (Option Proved) := do
  let concl' ← expand u concl
  let hypTys ← hyps.mapM fun (i, h) => return (i, ← expand u h)
  -- Each prover runs plain first; the variant that evaluates value
  -- definitions by their equations (`proverTactic`) is only a fallback, so a
  -- proof that treats such a definition as an opaque symbol is kept, and the
  -- name records which variant closed the goal (`+equations`).
  let duper ← `(tactic| duper [*])
  let mut provers : Array (String × Syntax) := #[("duper", duper)]
  if !u.eqns.isEmpty then
    provers := provers.push ("duper+equations", ← proverTactic u duper)
  if !duperOnly && !zip.isEmpty then
    let auto ← `(tactic| auto)
    provers := provers.push ("auto+zipperposition", auto)
    if !u.eqns.isEmpty then
      provers := provers.push ("auto+zipperposition+equations", ← proverTactic u auto)
  for (name, tac) in provers do
    let saved ← saveState
    let result ← tryCatchRuntimeEx (do
        let opts := (← getOptions)
          |>.set `maxHeartbeats heartbeats
          |>.set `auto.tptp (!name.startsWith "duper")
          |>.set `auto.tptp.premiseSelection true
          |>.set `auto.tptp.trust false
          |>.set `auto.native true
          |>.set `auto.smt false
          |>.set `auto.tptp.zipperposition.useDefault false
          |>.set `auto.tptp.zipperposition.customPath zip
        withOptions (fun _ => opts) <| withCurrHeartbeats <| withTheReader Core.Context
            (fun c => { c with maxHeartbeats := heartbeats * 1000 }) do
          let descrs := hypTys.map fun (i, t) => (Name.mkSimple s!"h{i}", fun _ => pure t)
          withLocalDeclsD descrs fun hs => do
            let mvar ← mkFreshExprMVar concl'
            let remaining ← Tactic.run mvar.mvarId! (Tactic.evalTactic tac)
            synthesizeSyntheticMVarsNoPostponing
            let proof ← instantiateMVars mvar
            if !remaining.isEmpty || proof.hasMVar || proof.hasSorry then return none
            let used := (hs.zip hypTys).filterMap fun (h, (i, _)) =>
              if proof.containsFVar h.fvarId! then some i else none
            -- Kernel check of the closed statement with the *original* types.
            let origHyps ← hyps.mapM fun (_, h) => instantiateMVars h
            let stmt ← mkForallFVars xs (← origHyps.foldrM (fun h acc => mkArrow h acc) concl)
            let value ← mkLambdaFVars xs (← mkLambdaFVars hs proof)
            let stmt ← instantiateMVars stmt
            if stmt.hasMVar then return none
            return some (used, stmt, ← instantiateMVars value))
      (fun _ => pure none)
    -- The kernel check runs outside the search budget, synchronously, so its
    -- axioms are those of the finished theorem.
    let result ← match result with
      | none => pure none
      | some (used, stmt, value) => kernelCheck name used stmt value
    saved.restore (restoreInfo := true)
    if let some p := result then return some p
  return none

/-- The binders among `xs` that `es` mention, with their dependencies, and
the local context without the others (their local instances dropped too). -/
def ownContext (xs : Array Expr) (es : Array Expr) :
    MetaM (Array Expr × LocalContext × LocalInstances) := do
  let mut keep : FVarIdSet := {}
  for e in es do
    for f in (collectFVars {} (← instantiateMVars e)).fvarIds do keep := keep.insert f
  for x in xs.reverse do
    if keep.contains x.fvarId! then
      for f in (collectFVars {} (← instantiateMVars (← inferType x))).fvarIds do
        keep := keep.insert f
  let drop := (xs.filter (!keep.contains ·.fvarId!)).map (·.fvarId!)
  let lctx := drop.foldl (·.erase ·) (← getLCtx)
  let insts := (← getLocalInstances).filter fun i => !drop.contains i.fvar.fvarId!
  return (xs.filter (keep.contains ·.fvarId!), lctx, insts)

/-- `prove` over the binders that the hypotheses and the conclusion mention
only. A contradiction (`False`) must not borrow an element or instance that
only another statement (the target, a dropped premise) introduces: `∀ y : B,
R y ∧ ¬ R y` is refuted only given some `x : B`, and is satisfiable over an
empty `B`. -/
def proveOwn (xs : Array Expr) (hyps : Array (Nat × Expr)) (concl : Expr) (u : Unfolding)
    (heartbeats : Nat) : TermElabM (Option Proved) := do
  let (xs', lctx, insts) ← ownContext xs ((hyps.map (·.2)).push concl)
  withLCtx lctx insts <| prove xs' hyps concl u heartbeats "" (duperOnly := true)

/-- A literal negation in an inconsistent core: indices `(i, j)` of two core
members where hypothesis `j` is definitionally (delta, default transparency)
the negation of hypothesis `i`, as `RevelationCapabilityRejected σ :=
¬ RevelationPossibleAndRecognizable σ` is of its rival. Such a core is a P/¬P
pair, true by construction, not a discovered incompatibility (#1819). Only
definitional unfolding counts: a contradictory pair that takes logic to
recognize (`∀ x, F x → G x` against `∃ x, F x ∧ ¬ G x`) is not literal. -/
def literalNegation (hyps : Array (Nat × Expr)) (core : Array Nat) (heartbeats : Nat) :
    TermElabM (Option (Nat × Nat)) := do
  let members := hyps.filter fun (i, _) => core.contains i
  for (i, hi) in members do
    for (j, hj) in members do
      if i == j then continue
      let same ← tryCatchRuntimeEx (withoutModifyingState <|
          withTheReader Core.Context (fun c => { c with maxHeartbeats := heartbeats * 1000 }) <|
            withCurrHeartbeats <| withTransparency .default <| isDefEq hj (mkNot hi))
        (fun _ => pure false)
      if same then return some (i, j)
  return none

/-- Deletion minimization: drop each remaining premise in turn and keep it
dropped when Duper still proves the goal. -/
def minimize (xs : Array Expr) (hyps : Array (Nat × Expr)) (concl : Expr) (u : Unfolding)
    (heartbeats : Nat) (start : Proved) (own : Bool := false) :
    TermElabM (Array Nat × Array Json × Proved) := do
  let mut current := start.used
  let mut best := start
  let mut log : Array Json := #[]
  for i in start.used do
    unless current.contains i do continue
    let without := current.filter (· != i)
    let sub := hyps.filter fun (j, _) => without.contains j
    let attempt ← if own then proveOwn xs sub concl u heartbeats
      else prove xs sub concl u heartbeats "" (duperOnly := true)
    match attempt with
    | some p =>
      log := log.push (Json.mkObj [("premise", toJson i), ("outcome", "dropped")])
      current := p.used
      best := p
    | none =>
      log := log.push (Json.mkObj [("premise", toJson i), ("outcome", "kept")])
  return (current, log, best)

/-- The theorem signature text: binders, hypotheses `h₁ …` and the conclusion. -/
def signature (xs : Array Expr) (hyps : Array (Nat × Expr)) (concl : Expr) : MetaM String := do
  -- Keep only the binders the statement mentions, with their dependencies.
  let mut keep : FVarIdSet := {}
  for e in hyps.map (·.2) |>.push concl do
    for f in (collectFVars {} (← instantiateMVars e)).fvarIds do keep := keep.insert f
  for x in xs.reverse do
    if keep.contains x.fvarId! then
      for f in (collectFVars {} (← instantiateMVars (← inferType x))).fvarIds do
        keep := keep.insert f
  let xs := xs.filter (keep.contains ·.fvarId!)
  withOptions (fun o => o |>.set `pp.fullNames true |>.set `pp.fieldNotation false
      |>.set `pp.funBinderTypes true |>.set `pp.piBinderTypes true
      |>.set `pp.mvars false |>.set `format.width (100000 : Nat)
      |>.set `pp.unicode.fun true) do
    let mut parts : Array String := #[]
    for x in xs do
      let decl ← x.fvarId!.getDecl
      let ty := toString (← ppExpr (← instantiateMVars decl.type))
      let n := decl.userName.eraseMacroScopes
      parts := parts.push <| match decl.binderInfo with
        | .instImplicit => s!"[{ty}]"
        | .implicit | .strictImplicit => "{" ++ s!"{n} : {ty}" ++ "}"
        | .default => s!"({n} : {ty})"
    for (i, h) in hyps do
      parts := parts.push s!"(h{i} : {← ppExpr (← instantiateMVars h)})"
    return s!"{" ".intercalate parts.toList} : {← ppExpr (← instantiateMVars concl)}"

def jsonNames (ns : Array Name) : Json := Json.arr (ns.map (Json.str ·.toString))

def proved (p : Option Proved) : Json :=
  match p with
  | none => Json.null
  | some p => Json.mkObj [("prover", Json.str p.prover), ("used", toJson p.used),
      ("axioms", jsonNames p.axioms)]

/-! ### One-point witnesses

A witness interprets every binder: each carrier (`B : Type`) as `Unit`, each
predicate-valued binder (`B → … → Prop`, also a structure field) as a constant
`True` or `False` (its *slot*), each structure binder by its constructor on
interpreted fields, each instance by synthesis and every other value by
`default`. `witness` tries the slot patterns all-`False`, all-`True` and each
single flip of those, and closes the instantiated goal by `simp`/`decide`. A
closed instance is kernel-checked (`addDecl`). It is a model of the stated
formal vocabulary only, and may be trivial (every antecedent empty). -/

/-- The interpretation of a type under the slot assignment; `slot` counts the
predicate slots used so far. -/
partial def interp (pattern : Nat → Bool) (ty : Expr) : StateT Nat MetaM Expr := do
  let ty ← whnfR (← instantiateMVars ty)
  if ty.isSort then return Lean.mkConst ``Unit
  -- Predicate-valued: a constant truth value.
  let isPred ← forallTelescopeReducing ty fun _ b => return b.isProp
  if isPred && ty.isForall then
    let i ← modifyGet fun s => (s, s + 1)
    let c := if pattern i then Lean.mkConst ``True else Lean.mkConst ``False
    return ← forallTelescopeReducing ty fun ys _ => mkLambdaFVars ys c
  if ty.isProp then
    let i ← modifyGet fun s => (s, s + 1)
    return if pattern i then Lean.mkConst ``True else Lean.mkConst ``False
  -- Structures: the constructor on interpreted fields.
  let env ← getEnv
  if let .const sName _ := ty.getAppFn then
    if isStructure env sName then
      let ctor := getStructureCtor env sName
      let params := ty.getAppArgs
      let mut e := mkAppN (mkConst ctor.name ty.getAppFn.constLevels!) params
      for _ in [0:ctor.numFields] do
        let .forallE _ d _ _ ← whnf (← inferType e) | throwError "constructor arity"
        e := mkApp e (← interp pattern d)
      return e
  -- Functions into values: constant default.
  if ty.isForall then
    return ← forallTelescopeReducing ty fun ys b => do
      mkLambdaFVars ys (← interp pattern b)
  if let some inst ← (try synthInstance? (← mkAppM ``Inhabited #[ty]) catch _ => pure none) then
    return ← mkAppOptM ``Inhabited.default #[ty, inst]
  throwError "no interpretation for {ty}"

/-- Instantiates the binders `xs` under `pattern`; instance binders by synthesis. -/
def instantiateBinders (xs : Array Expr) (pattern : Nat → Bool) : MetaM (Array Expr × Nat) := do
  let mut vals : Array Expr := #[]
  let mut slots := 0
  for x in xs do
    let ty := (← inferType x).replaceFVars (xs.extract 0 vals.size) vals
    if (← x.fvarId!.getBinderInfo).isInstImplicit then
      vals := vals.push (← synthInstance ty)
    else
      let (v, s) ← (interp pattern ty).run slots
      slots := s
      vals := vals.push v
  return (vals, slots)

/-- The axioms a reported proof or model may rest on (`ALLOWED_AXIOMS` in
`truth/src/discover.rs`, docs/axiom-policy.md). -/
def allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- A one-point model of `goals` (conjoined) over the binders `xs`: the slot
pattern that closes it, if any. -/
def witness (xs : Array Expr) (goals : Array Expr) (u : Unfolding) (heartbeats : Nat) :
    TermElabM (Option String) := do
  let (_, n) ← try instantiateBinders xs (fun _ => false) catch _ => return none
  let mut patterns : Array (String × (Nat → Bool)) := #[("all False", fun _ => false), ("all True", fun _ => true)]
  for i in [0:n] do
    patterns := patterns.push (s!"slot {i} True, rest False", fun j => j == i)
    patterns := patterns.push (s!"slot {i} False, rest True", fun j => j != i)
  for (label, pattern) in patterns do
    let saved ← saveState
    let ok ← tryCatchRuntimeEx (do
        withOptions (fun o => o.set `maxHeartbeats heartbeats) <| withCurrHeartbeats <|
          withTheReader Core.Context (fun c => { c with maxHeartbeats := heartbeats * 1000 }) do
            let (vals, _) ← instantiateBinders xs pattern
            let body := goals.foldr (fun g acc => mkAnd g acc) (Lean.mkConst ``True) |>.replaceFVars xs vals
            let body ← instantiateMVars (← expand u body)
            let mvar ← mkFreshExprMVar body
            -- Computed definitions evaluate by their equations (`Unfolding.eqns`).
            let eqs ← simpArgs u.eqns
            let tac ← `(tactic| first | (simp; done) | (simp [$eqs,*]; done) | decide | trivial | (simp_all; done) | (simp_all [$eqs,*]; done))
            let rest ← Tactic.run mvar.mvarId! (Tactic.evalTactic tac)
            let proof ← instantiateMVars mvar
            if !rest.isEmpty || proof.hasMVar || proof.hasSorry || proof.hasFVar then return false
            let aux ← mkFreshUserName `_discoverWitness
            withOptions (fun o => o.set `Elab.async false) <|
              addDecl (.thmDecl { name := aux, levelParams := [], type := body, value := proof })
            -- `simp` may close the goal by an imported lemma resting on `sorryAx`
            -- or another axiom: the model counts only within the allowance.
            let axioms ← collectAxioms aux
            return axioms.all allowedAxioms.contains)
      (fun _ => pure false)
    saved.restore (restoreInfo := true)
    if ok then return some label
  return none

/-- The name identifications among the declarations `kept`, recomputed from
the binder memberships: a kept declaration whose binder joined an outer binder
by the cross-module name fallback, while another kept declaration of a
different module shares that outer binder (by any rule: its origin, the
same-module convention, a sense tag or the fallback). The originating
declaration need not be kept: two retained declarations that share a binder
only through a dropped one still share it by name. -/
def keptIdentifications (all : Array Membership) (kept : Array Name) : Array String := Id.run do
  let mut out : Array String := #[]
  for m in all do
    unless m.byName && kept.contains m.decl do continue
    let partner := all.find? fun p => kept.contains p.decl && p.module != m.module &&
      p.originDecl == m.originDecl && p.originBinder == m.originBinder
    if let some p := partner then
      let t := m.text p.decl p.binder
      unless out.contains t do out := out.push t
  return out

/-! ### Missing bridges

When the premises do not prove the target, the gap may be that two
vocabularies are unconnected: the premises speak of a relation `p` (a binder or
a Prop-valued field of a structure binder, after delta-expansion) and the
conclusion of a relation `q`. Both directions are tried, pairs where each is
used on its side only first. For each such pair the command forms the
bridge

    ∀ a₁ … aₘ, p a₁ … aₘ → ∃ (unmatched bⱼ), q b₁ … bₙ

where each argument of `q` takes the first unused argument of `p` of the same
type, the others are existential, and (in the `fixed` variant, tried first,
as the weaker bridge) an unmatched argument of `p` whose type has exactly one
element binder in scope is fixed to it (`CausesIn c x esse`). A bridge is
reported when the premises with it prove the target and do not prove `False`.
It is a candidate proposition, a research question: never a premise of any
recorded argument until it is stated, reviewed and warranted. -/

/-- The predicate-valued atoms of a binder: itself, or its structure's
Prop-valued fields, with a display name. -/
def predicateAtoms (x : Expr) : MetaM (Array (String × Expr)) := do
  let ty ← whnfR (← inferType x)
  let name := (← x.fvarId!.getUserName).eraseMacroScopes.toString
  let isPred (t : Expr) : MetaM Bool :=
    forallTelescopeReducing t fun ys b => return !ys.isEmpty && b.isProp
  if ← isPred ty then return #[(name, x)]
  let env ← getEnv
  let .const c _ := ty.getAppFn | return #[]
  unless isStructure env c do return #[]
  let mut out := #[]
  for f in getStructureFields env c do
    let some proj := getProjFnForField? env c f | continue
    let some t ← (try some <$> mkAppM proj #[x] catch _ => pure none) | continue
    if ← isPred (← inferType t) then out := out.push (s!"{name}.{f}", t)
  return out

/-- Names every anonymous or inaccessible binder `x₁, x₂, …` for display. -/
partial def nameBinders (e : Expr) : StateM Nat Expr := do
  let fresh (n : Name) : StateM Nat Name := do
    if n.hasMacroScopes || n.isAnonymous then
      let i ← modifyGet fun s => (s, s + 1)
      return Name.mkSimple s!"x{i + 1}"
    return n
  match e with
  | .forallE n d b bi => return .forallE (← fresh n) (← nameBinders d) (← nameBinders b) bi
  | .lam n d b bi => return .lam (← fresh n) (← nameBinders d) (← nameBinders b) bi
  | .app f a => return .app (← nameBinders f) (← nameBinders a)
  | .mdata m b => return .mdata m (← nameBinders b)
  | _ => return e

/-- The unique element of `ty` among `elems`, if exactly one. -/
def uniqueElem (elems : Array (String × Expr)) (ty : Expr) : MetaM (Option (String × Expr)) := do
  let mut hits : Array (String × Expr) := #[]
  for (n, e) in elems do
    if ← isDefEq (← inferType e) ty then hits := hits.push (n, e)
  return if hits.size == 1 then some hits[0]! else none

/-- The bridge from relation `p` to relation `q`. In the `fix` variant every
argument of `p` whose type has exactly one element binder on `p`'s side is
fixed to it, and the matching argument of `q` to the element on `q`'s side
(or the same element). -/
def bridgeFor (p q : Expr) (pElems qElems : Array (String × Expr)) (fix : Bool) :
    MetaM (Option (Expr × Array String)) := do
  let pt ← inferType p
  let qt ← inferType q
  forallTelescopeReducing pt fun as _ =>
  forallTelescopeReducing qt fun bs _ => do
    let mut pArgs := as
    let mut fixedTo : Array (Option Expr) := Array.replicate as.size none
    let mut fixed : Array String := #[]
    if fix then
      for i in [0:as.size] do
        if let some (n, e) ← uniqueElem pElems (← inferType as[i]!) then
          pArgs := pArgs.set! i e
          fixedTo := fixedTo.set! i (some e)
          fixed := fixed.push n
      if fixed.isEmpty then return none
    let mut used := Array.replicate as.size false
    let mut qArgs : Array Expr := #[]
    let mut missing : Array Expr := #[]
    let mut linked := 0
    for b in bs do
      let bt ← inferType b
      let mut found : Option Nat := none
      for i in [0:as.size] do
        if !used[i]! && found.isNone then
          if ← isDefEq (← inferType as[i]!) bt then found := some i
      match found with
      | some i =>
        used := used.set! i true
        match fixedTo[i]! with
        | some e =>
          let v := (← uniqueElem qElems bt).map (·.2) |>.getD e
          qArgs := qArgs.push v
        | none => qArgs := qArgs.push as[i]!; linked := linked + 1
      | none => qArgs := qArgs.push b; missing := missing.push b
    if linked == 0 then return none
    let universal := (as.zip fixedTo).filterMap fun (a, f) => if f.isNone then some a else none
    let mut body := mkAppN q qArgs
    for b in missing.reverse do
      body ← mkAppM ``Exists #[← mkLambdaFVars #[b] body]
    let bridge ← mkForallFVars universal (← mkArrow (mkAppN p pArgs) body)
    if bridge.hasLooseBVars then return none
    let (bridge, _) := (nameBinders bridge).run 0
    return some (bridge, fixed)

/-- Whether `a` is `p` applied to further arguments (`p` a relation binder, or
a structure field applied to its binder). -/
def headedBy (p a : Expr) : Bool :=
  let pa := p.getAppArgs
  let aa := a.getAppArgs
  a.getAppFn == p.getAppFn && pa.size < aa.size &&
    (pa.zip (aa.extract 0 pa.size)).all fun (x, y) => x == y

/-- The conjuncts of `e` (`A ∧ B ∧ C` gives `A`, `B`, `C`). -/
partial def conjuncts (e : Expr) : Array Expr :=
  if e.isAppOfArity ``And 2 then conjuncts e.appFn!.appArg! ++ conjuncts e.appArg! else #[e]

/-! A target whose antecedent is a conjunction (`∀ g, Simple g → Perfect g → …
→ Q g`, or one hypothesis `A g ∧ B g`) invites bridges `∀ g, Simple g → R g`
that make one conjunct sufficient for what the whole conjunction is asked to
give. Such a bridge is formally a candidate but philosophically uninformative,
and each is stronger than the conjunctive bridge
`∀ g, Simple g → … → HasWill g → R g` over the same element. The conjunctive
builder matches each argument of `R` to the first unused antecedent element of
its type, so for an antecedent with several elements of one type it may not be
the weakening of a given single bridge, and it need not unlock every target a
single bridge does. The search therefore tries the conjunctive version first,
once per consequent relation (#1819); only when one passes are the
single-conjunct bridges dropped. Otherwise they are tried after the others and
reported as `single_conjunct` (demoted in the ranking). -/

/-- The relations heading the conjuncts of the expanded conclusion's antecedent
(at least two, else none), and the conjunctive bridges
`∀ elements, antecedents → ∃ unmatched, q args` for each premise relation `q`
outside the antecedent. -/
def conjunctiveBridges (c : Expr) (rel : Array (String × Expr)) (inH : Expr → Bool) :
    MetaM (Array String × Array (String × Expr)) :=
  forallTelescope c fun ys _ => do
    let mut props : Array Expr := #[]
    let mut elemYs : Array Expr := #[]
    for y in ys do
      if ← isProp (← inferType y) then props := props.push y else elemYs := elemYs.push y
    let mut atoms : Array Expr := #[]
    for y in props do
      atoms := atoms ++ conjuncts (← instantiateMVars (← inferType y))
    let ante := rel.filter fun (_, p) => atoms.any (headedBy p ·)
    if ante.size < 2 then return (#[], #[])
    let anteNames := ante.map (·.1)
    let mut out : Array (String × Expr) := #[]
    for (qn, q) in rel do
      if anteNames.contains qn || !inH q then continue
      let some bridge ← forallTelescopeReducing (← inferType q) fun bs _ => do
          let mut used := Array.replicate elemYs.size false
          let mut args : Array Expr := #[]
          let mut missing : Array Expr := #[]
          let mut linked := 0
          for b in bs do
            let bt ← inferType b
            let mut found : Option Nat := none
            for k in [0:elemYs.size] do
              if !used[k]! && found.isNone then
                if ← isDefEq (← inferType elemYs[k]!) bt then found := some k
            match found with
            | some k =>
              used := used.set! k true
              args := args.push elemYs[k]!
              linked := linked + 1
            | none =>
              args := args.push b
              missing := missing.push b
          if linked == 0 then return none
          let mut body := mkAppN q args
          for b in missing.reverse do
            body ← mkAppM ``Exists #[← mkLambdaFVars #[b] body]
          let bridge ← mkForallFVars ys body
          if bridge.hasLooseBVars then return none
          return some ((nameBinders bridge).run 0).1
        | continue
      out := out.push (qn, bridge)
    return (anteNames, out)

/-- The checks a candidate bridge must pass before it is reported (see
`missingBridges`); the report fields, or `none`. -/
def checkBridge (xs : Array Expr) (origins : Array Origin) (hyps : Array (Nat × Expr))
    (concl : Expr) (u : Unfolding) (heartbeats : Nat)
    (domains : Array Nat → Array Name → Array String) (bridge : Expr) (budget : Nat) :
    TermElabM (Option (List (String × Json))) := do
  let withBridge := hyps.push (1000, bridge)
  let some found ← prove xs withBridge concl u budget "" (duperOnly := true) | return none
  unless found.used.contains 1000 do return none
  -- Recheck over the reported statements' own binders: the search context
  -- also holds binders that unused candidates introduced (an element
  -- `x : B` of `Marker B x`), and a proof that borrows one would rest on a
  -- nonemptiness the report does not show. A binder that only the bridge
  -- mentions (a fixed argument) is kept and reported as `assumed_binders`.
  let usedHyps := withBridge.filter fun (i, _) => found.used.contains i
  let (ownXs, lctx, insts) ← ownContext xs ((usedHyps.map (·.2)).push concl)
  let (baseXs, _, _) ← ownContext xs (((usedHyps.filter (·.1 != 1000)).map (·.2)).push concl)
  let some proof ← withLCtx lctx insts <|
      prove ownXs usedHyps concl u budget "" (duperOnly := true) | return none
  unless proof.used.contains 1000 do return none
  unless proof.axioms.all allowedAxioms.contains do return none
  let bridgeOnly := ownXs.filter (!baseXs.contains ·)
  let assumed ← bridgeOnly.mapM fun x => do
    return (← x.fvarId!.getUserName).eraseMacroScopes.toString
  -- The declarations that introduced a bridge-only binder count as kept for
  -- the name identifications its domain rests on.
  let assumedDecls := (xs.zip origins).filterMap fun (x, o) =>
    if bridgeOnly.contains x then some o.decl else none
  -- A bridge that proves the target on its own merely restates it.
  if (← prove xs #[(1000, bridge)] concl u (max 2000 (heartbeats / 10)) ""
      (duperOnly := true)).isSome then return none
  if (← prove xs withBridge (Lean.mkConst ``False) u (max 2000 (heartbeats / 10)) ""
      (duperOnly := true)).isSome then return none
  let text ← withOptions (fun o => o |>.set `pp.fullNames true |>.set `pp.fieldNotation false
      |>.set `format.width (100000 : Nat)) do
    return toString (← ppExpr bridge)
  return some [("text", Json.str text), ("assumed_binders", toJson assumed),
    ("used", toJson (proof.used.filter (· != 1000))),
    ("domain_identified_by_name", toJson (domains (proof.used.filter (· != 1000)) assumedDecls))]

/-- At most this many conjunctive bridges are checked per goal, besides the
48 ordinary bridge candidates. -/
def maxConjunctive : Nat := 8

def missingBridges (xs : Array Expr) (origins : Array Origin) (_target : Name)
    (hyps : Array (Nat × Expr)) (concl : Expr) (u : Unfolding) (heartbeats : Nat)
    (domains : Array Nat → Array Name → Array String) :
    TermElabM (Array Json) := do
  -- The vocabulary the premises use and the vocabulary the conclusion uses,
  -- after delta-expansion: relations (binders, or Prop-valued fields of
  -- structure binders) and element binders (for fixed arguments).
  let hs ← hyps.mapM fun (_, h) => expand u h
  let c ← expand u concl
  let inH (e : Expr) : Bool := hs.any (e.occurs ·)
  let inC (e : Expr) : Bool := e.occurs c
  let mut rel : Array (String × Expr) := #[]
  let mut elems : Array (String × Expr) := #[]
  for (x, o) in xs.zip origins do
    let atoms := (← predicateAtoms x).map fun (n, e) => (s!"{o.decl}.{n}", e)
    rel := rel ++ atoms
    let ty ← whnfR (← inferType x)
    if atoms.isEmpty && !ty.isSort && !ty.isForall && !(← isStructureType ty) &&
        !(← x.fvarId!.getBinderInfo).isInstImplicit && !(← isProp ty) then
      elems := elems.push ((← x.fvarId!.getUserName).eraseMacroScopes.toString, x)
  -- The elements that occur together with a relation (in one hypothesis or the
  -- conclusion) are its candidates for a fixed argument.
  let exprs := hs.push c
  let near (r : Expr) : Array (String × Expr) :=
    elems.filter fun (_, x) => exprs.any fun e => r.occurs e && x.occurs e
  -- A conjunctive antecedent: its single-conjunct bridges are skipped, the
  -- conjunctive version is tried first.
  let (ante, conjunctive) ← conjunctiveBridges c rel inH
  -- Pairs of a premise relation and a conclusion relation; first those where
  -- each is used on its side only (the two vocabularies are unconnected).
  let mut first := #[]
  let mut later := #[]
  for (pn, p) in rel do
    unless inH p do continue
    for (qn, q) in rel do
      if pn == qn || !inC q then continue
      -- Both directions: the conclusion's antecedents may need the premises'
      -- vocabulary as much as the premises' consequents need the conclusion's.
      let pairs := #[((pn, p), (qn, q), near p, near q), ((qn, q), (pn, p), near q, near p)]
      if !inC p && !inH q then first := first ++ pairs else later := later ++ pairs
  -- One conjunct of a conjunctive antecedent alone, made sufficient.
  let single (a b : String) : Bool := ante.contains a && !ante.contains b
  let mut out : Array Json := #[]
  -- Conjunctive bridges have their own cap (`maxConjunctive`) and the full
  -- budget: one stands for many single ones, and its long antecedent makes the
  -- search heavier.
  let mut conjunctiveFound := false
  for (qn, bridge) in conjunctive.extract 0 maxConjunctive do
    let some fields ← checkBridge xs origins hyps concl u heartbeats domains bridge heartbeats
      | continue
    conjunctiveFound := true
    out := out.push (Json.mkObj ([("from", Json.str (" ∧ ".intercalate ante.toList)), ("to", Json.str qn),
      ("fixed", toJson (#[] : Array String)), ("conjunctive", Json.bool true),
      ("replaces_single_conjuncts", toJson ante)] ++ fields))
  -- Single-conjunct bridges are dropped when a conjunctive bridge passed;
  -- otherwise they are tried last and reported demoted (`single_conjunct`).
  let ordered := (first ++ later).filter (fun ((a, _), (b, _), _, _) => !single a b) ++
    (if conjunctiveFound then #[] else (first ++ later).filter fun ((a, _), (b, _), _, _) => single a b)
  let mut tried := 0
  for ((pn, p), (qn, q), pe, qe) in ordered do
    for fix in [true, false] do
      if tried ≥ 48 then return out
      let some (bridge, fixed) ← bridgeFor p q pe qe fix | continue
      tried := tried + 1
      let some fields ← checkBridge xs origins hyps concl u heartbeats domains bridge
          (max 2000 (heartbeats / 4)) | continue
      out := out.push (Json.mkObj ([("from", Json.str pn), ("to", Json.str qn),
        ("fixed", toJson fixed), ("single_conjunct", Json.bool (single pn qn))] ++ fields))
      break
  return out

/-! ### Projection binding

A target may bind a value that a premise reaches only as a field of a
structure binder: `OnticTSchemaValid (o : Ontic W B)` against
`OnticFrameKT (m : Profile W B)`, whose `m.ontic : Ontic W B`. Binding by name,
type or tag never identifies `o` with `m.ontic`, so the goal over separate `o`
and `m` is false although `∀ m, OnticFrameKT m → OnticTSchemaValid m.ontic`
may hold. When the goal fails, each such projection (a target binder that is
a value, never an instance, carrier, predicate or function, even through a
definitional alias; a non-instance premise structure binder with a field of
definitionally equal type) is tried in turn as an explicit binding choice: the
target binder is replaced by the projection everywhere and the goal searched
again. A choice that closes the goal is reported (`projection`, and `bound_to`
on the binder); none is ever made silently. A goal closed under it is a
specialization of the target statement to the projection, not the statement
over an arbitrary binder. A target binder with several candidate projections
among the premises minimization keeps is `ambiguous` (identification by type
alone; an alternative only a dropped premise introduced is listed as
`dropped_alternatives`, #1845), and a choice whose structure premise
minimization drops is `projection_unused`: `truth discover` rejects both. -/

/-- At most this many projection choices are searched per goal. -/
def maxProjections : Nat := 4

/-- The projection choices: `(i, j, field, value)` where target binder `xs[i]`
has the type of field `field` of the premise structure binder `xs[j]`, and
`value` is that projection applied to `xs[j]`. -/
def projectionCandidates (target : Name) (xs : Array Expr) (origins : Array Origin) :
    MetaM (Array (Nat × Nat × Name × Expr)) := do
  let env ← getEnv
  let mut out : Array (Nat × Nat × Name × Expr) := #[]
  for i in [0:xs.size] do
    let x := xs[i]!
    unless origins[i]!.decl == target do continue
    if (← x.fvarId!.getBinderInfo).isInstImplicit then continue
    let xt ← instantiateMVars (← inferType x)
    -- Values only (an element, a structure such as `o : Ontic W B`): a
    -- predicate or function binder is never bound to a field of matching type,
    -- which would equate unrelated relations (`Simple := D.Lives`).
    -- `forallTelescopeReducing` unfolds at default transparency, so an alias
    -- such as `def Pred B := B → Prop` (or Mathlib's `Set B`) counts as a
    -- predicate too.
    if xt.isSort || (← isProp xt) then continue
    if ← forallTelescopeReducing xt fun ys _ => pure !ys.isEmpty then continue
    for j in [0:xs.size] do
      let y := xs[j]!
      if origins[j]!.decl == target then continue
      if (← y.fvarId!.getBinderInfo).isInstImplicit then continue
      let yt ← whnfR (← instantiateMVars (← inferType y))
      let .const s _ := yt.getAppFn | continue
      unless isStructure env s do continue
      for f in getStructureFields env s do
        let some proj := getProjFnForField? env s f | continue
        let some t ← (try some <$> mkAppM proj #[y] catch _ => pure none) | continue
        if ← withoutModifyingState (isDefEq (← inferType t) xt) then
          out := out.push (i, j, f, ← instantiateMVars t)
  return out

/-- The goal with binder `xs[i]` replaced by `value`, reopened over the other
binders (the original binders erased from the context, so nothing can borrow
them): `k` receives the binders, the hypotheses and the conclusion. `none` when
another binder's type mentions `xs[i]`. -/
def withProjection (xs : Array Expr) (hyps : Array (Nat × Expr)) (concl : Expr) (i : Nat)
    (value : Expr) (k : Array Expr → Array (Nat × Expr) → Expr → TermElabM (Option α)) :
    TermElabM (Option α) := do
  let x := xs[i]!
  let rest := xs.filter (· != x)
  for y in rest do
    if (← instantiateMVars (← inferType y)).containsFVar x.fvarId! then return none
  if value.containsFVar x.fvarId! then return none
  let body ← hyps.foldrM (fun (_, h) acc => mkArrow h acc) concl
  let body := (← instantiateMVars body).replaceFVar x value
  let goal ← mkForallFVars rest body
  let erased := xs.map (·.fvarId!)
  let lctx := erased.foldl (·.erase ·) (← getLCtx)
  let insts := (← getLocalInstances).filter fun inst => !erased.contains inst.fvar.fvarId!
  withLCtx lctx insts <| forallBoundedTelescope goal (some rest.size) fun ys b => do
    let mut b := b
    let mut hs : Array (Nat × Expr) := #[]
    for (idx, _) in hyps do
      let .forallE _ d body _ := b | return none
      hs := hs.push (idx, d)
      b := body
    k ys hs b

/-- Everything after the goal closed: minimization, the incompatibility core
and its literal-negation check, the transcription probe, vacuous truth,
witnesses and the theorem signature. -/
def finish (target : Name) (premises : Array Name) (heartbeats : Nat)
    (byName : IO.Ref (Array Membership)) (xs : Array Expr) (hyps : Array (Nat × Expr))
    (concl : Expr) (u : Unfolding) (added : Array Json) (full : Proved) (projection : Json)
    (structureBinder : Option Expr := none) (alternatives : Array (Nat × String) := #[]) :
    TermElabM Json := do
    -- Duper is the authority for the Solution: re-prove an ATP-found goal on its core.
    let start ← if full.prover.startsWith "duper" then pure (some full) else
      prove xs (hyps.filter fun (i, _) => full.used.contains i) concl u heartbeats "" (duperOnly := true)
    let some start := start
      | return Json.mkObj [("binders", toJson added), ("alone", Json.null), ("closed", proved (some full)),
          ("projection", projection),
          ("reconstruction", "Duper did not reprove the premise core the external prover selected")]
    let (minimal, log, best) ← minimize xs hyps concl u heartbeats start
    let minHyps := hyps.filter fun (i, _) => minimal.contains i
    -- A projection choice is ambiguous when another structure binder (or
    -- another field of the same one) with a field of the target binder's type
    -- survives minimization: an alternative that only a dropped premise
    -- introduced is no part of the theorem (#1845).
    let projection := if alternatives.isEmpty then projection else
      let retained := alternatives.filter fun (k, _) => match xs[k]? with
        | some y => minHyps.any fun (_, h) => h.containsFVar y.fvarId!
        | none => false
      let dropped := alternatives.filter fun a => !retained.any (·.2 == a.2)
      projection
        |>.setObjVal! "ambiguous" (Json.bool (retained.size > 1))
        |>.setObjVal! "alternatives" (toJson (retained.map (·.2)))
        |>.setObjVal! "dropped_alternatives" (toJson (dropped.map (·.2)))
    -- Under a projection binding, a minimal premise must still speak of the
    -- structure binder: otherwise the premise that introduced it was dropped
    -- and the "derivation" is about the structure alone (`projection_unused`).
    let projectionUnused := match structureBinder with
      | some y => !minHyps.any fun (_, h) => h.containsFVar y.fvarId!
      | none => false
    -- An incompatibility is checked over the premises' own binders only (`proveOwn`).
    let vacuous ← proveOwn xs minHyps (Lean.mkConst ``False) u heartbeats
    let (vacuousCore, core, coreNames, coreProof) ← match vacuous with
      | some v => do
        let (core, _, best) ← minimize xs minHyps (Lean.mkConst ``False) u heartbeats v (own := true)
        pure (toJson core, core, core.filterMap fun i => premises[i]?, some best)
      | none => pure (Json.null, #[], #[], none)
    -- A core that is a premise and its literal negation (`truth discover`
    -- reports it as filtered `literal_negation`, never as an incompatibility).
    let literal ← if vacuous.isSome then
        literalNegation minHyps core (max 2000 (heartbeats / 10))
      else pure none
    -- Transcription probe on the folded goal (the prove-sweep heuristic).
    let folded ← mkForallFVars xs (← minHyps.foldrM (fun (_, h) acc => mkArrow h acc) concl)
    let probe ← withoutModifyingState do
      let mvar ← mkFreshExprMVar folded
      tryCatchRuntimeEx (do
          let rest ← Tactic.run mvar.mvarId! (Tactic.evalTactic (← `(tactic| prove_sweep_probe)))
          return rest.isEmpty)
        (fun _ => pure false)
    let minNames := minimal.map fun i => premises[i]!
    let identified ← byName.get
    -- Name the projected structure after a kept declaration: the outer binder
    -- may come from a dropped premise that a kept one joined (same module, a
    -- tag, or the name fallback).
    let (projection, added) := Id.run do
      let some sb := (projection.getObjValAs? String "structure_binder").toOption
        | return (projection, added)
      if minNames.any fun n => sb.startsWith s!"{n}." then return (projection, added)
      let some m := identified.find? fun m =>
          s!"{m.originDecl}.{m.originBinder}" == sb && minNames.contains m.decl
        | return (projection, added)
      let field := (projection.getObjValAs? String "field").toOption.getD ""
      let old := (projection.getObjValAs? String "bound_to").toOption.getD ""
      let bound := s!"{m.decl}.{m.binder}.{field}"
      let added := added.map fun b =>
        if (b.getObjValAs? String "bound_to").toOption == some old then
          b.setObjVal! "bound_to" (Json.str bound) else b
      let rename (key : String) : Json :=
        toJson (((projection.getObjValAs? (Array String) key).toOption.getD #[]).map
          fun a => if a == old then bound else a)
      let projection := projection |>.setObjVal! "structure_binder" (Json.str s!"{m.decl}.{m.binder}")
        |>.setObjVal! "bound_to" (Json.str bound)
      let projection := if (projection.getObjVal? "dropped_alternatives").isOk then
          projection.setObjVal! "dropped_alternatives" (rename "dropped_alternatives") else projection
      return (projection.setObjVal! "alternatives" (rename "alternatives"), added)
    let u' ← unfoldSet (minNames.push target)
    -- Vacuous truth: do the premises refute the target's own antecedents?
    -- (`∀ x, A x → B x` holds because nothing is `A`.) A valid derivation that a
    -- reviewer must see as such.
    let antecedentRefuted ← if vacuous.isSome then pure false else do
      let ec ← expand u' concl
      let refuted ← forallTelescope ec fun ys _ => do
        let mut props := false
        for y in ys do
          if ← isProp (← inferType y) then props := true
        if !props then return none
        let noB ← mkForallFVars ys (Lean.mkConst ``False)
        prove xs minHyps noB u' (max 2000 (heartbeats / 4)) "" (duperOnly := true)
      pure refuted.isSome
    -- Joint witness (premises and conclusion) and one-point omission models.
    let (joint, omissions) ← if vacuous.isSome then pure (none, #[]) else do
      let joint ← witness xs ((minHyps.map (·.2)).push concl) u (max 2000 (heartbeats / 4))
      let mut omissions : Array Json := #[]
      for (i, _) in minHyps do
        let others := minHyps.filter (·.1 != i) |>.map (·.2)
        let m ← witness xs (others.push (mkNot concl)) u (max 2000 (heartbeats / 10))
        omissions := omissions.push (Json.mkObj [("premise", toJson i),
          ("model", (m.map Json.str).getD Json.null)])
      pure (joint, omissions)
    return Json.mkObj [
      ("witness", (joint.map Json.str).getD Json.null),
      ("antecedent_refuted", Json.bool antecedentRefuted),
      ("omissions", Json.arr omissions),
      ("binders", toJson added),
      ("projection", projection),
      ("projection_unused", Json.bool projectionUnused),
      ("alone", Json.null),
      ("closed", proved (some full)),
      ("minimal", toJson minimal),
      ("deletions", Json.arr log),
      ("proof", proved (some best)),
      -- An incompatibility concerns its core only; an implication, its premises and target.
      ("domain_identified_by_name", toJson (keptIdentifications identified
        (if vacuous.isSome then coreNames else minNames.push target))),
      ("vacuous", proved vacuous),
      ("vacuous_core", vacuousCore),
      ("vacuous_core_proof", proved coreProof),
      ("literal_negation", match literal with
        | some (i, j) => toJson #[i, j]
        | none => Json.null),
      ("probe", Json.bool probe),
      ("signature", Json.str (← signature xs minHyps concl)),
      ("unfold", jsonNames (u'.delta.toArray.qsort Name.lt)),
      -- Only when the closing proof needed them (the `+equations` fallback).
      ("equations", jsonNames (if best.prover.endsWith "+equations" then
        u'.eqns.toArray.qsort Name.lt else #[]))]

def trial (target : Name) (premises : Array Name) (heartbeats : Nat) (zip : String)
    (tags : Array (Name × Name × String)) (bridges : Bool) (strict : Bool)
    (byName : IO.Ref (Array Membership)) :
    TermElabM Json := do
  let env ← getEnv
  for n in premises.push target do
    unless env.contains n do
      return Json.mkObj [("error", Json.str s!"unknown declaration {n}")]
  bindAll tags strict byName #[] #[] (target :: premises.toList) #[] fun xs origins ps => do
    let concl := ps[0]!
    let hyps := (ps.extract 1 ps.size).zipIdx.map fun (h, i) => (i, h)
    for e in ps do
      unless ← isProp e do
        return Json.mkObj [("error", Json.str s!"not a Prop-valued family: {← ppExpr (← inferType e)}")]
    -- Universe-polymorphic statements are taken at the lowest universe that
    -- keeps a carrier a type: a level `u` with a binder `B : Sort u` becomes 1,
    -- any other level 0 (a specialization; the theorem stays valid).
    for x in xs do
      if let .sort (.mvar m) := (← instantiateMVars (← inferType x)) then
        unless ← isLevelMVarAssigned m do assignLevelMVar m Level.one
    let mut levels : Array LMVarId := #[]
    for e in (← xs.mapM fun x => inferType x) ++ ps do
      levels := levels ++ (collectLevelMVars {} (← instantiateMVars e)).result
    for m in levels do
      unless ← isLevelMVarAssigned m do assignLevelMVar m Level.zero
    let xsTypes ← xs.mapM fun x => do instantiateMVars (← inferType x)
    if xsTypes.any (·.hasMVar) || (← instantiateMVars concl).hasLevelMVar then
      return Json.mkObj [("error", Json.str "universe or type metavariables remain after binding")]
    let u ← unfoldSet (premises.push target)
    let added ← (xs.zip origins).mapM fun (x, o) => return Json.mkObj [("name", Json.str (← x.fvarId!.getUserName).toString),
      ("from", Json.str s!"{o.decl}.{o.binder}"), ("sense", (o.sense.map Json.str).getD Json.null)]
    -- Premise-free check over the target's own binders only: a binder that a
    -- candidate premise introduced (an element `x : B`, an instance) is erased
    -- from the context, so it can neither be used nor quantified, and a
    -- vocabulary theorem never rests on a nonemptiness assumption the target
    -- does not make. The target is bound first, so no target binder depends on
    -- an erased one.
    let targetXs := (xs.zip origins).filterMap fun (x, o) => if o.decl == target then some x else none
    let extra := (xs.zip origins).filterMap fun (x, o) => if o.decl == target then none else some x.fvarId!
    let aloneLCtx := extra.foldl (·.erase ·) (← getLCtx)
    let aloneInsts := (← getLocalInstances).filter fun i => !extra.contains i.fvar.fvarId!
    let alone ← withLCtx aloneLCtx aloneInsts <| prove targetXs #[] concl u heartbeats zip
    if alone.isSome then
      let uAlone ← unfoldSet #[target]
      return Json.mkObj [("binders", toJson added), ("alone", proved alone),
        ("signature", Json.str (← withLCtx aloneLCtx aloneInsts <| signature targetXs #[] concl)),
        ("unfold", jsonNames (uAlone.delta.toArray.qsort Name.lt)),
        ("equations", jsonNames (if (alone.map (·.prover.endsWith "+equations")).getD false then
          uAlone.eqns.toArray.qsort Name.lt else #[]))]
    if let some full ← prove xs hyps concl u heartbeats zip then
      return ← finish target premises heartbeats byName xs hyps concl u added full Json.null
    -- Projection binding choices (explicit and reported, never silent). A
    -- target binder with more than one candidate projection (two fields, or
    -- two structure binders, of its type) is identified by type alone: the
    -- choice is reported `ambiguous` and `truth discover` rejects it
    -- (`projection_ambiguous`).
    let candidates ← projectionCandidates target xs origins
    let label (j : Nat) (field : Name) : String :=
      s!"{origins[j]!.decl}.{origins[j]!.binder}.{field}"
    let mut tried : Array Json := #[]
    let mut unused : Option Json := none
    for (i, j, field, value) in candidates.extract 0 maxProjections do
      let o := origins[i]!
      let p := origins[j]!
      let alternatives := (candidates.filter (·.1 == i)).map fun (_, j', f', _) => Json.str (label j' f')
      let choice := Json.mkObj [("binder", Json.str s!"{o.decl}.{o.binder}"),
        ("bound_to", Json.str (label j field)),
        ("structure_binder", Json.str s!"{p.decl}.{p.binder}"), ("field", Json.str field.toString),
        ("ambiguous", Json.bool (alternatives.size > 1)), ("alternatives", Json.arr alternatives)]
      tried := tried.push choice
      let added' := added.mapIdx fun k b =>
        if k == i then b.setObjVal! "bound_to" (Json.str (label j field)) else b
      -- The structure binder's position once `xs[i]` is removed.
      let j' := if j > i then j - 1 else j
      -- Every alternative, by its structure binder's position in the reopened goal.
      let alts := (candidates.filter (·.1 == i)).map fun (_, j2, f2, _) =>
        ((if j2 > i then j2 - 1 else j2), label j2 f2)
      let result ← withProjection xs hyps concl i value fun ys hs c => do
        let some full ← prove ys hs c u heartbeats zip | return none
        some <$> finish target premises heartbeats byName ys hs c u added' full choice ys[j']? alts
      if let some json := result then
        -- A choice whose structure premise minimization dropped is kept only
        -- as the report of last resort; another choice may use its premise.
        if (json.getObjValAs? Bool "projection_unused").toOption == some true then
          if unused.isNone then unused := some json
        else return json
    if let some json := unused then return json
    let identified ← byName.get
    let domains (used : Array Nat) (extra : Array Name) : Array String :=
      keptIdentifications identified ((used.filterMap fun i => premises[i]?).push target ++ extra)
    let found ← if bridges then missingBridges xs origins target hyps concl u heartbeats domains
      else pure #[]
    return Json.mkObj [("binders", toJson added), ("alone", Json.null), ("closed", Json.null),
      ("projections_tried", Json.arr tried), ("bridges", Json.arr found)]

syntax (name := discoverTry) "#discover " str num str str ident " from " ident* : command

@[command_elab discoverTry] def elabDiscover : CommandElab := fun stx => do
  let label := stx[1].isStrLit?.getD ""
  let heartbeats := stx[2].isNatLit?.getD 20000
  let zip := stx[3].isStrLit?.getD ""
  let config := (Json.parse (stx[4].isStrLit?.getD "{}")).toOption.getD (Json.mkObj [])
  let tags : Array (Name × Name × String) :=
    ((config.getObjValAs? (Array (Array String)) "tags").toOption.getD #[]).filterMap fun t =>
      if t.size == 3 then some (t[0]!.toName, t[1]!.toName, t[2]!) else none
  let bridges := (config.getObjValAs? Bool "bridges").toOption.getD false
  let strict := (config.getObjValAs? Bool "strict_domains").toOption.getD false
  let byName ← IO.mkRef (#[] : Array Membership)
  let target := stx[5].getId
  let premises := stx[7].getArgs.map (·.getId)
  let started ← IO.monoMsNow
  let result ← liftTermElabM do
    try trial target premises heartbeats zip tags bridges strict byName
    catch e => return Json.mkObj [("error", Json.str (← e.toMessageData.toString))]
  let result := result.setObjVal! "label" (Json.str label)
  let all := (← byName.get).filterMap fun m =>
    if m.byName then some (m.text m.originDecl m.originBinder) else none
  let result := if (result.getObjVal? "domain_identified_by_name").isOk then result else
    result.setObjVal! "domain_identified_by_name" (toJson all)
  let result := result.setObjVal! "ms" (toJson ((← IO.monoMsNow) - started))
  -- `truth discover` reads this log, so finished targets survive a timed-out run.
  if let some path ← IO.getEnv "TRUTH_DISCOVER_LOG" then
    IO.FS.withFile path .append fun h => h.putStrLn s!"DISCOVER-JSON {result.compress}"
  logInfo m!"DISCOVER-JSON {result.compress}"

end Discover
