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
  or both tagged with the same sense id.

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

def moduleOf (n : Name) : MetaM Name := do
  let env ← getEnv
  match env.getModuleIdxFor? n with
  | some idx => return env.header.moduleNames[idx.toNat]!
  | none => return .anonymous

def senseOf (tags : Array (Name × Name × String)) (decl binder : Name) : Option String :=
  (tags.find? fun (d, b, _) => d == decl && b == binder.eraseMacroScopes).map (·.2.2)

def isStructureType (d : Expr) : MetaM Bool := do
  let d ← whnfR d
  match d.getAppFn with
  | .const c _ => return isStructure (← getEnv) c
  | _ => return false

partial def bind (tags : Array (Name × Name × String)) (strict : Bool)
    (byName : IO.Ref (Array (Name × Name × Name × String))) (decl : Name) (module : Name)
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
      let authored := (sameName && o.module == module) || (sense.isSome && o.sense == sense)
      let fallback := !strict && (carrier || bundle) && sameName && !authored
      let allowed := if bi.isInstImplicit then xbi.isInstImplicit else authored || fallback
      if allowed then
        if ← isDefEq (← inferType x) d then
          if fallback && !bi.isInstImplicit then
            byName.modify (·.push (decl, o.decl, o.binder, s!"{decl}.{n} = {o.decl}.{o.binder}"))
          return ← bind tags strict byName decl module xs origins (mkApp e x) k
    if bi.isInstImplicit then
      if let some inst ← (try synthInstance? d catch _ => pure none) then
        return ← bind tags strict byName decl module xs origins (mkApp e inst) k
    let n' ← freshUserName xs n
    withLocalDecl n' bi (← instantiateMVars d) fun y =>
      bind tags strict byName decl module (xs.push y) (origins.push { decl, binder := n, module, sense })
        (mkApp e y) k
  | _ => k xs origins e

/-- `bind` for every name in turn: the target first, then the premises. -/
partial def bindAll (tags : Array (Name × Name × String)) (strict : Bool)
    (byName : IO.Ref (Array (Name × Name × Name × String)))
    (xs : Array Expr) (origins : Array Origin) (names : List Name) (acc : Array Expr)
    (k : Array Expr → Array Origin → Array Expr → TermElabM α) : TermElabM α := do
  match names with
  | [] => k xs origins acc
  | n :: rest =>
    let e ← mkConstWithFreshMVarLevels n
    bind tags strict byName n (← moduleOf n) xs origins e fun xs' os p =>
      bindAll tags strict byName xs' os rest (acc.push p) k

/-- Project definitions to delta-expand: `TruthCore.` definitions with a value
whose type ends in `Prop`, not projections, instances or recursive helpers,
reached transitively from `roots`. -/
partial def unfoldSet (roots : Array Name) : MetaM NameSet := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo := roots.toList
  let mut out : NameSet := {}
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
    let isPred ← forallTelescopeReducing d.type fun _ body => return body.isProp
    unless isPred do continue
    out := out.insert n
    for c in d.value.getUsedConstants do
      unless seen.contains c do todo := c :: todo
  return out

def expand (u : NameSet) (e : Expr) : MetaM Expr := do
  deltaExpand (← instantiateMVars e) u.contains

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
def prove (xs : Array Expr) (hyps : Array (Nat × Expr)) (concl : Expr) (u : NameSet)
    (heartbeats : Nat) (zip : String) (duperOnly : Bool := false) : TermElabM (Option Proved) := do
  let concl' ← expand u concl
  let hypTys ← hyps.mapM fun (i, h) => return (i, ← expand u h)
  let mut provers : Array (String × Syntax) := #[("duper", ← `(tactic| duper [*]))]
  if !duperOnly && !zip.isEmpty then
    provers := provers.push ("auto+zipperposition", ← `(tactic| auto))
  for (name, tac) in provers do
    let saved ← saveState
    let result ← tryCatchRuntimeEx (do
        let opts := (← getOptions)
          |>.set `maxHeartbeats heartbeats
          |>.set `auto.tptp (name != "duper")
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

/-- Deletion minimization: drop each remaining premise in turn and keep it
dropped when Duper still proves the goal. -/
def minimize (xs : Array Expr) (hyps : Array (Nat × Expr)) (concl : Expr) (u : NameSet)
    (heartbeats : Nat) (start : Proved) : TermElabM (Array Nat × Array Json × Proved) := do
  let mut current := start.used
  let mut best := start
  let mut log : Array Json := #[]
  for i in start.used do
    unless current.contains i do continue
    let without := current.filter (· != i)
    let sub := hyps.filter fun (j, _) => without.contains j
    match ← prove xs sub concl u heartbeats "" (duperOnly := true) with
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

/-- A one-point model of `goals` (conjoined) over the binders `xs`: the slot
pattern that closes it, if any. -/
def witness (xs : Array Expr) (goals : Array Expr) (u : NameSet) (heartbeats : Nat) :
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
            let tac ← `(tactic| first | (simp; done) | decide | trivial | (simp_all; done))
            let rest ← Tactic.run mvar.mvarId! (Tactic.evalTactic tac)
            let proof ← instantiateMVars mvar
            if !rest.isEmpty || proof.hasMVar || proof.hasSorry || proof.hasFVar then return false
            let aux ← mkFreshUserName `_discoverWitness
            withOptions (fun o => o.set `Elab.async false) <|
              addDecl (.thmDecl { name := aux, levelParams := [], type := body, value := proof })
            return true)
      (fun _ => pure false)
    saved.restore (restoreInfo := true)
    if ok then return some label
  return none

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

def missingBridges (xs : Array Expr) (origins : Array Origin) (_target : Name)
    (hyps : Array (Nat × Expr)) (concl : Expr) (u : NameSet) (heartbeats : Nat) :
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
      if !inC p && !inH q then
        first := first.push ((pn, p), (qn, q), near p, near q) |>.push ((qn, q), (pn, p), near q, near p)
      else
        later := later.push ((pn, p), (qn, q), near p, near q) |>.push ((qn, q), (pn, p), near q, near p)
  let budget := max 2000 (heartbeats / 4)
  let mut out : Array Json := #[]
  let mut tried := 0
  for ((pn, p), (qn, q), pe, qe) in first ++ later do
    for fix in [true, false] do
      if tried ≥ 48 then return out
      let some (bridge, fixed) ← bridgeFor p q pe qe fix | continue
      tried := tried + 1
      let withBridge := hyps.push (1000, bridge)
      let some proof ← prove xs withBridge concl u budget "" (duperOnly := true) | continue
      unless proof.used.contains 1000 do continue
      -- A bridge that proves the target on its own merely restates it.
      if (← prove xs #[(1000, bridge)] concl u (max 2000 (heartbeats / 10)) ""
          (duperOnly := true)).isSome then continue
      if (← prove xs withBridge (Lean.mkConst ``False) u (max 2000 (heartbeats / 10)) ""
          (duperOnly := true)).isSome then continue
      let text ← withOptions (fun o => o |>.set `pp.fullNames true |>.set `pp.fieldNotation false
          |>.set `format.width (100000 : Nat)) do
        return toString (← ppExpr bridge)
      out := out.push (Json.mkObj [("from", Json.str pn), ("to", Json.str qn),
        ("fixed", toJson fixed), ("text", Json.str text),
        ("used", toJson (proof.used.filter (· != 1000)))])
      break
  return out

/-- The name identifications that matter for the declarations `kept`: between
two kept declarations, or of two kept declarations with the same binder of a
dropped one. -/
def keptIdentifications (all : Array (Name × Name × Name × String)) (kept : Array Name) :
    Array String :=
  all.filterMap fun (d, od, ob, text) =>
    if !kept.contains d then none
    else if kept.contains od then some text
    else if all.any (fun (d2, od2, ob2, _) => d2 != d && kept.contains d2 && od2 == od && ob2 == ob)
      then some text else none

def trial (target : Name) (premises : Array Name) (heartbeats : Nat) (zip : String)
    (tags : Array (Name × Name × String)) (bridges : Bool) (strict : Bool)
    (byName : IO.Ref (Array (Name × Name × Name × String))) :
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
    let alone ← prove xs #[] concl u heartbeats zip
    if alone.isSome then
      return Json.mkObj [("binders", toJson added), ("alone", proved alone),
        ("signature", Json.str (← signature xs #[] concl)),
        ("unfold", jsonNames ((← unfoldSet #[target]).toArray.qsort Name.lt))]
    let full ← prove xs hyps concl u heartbeats zip
    let some full := full
      | do
        let found ← if bridges then missingBridges xs origins target hyps concl u heartbeats
          else pure #[]
        return Json.mkObj [("binders", toJson added), ("alone", Json.null), ("closed", Json.null),
          ("bridges", Json.arr found)]
    -- Duper is the authority for the Solution: re-prove an ATP-found goal on its core.
    let start ← if full.prover == "duper" then pure (some full) else
      prove xs (hyps.filter fun (i, _) => full.used.contains i) concl u heartbeats "" (duperOnly := true)
    let some start := start
      | return Json.mkObj [("binders", toJson added), ("alone", Json.null), ("closed", proved (some full)),
          ("reconstruction", "Duper did not reprove the premise core the external prover selected")]
    let (minimal, log, best) ← minimize xs hyps concl u heartbeats start
    let minHyps := hyps.filter fun (i, _) => minimal.contains i
    let vacuous ← prove xs minHyps (Lean.mkConst ``False) u heartbeats "" (duperOnly := true)
    let vacuousCore ← match vacuous with
      | some v => do
        let (core, _, _) ← minimize xs minHyps (Lean.mkConst ``False) u heartbeats v
        pure (toJson core)
      | none => pure Json.null
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
      ("alone", Json.null),
      ("closed", proved (some full)),
      ("minimal", toJson minimal),
      ("deletions", Json.arr log),
      ("proof", proved (some best)),
      ("domain_identified_by_name", toJson (keptIdentifications identified (minNames.push target))),
      ("vacuous", proved vacuous),
      ("vacuous_core", vacuousCore),
      ("probe", Json.bool probe),
      ("signature", Json.str (← signature xs minHyps concl)),
      ("unfold", jsonNames (u'.toArray.qsort Name.lt))]

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
  let byName ← IO.mkRef (#[] : Array (Name × Name × Name × String))
  let target := stx[5].getId
  let premises := stx[7].getArgs.map (·.getId)
  let started ← IO.monoMsNow
  let result ← liftTermElabM do
    try trial target premises heartbeats zip tags bridges strict byName
    catch e => return Json.mkObj [("error", Json.str (← e.toMessageData.toString))]
  let result := result.setObjVal! "label" (Json.str label)
  let all := (← byName.get).map (·.2.2.2)
  let result := if (result.getObjVal? "domain_identified_by_name").isOk then result else
    result.setObjVal! "domain_identified_by_name" (toJson all)
  let result := result.setObjVal! "ms" (toJson ((← IO.monoMsNow) - started))
  -- `truth discover` reads this log, so finished targets survive a timed-out run.
  if let some path ← IO.getEnv "TRUTH_DISCOVER_LOG" then
    IO.FS.withFile path .append fun h => h.putStrLn s!"DISCOVER-JSON {result.compress}"
  logInfo m!"DISCOVER-JSON {result.compress}"

end Discover
