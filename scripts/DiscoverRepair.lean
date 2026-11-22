import Lean
/-!
Exact-bundle countermodel probe for `scripts/discover_blueprint.py repair`
(#1833, docs/discover.md, "Adaptive repair").

Like `scripts/Discover.lean`, this file is not run on its own: the repair tool
appends its body (its `import` lines hoisted) after the body of
`scripts/Discover.lean` in a scratch file, so it reuses that file's binding
(`Discover.bindAll`, the same policy and sense tags as `truth discover`) and
its one-point model search (`Discover.witness`) unchanged. One command per
probe:

    #discover_countermodel "label" HEARTBEATS "CONFIG" Target from P₁ … Pₙ

It binds the target and the premises exactly as `#discover` does, then
searches a one-point model of

* the premises alone (`premises_model`: the bundle is jointly satisfiable, so
  it is not an inconsistent core), and
* the premises together with the negated target (`countermodel`: the formal
  implication `∀ binders, P₁ → … → Pₙ → Target` fails at that instantiation of
  the outer binders under this *plain* binding, so no proof-search budget
  proves the plainly bound goal).

Every carrier is read as `Unit` and every predicate as a constant, as in
`Discover.witness`; `slots` maps each binder to the predicate slots it
received, so the slot pattern names which binder is `True` and which `False`.
Such a model is a fact about this plain binding of these declarations only.
`#discover` also tries *projection bindings* (a target binder bound to a field
of a premise's structure binder, `Discover.projectionCandidates`): those are
not tested here and are listed as `projections_untested`; a countermodel to
`∀ o m, H m → T o` does not refute `∀ m, H m → T m.ontic`. The model refutes no
premise and excludes no stronger formulation, other binding, sense
identification or added premise. The binders are reported with their origin,
sense tag and type so that the model's quantifier scope is explicit. The
output is one `DISCOVER-REPAIR-JSON` info line (also appended to
`TRUTH_DISCOVER_LOG`); the bounds prose of the repair report is added by
`scripts/discover_blueprint.py`, not here.
-/
open Lean Elab Command Term Meta

namespace DiscoverRepair

/-- The predicate slots each binder receives under `Discover.instantiateBinders`
(the same traversal, all slots `False`): `[{binder, slots}]`, binders without a
slot omitted. -/
def slotMap (xs : Array Expr) : MetaM (Array Json) := do
  let mut vals : Array Expr := #[]
  let mut slots := 0
  let mut out : Array Json := #[]
  for x in xs do
    let ty := (← inferType x).replaceFVars (xs.extract 0 vals.size) vals
    if (← x.fvarId!.getBinderInfo).isInstImplicit then
      vals := vals.push (← synthInstance ty)
    else
      let (v, s) ← (Discover.interp (fun _ => false) ty).run slots
      if s > slots then
        out := out.push (Json.mkObj [("binder", Json.str (← x.fvarId!.getUserName).toString),
          ("slots", toJson (List.range' slots (s - slots)))])
      slots := s
      vals := vals.push v
  return out

def countermodel (target : Name) (premises : Array Name) (heartbeats : Nat)
    (tags : Array (Name × Name × String)) (strict : Bool)
    (byName : IO.Ref (Array Discover.Membership)) : TermElabM Json := do
  let env ← getEnv
  for n in premises.push target do
    unless env.contains n do
      return Json.mkObj [("error", Json.str s!"unknown declaration {n}")]
  Discover.bindAll tags strict byName #[] #[] (target :: premises.toList) #[] fun xs origins ps => do
    let concl := ps[0]!
    let hyps := ps.extract 1 ps.size
    for e in ps do
      unless ← isProp e do
        return Json.mkObj [("error", Json.str s!"not a Prop-valued family: {← ppExpr (← inferType e)}")]
    -- The universe specialization of `Discover.trial`.
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
    let u ← Discover.unfoldSet (premises.push target)
    let binders ← (xs.zip origins).mapM fun (x, o) => do
      return Json.mkObj [("name", Json.str (← x.fvarId!.getUserName).toString),
        ("from", Json.str s!"{o.decl}.{o.binder}"),
        ("sense", (o.sense.map Json.str).getD Json.null),
        ("type", Json.str (toString (← ppExpr (← inferType x))))]
    let premisesModel ← Discover.witness xs hyps u heartbeats
    let counter ← Discover.witness xs (hyps.push (mkNot concl)) u heartbeats
    let slots ← try slotMap xs catch _ => pure #[]
    let projections ← Discover.projectionCandidates target xs origins
    let untested := projections.map fun (i, j, field, _) =>
      Json.str s!"{origins[i]!.decl}.{origins[i]!.binder} := {origins[j]!.decl}.{origins[j]!.binder}.{field}"
    let identified ← byName.get
    let names := identified.filterMap fun m =>
      if m.byName then some (m.text m.originDecl m.originBinder) else none
    return Json.mkObj [("binders", Json.arr binders),
      ("premises_model", (premisesModel.map Json.str).getD Json.null),
      ("countermodel", (counter.map Json.str).getD Json.null),
      ("slots", Json.arr slots),
      ("projections_untested", Json.arr untested),
      ("domain_identified_by_name", toJson names)]

syntax (name := countermodelTry) "#discover_countermodel " str num str ident " from " ident* : command

@[command_elab countermodelTry] def elabCountermodel : CommandElab := fun stx => do
  let label := stx[1].isStrLit?.getD ""
  let heartbeats := stx[2].isNatLit?.getD 20000
  let config := (Json.parse (stx[3].isStrLit?.getD "{}")).toOption.getD (Json.mkObj [])
  let tags : Array (Name × Name × String) :=
    ((config.getObjValAs? (Array (Array String)) "tags").toOption.getD #[]).filterMap fun t =>
      if t.size == 3 then some (t[0]!.toName, t[1]!.toName, t[2]!) else none
  let strict := (config.getObjValAs? Bool "strict_domains").toOption.getD false
  let byName ← IO.mkRef (#[] : Array Discover.Membership)
  let target := stx[4].getId
  let premises := stx[6].getArgs.map (·.getId)
  let started ← IO.monoMsNow
  let result ← liftTermElabM do
    try countermodel target premises heartbeats tags strict byName
    catch e => return Json.mkObj [("error", Json.str (← e.toMessageData.toString))]
  let result := result.setObjVal! "label" (Json.str label)
  let result := result.setObjVal! "ms" (toJson ((← IO.monoMsNow) - started))
  if let some path ← IO.getEnv "TRUTH_DISCOVER_LOG" then
    IO.FS.withFile path .append fun h => h.putStrLn s!"DISCOVER-REPAIR-JSON {result.compress}"
  logInfo m!"DISCOVER-REPAIR-JSON {result.compress}"

end DiscoverRepair
