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
  the outer binders, so no proof-search budget can prove it).

Every carrier is read as `Unit` and every predicate as a constant (the slot
pattern names which), as in `Discover.witness`. Such a model is a fact about
this binding of these declarations only: it neither refutes a premise nor
excludes a stronger formulation, another binding, a sense identification or
an added premise. The binders are reported with their origin, sense tag and
type so that the model's quantifier scope is explicit. The output is one
`DISCOVER-REPAIR-JSON` info line (also appended to `TRUTH_DISCOVER_LOG`).
-/
open Lean Elab Command Term Meta

namespace DiscoverRepair

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
    let identified ← byName.get
    let names := identified.filterMap fun m =>
      if m.byName then some (m.text m.originDecl m.originBinder) else none
    return Json.mkObj [("binders", Json.arr binders),
      ("premises_model", (premisesModel.map Json.str).getD Json.null),
      ("countermodel", (counter.map Json.str).getD Json.null),
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
