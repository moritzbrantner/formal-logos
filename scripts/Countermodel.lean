import Lean
/-!
First-order skeleton of a theorem for the omission-countermodel finder
(`truth countermodel`, `truth/src/countermodel.rs`, docs/countermodels.md).

Usage, after `lake build <module>`:

    lake env lean --run scripts/Countermodel.lean <input.json>

Input: `{"modules": [...], "theorem": "<name>"}`. The theorem's binders are
classified as carriers (`B : Type` or `Sort u`), predicate parameters (functions
from carriers, or from carrier-valued predicates `T → Prop`, into `Prop`),
element constants (`esse : R`), total unary functions between carriers,
nested structures of relations, and propositional hypotheses (premises). Each
premise and the conclusion are unfolded through definitions into a formula over
`∀ ∃ ∧ ∨ ¬ → ↔ = ≠ True False` and predicate atoms; quantifiers over `Prop`
(as in `ExcludedMiddle`) range over the two truth values. The output is a search
problem, never a verdict: a model the finder proposes is checked again by Lean.
Anything outside this fragment is reported as an `error` naming the offending
expression.
-/
open Lean Meta

namespace Countermodel

def str (s : String) : Json := Json.str s

abbrev FieldPath := FVarId × Array Nat

structure Ctx where
  /-- Carrier free variables and their names. -/
  carriers : Array (FVarId × String) := #[]
  /-- Predicate parameters, element constants and bound variables. -/
  names : Array (FVarId × String) := #[]
  /-- Top-level unary carrier functions, kept distinct from predicate names. -/
  functions : Array (FVarId × String) := #[]
  /-- Relation tables keyed by their root parameter and constructor field indices. -/
  fields : Array (FieldPath × (String × Bool)) := #[]

structure St where
  unfolded : Array Name := #[]
  counter : Nat := 0

abbrev M := StateRefT St MetaM

def lookup (xs : Array (FVarId × String)) (f : FVarId) : Option String :=
  (xs.find? (·.1 == f)).map (·.2)

def fresh (base : Name) : M String := do
  let n ← modifyGet fun s => (s.counter, { s with counter := s.counter + 1 })
  let b := base.eraseMacroScopes.toString
  return s!"{if b.isEmpty then "x" else b}#{n}"

def carrierOf (ctx : Ctx) (ty : Expr) : Option String :=
  match ty.consumeMData with
  | .fvar f => lookup ctx.carriers f
  | _ => none

/-- A sort: a carrier name, or `{"set": [carriers]}` for `T₁ → … → Tₙ → Prop`. -/
def sortOf (ctx : Ctx) (ty : Expr) : MetaM (Option Json) := do
  if let some c := carrierOf ctx ty then return some (str c)
  forallTelescope ty fun xs body => do
    if xs.isEmpty || !body.consumeMData.isProp then return none
    let mut cs : Array Json := #[]
    for x in xs do
      match carrierOf ctx (← inferType x) with
      | some c => cs := cs.push (str c)
      | none => return none
    return some (Json.mkObj [("set", Json.arr cs)])

def unsupported (what : String) (e : Expr) : M α := do
  throwError "unsupported {what}: {← ppExpr e}"

def ppFull (e : Expr) : MetaM String := do
  return toString (← withOptions (fun o => o.setBool `pp.fullNames true) (ppExpr e))

/-- Separate the field path from any arguments applied to its relation. -/
partial def fieldApplication (e : Expr) : MetaM (Option (FieldPath × Array Expr)) := do
  let e := e.consumeMData.headBeta
  if let .fvar f := e then return some ((f, #[]), #[])
  let args := e.getAppArgs
  let (owner, index, inputs) ← match e.getAppFn.consumeMData with
    | .proj _ index owner => pure (owner, index, args)
    | .const name _ =>
      let some info := (← getEnv).getProjectionFnInfo? name | return none
      let some owner := args[info.numParams]? | return none
      pure (owner, info.i, args.extract (info.numParams + 1) args.size)
    | _ => return none
  let some ((root, path), remaining) ← fieldApplication owner | return none
  if !remaining.isEmpty then return none
  return some ((root, path.push index), inputs)

def relationField (ctx : Ctx) (e : Expr) (isBool : Bool) :
    MetaM (Option (String × Array Expr)) := do
  if ctx.fields.isEmpty then return none
  let some (path, args) ← fieldApplication e | return none
  let some (_, (name, returnsBool)) := ctx.fields.find? (·.1 == path) | return none
  return if isBool == returnsBool then some (name, args) else none

mutual

partial def term (ctx : Ctx) (e : Expr) : M Json := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  if let .fvar f := e then
    if let some n := lookup ctx.names f then return Json.mkObj [("v", str n)]
  if let .fvar f := e.getAppFn.consumeMData then
    if let some n := lookup ctx.functions f then
      let args := e.getAppArgs
      if args.size != 1 then unsupported "unary function application" e
      return Json.mkObj [("app", str n), ("arg", ← term ctx args[0]!)]
  let ty ← whnf (← inferType e)
  if ty.isForall then
    -- a predicate-valued argument: eta-expand over carriers
    return ← forallTelescope ty fun xs result => do
      if !result.consumeMData.isProp then unsupported "function-valued term" e
      let mut vars : Array Json := #[]
      let mut ctx := ctx
      for x in xs do
        let some c := carrierOf ctx (← inferType x) | unsupported "lambda binder" e
        let v ← fresh ((← x.fvarId!.getDecl).userName)
        ctx := { ctx with names := ctx.names.push (x.fvarId!, v) }
        vars := vars.push (Json.mkObj [("v", str v), ("sort", str c)])
      let body ← formula ctx (mkAppN e xs).headBeta
      return Json.mkObj [("lam", Json.arr vars), ("body", body)]
  unsupported "term" e

partial def binder (ctx : Ctx) (q : String) (n : Name) (dom body : Expr) (bi : BinderInfo) : M Json := do
  let s? ← if dom.consumeMData.isProp then pure (some (str "Prop")) else sortOf ctx dom
  let some s := s? | unsupported "quantifier domain" dom
  if (s.getObjVal? "set").isOk then unsupported "quantifier over predicates" dom
  withLocalDecl n bi dom fun x => do
    let v ← fresh n
    let b ← formula { ctx with names := ctx.names.push (x.fvarId!, v) } (body.instantiate1 x)
    return Json.mkObj [("t", str q), ("v", str v), ("sort", s), ("body", b)]

partial def boolFormula (ctx : Ctx) (e : Expr) : M Json := do
  let e := e.consumeMData.headBeta
  if e.isConstOf ``Bool.true then return Json.mkObj [("t", str "true")]
  if e.isConstOf ``Bool.false then return Json.mkObj [("t", str "false")]
  if let some (p, args) ← relationField ctx e true then
    return Json.mkObj [("t", str "atom"), ("p", str p), ("args", Json.arr (← args.mapM (term ctx)))]
  unsupported "Boolean expression" e

partial def formula (ctx : Ctx) (e : Expr) : M Json := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  if let .forallE n dom body bi := e then
    if (← isProp dom) && !body.hasLooseBVars then
      return Json.mkObj [("t", str "imp"), ("a", ← formula ctx dom), ("b", ← formula ctx body)]
    return ← binder ctx "forall" n dom body bi
  if let some (p, args) ← relationField ctx e false then
    return Json.mkObj [("t", str "atom"), ("p", str p), ("args", Json.arr (← args.mapM (term ctx)))]
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  let bin (t : String) := do
    return Json.mkObj [("t", str t), ("a", ← formula ctx args[0]!), ("b", ← formula ctx args[1]!)]
  match fn with
  | .const ``True _ => return Json.mkObj [("t", str "true")]
  | .const ``False _ => return Json.mkObj [("t", str "false")]
  | .const ``And _ => if args.size == 2 then return ← bin "and"
  | .const ``Or _ => if args.size == 2 then return ← bin "or"
  | .const ``Iff _ => if args.size == 2 then return ← bin "iff"
  | .const ``Not _ =>
    if args.size == 1 then return Json.mkObj [("t", str "not"), ("a", ← formula ctx args[0]!)]
  | .const ``Exists _ =>
    if args.size == 2 then
      match args[1]!.consumeMData with
      | .lam n dom body bi => return ← binder ctx "exists" n dom body bi
      | p =>
        let .forallE n dom _ bi ← whnf (← inferType p) | unsupported "existential" e
        return ← binder ctx "exists" n dom (mkApp (p.liftLooseBVars 0 1) (.bvar 0)) bi
  | .const ``Eq _ =>
    if args.size == 3 && args[0]!.isConstOf ``Bool then
      return Json.mkObj [("t", str "iff"), ("a", ← boolFormula ctx args[1]!),
        ("b", ← boolFormula ctx args[2]!)]
    if args.size == 3 && (carrierOf ctx args[0]!).isSome then
      return Json.mkObj [("t", str "eq"), ("a", ← term ctx args[1]!), ("b", ← term ctx args[2]!)]
  | .const ``Ne _ =>
    if args.size == 3 && args[0]!.isConstOf ``Bool then
      return Json.mkObj [("t", str "not"), ("a", Json.mkObj [("t", str "iff"),
        ("a", ← boolFormula ctx args[1]!), ("b", ← boolFormula ctx args[2]!)])]
    if args.size == 3 && (carrierOf ctx args[0]!).isSome then
      return Json.mkObj [("t", str "not"), ("a", Json.mkObj [("t", str "eq"),
        ("a", ← term ctx args[1]!), ("b", ← term ctx args[2]!)])]
  | .fvar f =>
    if let some p := lookup ctx.names f then
      return Json.mkObj [("t", str "atom"), ("p", str p), ("args", Json.arr (← args.mapM (term ctx)))]
  | .const n _ =>
    if let some e' ← unfoldDefinition? e then
      unless (← get).unfolded.contains n do
        modify fun s => { s with unfolded := s.unfolded.push n }
      return ← formula ctx e'
  | _ => pure ()
  unsupported "formula" e

end

/-- Argument sorts of a predicate parameter `S₁ → … → Sₙ → Prop`. -/
def predicateArgs (ctx : Ctx) (ty : Expr) : MetaM (Option (Array Json)) :=
  forallTelescope ty fun ys body => do
    if ys.isEmpty || !body.consumeMData.isProp then return none
    let mut args : Array Json := #[]
    for y in ys do
      match ← sortOf ctx (← inferType y) with
      | some s => args := args.push s
      | none => return none
    return some args

/-- Only a nondependent unary function with an explicit input between already
declared carriers. Function-valued arguments/results, multiple arguments and
dependent families remain outside the extracted fragment. -/
def unaryFunctionSorts (ctx : Ctx) (ty : Expr) : MetaM (Option (String × String)) :=
  forallTelescope ty fun xs body => do
    if xs.size != 1 then return none
    -- Certificates render an explicit arrow; accepting implicit inputs would
    -- lose the binder metadata needed by the original pretty-printed premises.
    if (← xs[0]!.fvarId!.getBinderInfo) != .default then return none
    let some domain := carrierOf ctx (← inferType xs[0]!) | return none
    let some codomain := carrierOf ctx body | return none
    return some (domain, codomain)

def fieldRelationArgs (ctx : Ctx) (ty : Expr) : MetaM (Option (Array String × Bool)) :=
  forallTelescope ty fun xs result => do
    let isBool := result.isConstOf ``Bool
    if !isBool && !result.isProp then return none
    let mut args := #[]
    for x in xs do
      if (← x.fvarId!.getBinderInfo) != .default then return none
      let some carrier := carrierOf ctx (← inferType x) | return none
      args := args.push carrier
    return some (args, isBool)

/-- Extract only structures over the already declared carriers. Each leaf adds
one ordinary solver predicate, so nested fields use the same finite search. -/
partial def structureValue (ctx : Ctx) (preds : Array Json) (root : FVarId)
    (path : Array Nat) (label : String) (value : Expr) :
    MetaM (Ctx × Array Json × String) := do
  let ty ← inferType value
  if let some (args, isBool) ← fieldRelationArgs ctx ty then
    let name := s!"«countermodel field {preds.size}»"
    let ctx := { ctx with fields := ctx.fields.push ((root, path), (name, isBool)) }
    let preds := preds.push (Json.mkObj [("name", str name), ("args", Json.arr (args.map str))])
    let rendered := if !isBool then name else
      let vars := (List.range args.size).map (fun i => s!"x{i}")
      let call := String.intercalate " " (name :: vars)
      if vars.isEmpty then s!"(decide {call})"
      else s!"(fun {String.intercalate " " vars} => decide ({call}))"
    return (ctx, preds, rendered)
  let env ← getEnv
  let what := if path.isEmpty then s!"parameter {label}" else s!"structure field {label}"
  let some head := ty.getAppFn.constName? | throwError "unsupported {what} : {← ppExpr ty}"
  if !isStructure env head || (← isClass? ty).isSome then
    throwError "unsupported {what} : {← ppExpr ty}"
  let ctor := getStructureCtor env head
  let params := ty.getAppArgs
  unless params.size == ctor.numParams do
    throwError "unsupported indexed structure at {label} : {← ppExpr ty}"
  let mut parts := #[s!"@{ctor.name}"]
  for param in params do
    let some c := carrierOf ctx param |
      throwError "unsupported structure parameter at {label} : {← ppExpr param}"
    parts := parts.push c
  let mut ctx := ctx
  let mut preds := preds
  let fields := getStructureFields env head
  for i in [:fields.size] do
    let (nextCtx, nextPreds, rendered) ← structureValue ctx preds root (path.push i)
      s!"{label}.{fields[i]!}" (.proj head i value)
    ctx := nextCtx
    preds := nextPreds
    parts := parts.push rendered
  return (ctx, preds, s!"({String.intercalate " " parts.toList})")

def run (n : Name) : MetaM Json := do
  let some info := (← getEnv).find? n | throwError "unknown declaration {n}"
  forallTelescope info.type fun xs concl => do
    let mut ctx : Ctx := {}
    let mut carriers : Array Json := #[]
    let mut preds : Array Json := #[]
    let mut consts : Array Json := #[]
    let mut funcs : Array Json := #[]
    let mut structures : Array Json := #[]
    let mut application : Array Json := #[]
    let mut names : Array String := #[]
    let mut hyps : Array (String × Expr) := #[]
    for x in xs do
      let decl ← x.fvarId!.getDecl
      let name := decl.userName.eraseMacroScopes.toString
      if ctx.functions.any (fun entry => entry.2 == name) then
        throwError "unsupported duplicate function binder name {name}"
      let reusedName := names.contains name
      names := names.push name
      let ty ← instantiateMVars decl.type
      let mut argument := name
      if ty.isProp then
        ctx := { ctx with names := ctx.names.push (x.fvarId!, name) }
        preds := preds.push (Json.mkObj [("name", str name), ("args", Json.arr #[])])
      else if ty.isSort then
        ctx := { ctx with carriers := ctx.carriers.push (x.fvarId!, name) }
        carriers := carriers.push (str name)
      else if ← isProp ty then
        argument := s!"«countermodel premise {hyps.size}»"
        hyps := hyps.push (name, ty)
      else if let some c := carrierOf ctx ty then
        ctx := { ctx with names := ctx.names.push (x.fvarId!, name) }
        consts := consts.push (Json.mkObj [("name", str name), ("sort", str c)])
      else if let some args ← predicateArgs ctx ty then
        ctx := { ctx with names := ctx.names.push (x.fvarId!, name) }
        preds := preds.push (Json.mkObj [("name", str name), ("args", Json.arr args)])
      else if let some (domain, codomain) ← unaryFunctionSorts ctx ty then
        if reusedName then throwError "unsupported duplicate function binder name {name}"
        ctx := { ctx with functions := ctx.functions.push (x.fvarId!, name) }
        funcs := funcs.push (Json.mkObj [("name", str name),
          ("domain", str domain), ("codomain", str codomain)])
      else
        if decl.binderInfo.isInstImplicit then
          throwError "unsupported parameter {name} : {← ppExpr ty}"
        let (nextCtx, nextPreds, value) ← structureValue ctx preds x.fvarId!
          #[] name x
        ctx := nextCtx
        preds := nextPreds
        structures := structures.push (Json.mkObj [("name", str name),
          ("lean_type", str (← ppFull ty)), ("lean_value", str value)])
      application := application.push (str argument)
    if !structures.isEmpty then
      let mut seen : Array String := #[]
      for name in names do
        if seen.contains name || name.startsWith "countermodel " then
          throwError "unsupported duplicate or reserved binder name {name} in structure model"
        seen := seen.push name
    let action : M Json := do
      let mut premises : Array Json := #[]
      for (name, ty) in hyps do
        let f ← formula ctx ty
        premises := premises.push (Json.mkObj [("name", str name), ("formula", f),
          ("lean", str (← ppFull ty))])
      let c ← formula ctx concl
      let st ← get
      return Json.mkObj [("theorem", str n.toString), ("carriers", Json.arr carriers),
        ("predicates", Json.arr preds), ("constants", Json.arr consts),
        ("functions", Json.arr funcs),
        ("structures", Json.arr structures),
        ("application", Json.arr application),
        ("premises", Json.arr premises),
        ("conclusion", Json.mkObj [("formula", c), ("lean", str (← ppFull concl))]),
        ("unfolded", Json.arr (st.unfolded.map (str ·.toString)))]
    action.run' {}

end Countermodel

unsafe def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: lean --run scripts/Countermodel.lean input.json"; return 2
  let input ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let modules ← IO.ofExcept (input.getObjValAs? (Array String) "modules")
  let thm ← IO.ofExcept (input.getObjValAs? String "theorem")
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (modules.map fun m => { module := m.toName }) {} (trustLevel := 1024) (loadExts := true)
  let ctx : Core.Context := { fileName := "<countermodel>", fileMap := default, maxHeartbeats := 0 }
  let action : MetaM Json := do
    try Countermodel.run thm.toName
    catch e => return Json.mkObj [("error", Json.str (← e.toMessageData.toString))]
  let (out, _) ← (MetaM.run' action).toIO ctx { env }
  IO.println out.compress
  return 0
