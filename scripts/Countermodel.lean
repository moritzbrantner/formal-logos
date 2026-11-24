import Lean
/-!
First-order skeleton of a theorem for the omission-countermodel finder
(`truth countermodel`, `truth/src/countermodel.rs`, docs/countermodels.md).

Usage, after `lake build <module>`:

    lake env lean --run scripts/Countermodel.lean <input.json>

Input: `{"modules": [...], "theorem": "<name>"}`. The theorem's binders are
classified as carriers (`B : Type` or `Sort u`), predicate parameters (functions
from carriers, or from carrier-valued predicates `T → Prop`, into `Prop`),
element constants (`esse : R`), total unary functions between carriers, and
propositional hypotheses (premises). Each
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

structure Ctx where
  /-- Carrier free variables and their names. -/
  carriers : Array (FVarId × String) := #[]
  /-- Predicate parameters, element constants and bound variables. -/
  names : Array (FVarId × String) := #[]
  /-- Top-level unary carrier functions, kept distinct from predicate names. -/
  functions : Array (FVarId × String) := #[]
  /-- Structure binders (`F : CausalityFrame W B T R`) by their name. -/
  structs : Array (FVarId × String) := #[]
  /-- Fields of structure binders, by path (`F.history.IsAt`): the flat name
  of a predicate or element field (`F_history_IsAt`). -/
  fieldNames : Array (String × String) := #[]
  /-- Unary function fields, by path. -/
  fieldFunctions : Array (String × String) := #[]
  /-- Fields outside the fragment, by path, with their type: an error only
  when a premise or the conclusion mentions them. -/
  opaques : Array (String × String) := #[]

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

def lookupPath (xs : Array (String × String)) (p : String) : Option String :=
  (xs.find? (·.1 == p)).map (·.2)

/-- The path of a structure value built from a structure binder by
projections (`F.history.ontic` for `History.ontic (CausalityFrame.history F)`,
or its `Expr.proj` form). -/
partial def pathOf (ctx : Ctx) (e : Expr) : MetaM (Option String) := do
  let e := e.consumeMData
  match e with
  | .fvar f => return lookup ctx.structs f
  | .proj s i b =>
    let some base ← pathOf ctx b | return none
    let some f := (getStructureFields (← getEnv) s)[i]? | return none
    return some s!"{base}.{f}"
  | _ =>
    let .const p _ := e.getAppFn | return none
    let some info ← getProjectionFnInfo? p | return none
    let args := e.getAppArgs
    unless args.size == info.numParams + 1 do return none
    let some base ← pathOf ctx args[info.numParams]! | return none
    let some f := (getStructureFields (← getEnv) (p.getPrefix))[info.i]? | return none
    return some s!"{base}.{f}"

/-- A structure value in a form the extractor reads: an expression with a path
(`F.history.ontic`), or a constructor application. Projections are pushed
through constructors and definitions are unfolded on the way (recorded for the
certificate's `delta`): `Profile.ontic (groundProfile F concrete G)` becomes
`F.history.ontic`, since `groundProfile F concrete G` unfolds to
`⟨F.history.ontic, concrete, G⟩`. -/
partial def structValue (ctx : Ctx) (e : Expr) : M (Option Expr) := do
  if (← pathOf ctx e).isSome then return some e
  let e ← whnfCore e
  if (← pathOf ctx e).isSome then return some e
  -- field `i` of the (normalized) structure `b`, applied to `rest`
  let project (b : Expr) (i : Nat) (rebuild : Expr → Expr) (rest : Array Expr) : M (Option Expr) := do
    let some b' ← structValue ctx b | return none
    if (← pathOf ctx b').isSome then return some (mkAppN (rebuild b') rest)
    let .const c _ := b'.getAppFn | return none
    let some (.ctorInfo ci) := (← getEnv).find? c | return none
    let some v := b'.getAppArgs[ci.numParams + i]? | return none
    -- The field's value: read further when it is itself a structure.
    let r := (mkAppN v rest).headBeta
    return some ((← structValue ctx r).getD r)
  match e.getAppFn with
  | .proj sn i b => project b i (fun b' => .proj sn i b') e.getAppArgs
  | .const c _ =>
    if let some (.ctorInfo _) := (← getEnv).find? c then return some e
    let args := e.getAppArgs
    if let some info ← getProjectionFnInfo? c then
      if info.fromClass || args.size ≤ info.numParams then return none
      let rest := args.extract (info.numParams + 1) args.size
      return ← project args[info.numParams]! info.i
        (fun b' => mkAppN e.getAppFn (args.extract 0 info.numParams |>.push b')) rest
    let some e' ← unfoldDefinition? e | return none
    unless (← get).unfolded.contains c do
      modify fun st => { st with unfolded := st.unfolded.push c }
    structValue ctx e'
  | _ => return none

/-- A field of a structure binder at the head of `e`: its path and the
remaining arguments (`F.GivesAt v c x t` gives `F.GivesAt` and `v c x t`);
or, for a projection of a value that reduces to a constructor or a path
(`structValue`), `e` with that projection reduced (`.inr`). -/
def fieldHead (ctx : Ctx) (e : Expr) : M (Option ((String × Array Expr) ⊕ Expr)) := do
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  let fieldName (s : Name) (i : Nat) : MetaM (Option Name) :=
    return (getStructureFields (← getEnv) s)[i]?
  let (struct, sname, i, rest) ← match fn with
    | .proj sn i b => pure (b, sn, i, args)
    | .const p _ => do
      let some info ← getProjectionFnInfo? p | return none
      if info.fromClass || args.size ≤ info.numParams then return none
      pure (args[info.numParams]!, p.getPrefix, info.i, args.extract (info.numParams + 1) args.size)
    | _ => return none
  if let some base ← pathOf ctx struct then
    let some f ← fieldName sname i | return none
    return some (.inl (s!"{base}.{f}", rest))
  let some v ← structValue ctx (mkAppN fn (args.extract 0 (args.size - rest.size))) | return none
  if let some path ← pathOf ctx v then return some (.inl (path, rest))
  return some (.inr (mkAppN v rest).headBeta)

/-- A mentioned field outside the fragment: the precise error. -/
def opaqueField (ctx : Ctx) (path : String) : M Unit := do
  if let some ty := lookupPath ctx.opaques path then
    throwError "unsupported field {path} : {ty}"

/-- The first field outside the fragment that `e` mentions, if any. -/
partial def opaqueIn (ctx : Ctx) (e : Expr) : MetaM (Option (String × String)) := do
  if let some path ← pathOf ctx e then
    if let some ty := lookupPath ctx.opaques path then return some (path, ty)
  match e with
  | .app f a => return (← opaqueIn ctx f) <|> (← opaqueIn ctx a)
  | .lam _ d b _ | .forallE _ d b _ => return (← opaqueIn ctx d) <|> (← opaqueIn ctx b)
  | .mdata _ b | .proj _ _ b => opaqueIn ctx b
  | _ => return none

/-- An expression outside the fragment: the precise field error when it
mentions a field outside the fragment (`F.extra = []`), else the generic one. -/
def unsupportedIn (ctx : Ctx) (what : String) (e : Expr) : M α := do
  if let some (path, ty) ← opaqueIn ctx e then throwError "unsupported field {path} : {ty}"
  unsupported what e

mutual

partial def term (ctx : Ctx) (e : Expr) : M Json := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  if let .fvar f := e then
    if let some n := lookup ctx.names f then return Json.mkObj [("v", str n)]
  match ← fieldHead ctx e with
  | some (.inr e') => return ← term ctx e'
  | some (.inl (path, rest)) =>
    opaqueField ctx path
    if let some n := lookupPath ctx.fieldFunctions path then
      if rest.size != 1 then unsupported "unary function application" e
      return Json.mkObj [("app", str n), ("arg", ← term ctx rest[0]!)]
    if rest.isEmpty then
      if let some n := lookupPath ctx.fieldNames path then
        return Json.mkObj [("v", str n)]
  | none => pure ()
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
  unsupportedIn ctx "term" e

partial def binder (ctx : Ctx) (q : String) (n : Name) (dom body : Expr) (bi : BinderInfo) : M Json := do
  let s? ← if dom.consumeMData.isProp then pure (some (str "Prop")) else sortOf ctx dom
  if s?.isNone then
    -- A carrier bundled in a structure (`frame.Carrier`): name the field.
    if let some (.inl (path, _)) ← fieldHead ctx dom.consumeMData then opaqueField ctx path
  let some s := s? | unsupported "quantifier domain" dom
  if (s.getObjVal? "set").isOk then unsupported "quantifier over predicates" dom
  withLocalDecl n bi dom fun x => do
    let v ← fresh n
    let b ← formula { ctx with names := ctx.names.push (x.fvarId!, v) } (body.instantiate1 x)
    return Json.mkObj [("t", str q), ("v", str v), ("sort", s), ("body", b)]

partial def formula (ctx : Ctx) (e : Expr) : M Json := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  if let .forallE n dom body bi := e then
    if (← isProp dom) && !body.hasLooseBVars then
      return Json.mkObj [("t", str "imp"), ("a", ← formula ctx dom), ("b", ← formula ctx body)]
    return ← binder ctx "forall" n dom body bi
  match ← fieldHead ctx e with
  | some (.inr e') => return ← formula ctx e'
  | some (.inl (path, rest)) =>
    opaqueField ctx path
    if let some p := lookupPath ctx.fieldNames path then
      return Json.mkObj [("t", str "atom"), ("p", str p), ("args", Json.arr (← rest.mapM (term ctx)))]
  | none => pure ()
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
    if args.size == 3 && (carrierOf ctx args[0]!).isSome then
      return Json.mkObj [("t", str "eq"), ("a", ← term ctx args[1]!), ("b", ← term ctx args[2]!)]
  | .const ``Ne _ =>
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
  unsupportedIn ctx "formula" e

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

/-- The structure a type unfolds to (reducibly: `GProfile W B` is `Profile W B`). -/
def structureOf (ty : Expr) : MetaM (Option Name) := do
  let ty ← whnfR ty
  let .const c _ := ty.getAppFn | return none
  return if isStructure (← getEnv) c then some c else none

/-- What a structure binder contributes, field by field, recursively: flat
predicate, element and function names; opaque fields; and the structure
values to build, inner ones first (`{"name", "type", "fields"}`, a field
`null` when it is opaque and rendered `default`). -/
structure Expansion where
  ctx : Ctx
  preds : Array Json := #[]
  consts : Array Json := #[]
  funcs : Array Json := #[]
  structures : Array Json := #[]
  opaques : Array Json := #[]

/-- Expands the structure value `v : ty` at `path` (rendered as `name`). A
proof field cannot be built by a finite certificate: that is the precise
"unsupported field" error. Any other field outside the fragment is opaque:
rendered `default`, and an error only where a formula mentions it. -/
partial def expand (pp : Expr → MetaM String) (x : Expansion) (path name : String) (v ty : Expr) :
    MetaM Expansion := do
  let some s ← structureOf ty | throwError "not a structure: {path}"
  let mut x := x
  let mut fields : Array Json := #[]
  for f in getStructureFields (← getEnv) s do
    let fp := s!"{path}.{f}"
    let fn := s!"{name}_{f}"
    let proj ← mkProjection v f
    let fty ← instantiateMVars (← inferType proj)
    let ctx := x.ctx
    if ← isProp fty then
      throwError "unsupported field {fp} : {← pp fty} (a proof field: a finite certificate cannot construct it)"
    if fty.isProp then
      let p := Json.mkObj [("name", str fn), ("args", Json.arr #[]), ("field", str fp)]
      x := { x with ctx := { ctx with fieldNames := ctx.fieldNames.push (fp, fn) }, preds := x.preds.push p }
    else if let some c := carrierOf ctx fty then
      let k := Json.mkObj [("name", str fn), ("sort", str c), ("field", str fp)]
      x := { x with ctx := { ctx with fieldNames := ctx.fieldNames.push (fp, fn) }, consts := x.consts.push k }
    else if let some args ← predicateArgs ctx fty then
      let p := Json.mkObj [("name", str fn), ("args", Json.arr args), ("field", str fp)]
      x := { x with ctx := { ctx with fieldNames := ctx.fieldNames.push (fp, fn) }, preds := x.preds.push p }
    else if let some (domain, codomain) ← unaryFunctionSorts ctx fty then
      let f := Json.mkObj [("name", str fn), ("domain", str domain),
        ("codomain", str codomain), ("field", str fp)]
      x := { x with ctx := { ctx with fieldFunctions := ctx.fieldFunctions.push (fp, fn) }, funcs := x.funcs.push f }
    else if (← structureOf fty).isSome then
      x ← expand pp x fp fn proj fty
    else
      let t ← pp fty
      let o := Json.mkObj [("field", str fp), ("type", str t)]
      x := { x with ctx := { ctx with opaques := ctx.opaques.push (fp, t) }, opaques := x.opaques.push o }
      fields := fields.push Json.null
      continue
    fields := fields.push (str fn)
  let built := Json.mkObj [("name", str name), ("type", str (← pp ty)), ("fields", Json.arr fields)]
  return { x with structures := x.structures.push built }

def run (n : Name) : MetaM Json := do
  let some info := (← getEnv).find? n | throwError "unknown declaration {n}"
  forallTelescope info.type fun xs concl => do
    let mut ctx : Ctx := {}
    let mut carriers : Array Json := #[]
    let mut preds : Array Json := #[]
    let mut consts : Array Json := #[]
    let mut funcs : Array Json := #[]
    let mut names : Array String := #[]
    let mut hyps : Array (String × Expr) := #[]
    let mut structures : Array Json := #[]
    let mut opaques : Array Json := #[]
    let pp (e : Expr) : MetaM String := do
      return toString (← withOptions (fun o => o.setBool `pp.fullNames true) (ppExpr e))
    for x in xs do
      let decl ← x.fvarId!.getDecl
      let name := decl.userName.eraseMacroScopes.toString
      if ctx.functions.any (fun entry => entry.2 == name) then
        throwError "unsupported duplicate function binder name {name}"
      let reusedName := names.contains name
      names := names.push name
      let ty ← instantiateMVars decl.type
      if ty.isProp then
        ctx := { ctx with names := ctx.names.push (x.fvarId!, name) }
        preds := preds.push (Json.mkObj [("name", str name), ("args", Json.arr #[])])
      else if ty.isSort then
        ctx := { ctx with carriers := ctx.carriers.push (x.fvarId!, name) }
        carriers := carriers.push (str name)
      else if ← isProp ty then
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
      else if (← structureOf ty).isSome && !decl.binderInfo.isInstImplicit then
        -- A structure binder (a shared frame, a profile): its fields become
        -- typed tables, and the certificate builds it by its constructor.
        ctx := { ctx with structs := ctx.structs.push (x.fvarId!, name) }
        let e ← expand pp { ctx := ctx } name name x ty
        ctx := e.ctx
        preds := preds ++ e.preds
        consts := consts ++ e.consts
        funcs := funcs ++ e.funcs
        structures := structures ++ e.structures
        opaques := opaques ++ e.opaques
      else
        throwError "unsupported parameter {name} : {← ppExpr ty}"
    -- Flat field names must not collide with binder names or each other.
    let flat := (preds ++ consts ++ funcs).filterMap fun j => (j.getObjValAs? String "name").toOption
    for i in [0:flat.size] do
      if flat.extract 0 i |>.contains flat[i]! then
        throwError "unsupported duplicate name {flat[i]!} (a structure field's flat name)"
    let action : M Json := do
      let mut premises : Array Json := #[]
      for (name, ty) in hyps do
        let f ← formula ctx ty
        premises := premises.push (Json.mkObj [("name", str name), ("formula", f),
          ("lean", str (← pp ty))])
      let c ← formula ctx concl
      let st ← get
      return Json.mkObj [("theorem", str n.toString), ("carriers", Json.arr carriers),
        ("predicates", Json.arr preds), ("constants", Json.arr consts),
        ("functions", Json.arr funcs),
        ("structures", Json.arr structures),
        ("opaque_fields", Json.arr opaques),
        ("premises", Json.arr premises),
        ("conclusion", Json.mkObj [("formula", c), ("lean", str (← pp concl))]),
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
