/-
Advisory vocabulary export for bridge-candidate ranking (#415).

Run after a normal lake build, without rebuilding:
  lake env lean --run scripts/StatementConstants.lean <ROOT-MODULE> <declarations.txt>

`<declarations.txt>` holds one fully qualified declaration name per line
(normally every statement `lean_declaration`). For each name the tool prints
one JSON object with the defining module, the binder names of its type, the
head constant of each binder's type and, for a binder whose type is a local
structure, the head constants of its fields' types (`truth discover` ranks a
premise whose structure binder projects to a target binder's type, #1819), for
each binder used only through field projections the heads of those fields'
types (a premise that speaks of a structure only through one field, #1845), and
the sorted TruthCore-local constants that occur syntactically in its type and,
for a definition, its stored body (the declaration itself included). Nothing
is unfolded. Shared constants are a ranking signal only: they are not
evidence of entailment, equivalence or a common interpretation.

With a third argument `--closure` it also prints one row for every
TruthCore-local constant reachable from the listed ones through those
constant lists (type and stored body, transitively), each once, in
breadth-first order. `truth definitions residue` reads this closure to tell
whether a definition's declaration occurs in a statement's own type, is reached
only by unfolding, or is not reached at all (#1926, #216).
-/
import Lean

open Lean

/-- Whether `n` was declared in a module under the root package. -/
def isLocal (env : Environment) (package : Name) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => match env.header.moduleNames[idx.toNat]? with
    | some m => m.getRoot == package
    | none => false
  | none => false

def binderNames : Expr → List String
  | .forallE n _ body _ => n.toString :: binderNames body
  | _ => []

/-- The local head constant of a type (`""` when none or not local). -/
def headOf (env : Environment) (package : Name) (ty : Expr) : String :=
  match ty.getAppFn with
  | .const c _ => if isLocal env package c then c.toString else ""
  | _ => ""

/-- A type under its first `n` `∀` binders. -/
def dropForalls : Nat → Expr → Expr
  | n + 1, .forallE _ _ body _ => dropForalls n body
  | _, e => e

/-- Each binder's local type head, and the local heads of its structure's
field types (empty when the binder's type is no local structure). -/
def binderTypes (env : Environment) (package : Name) : Expr → List (String × Array String)
  | .forallE _ d body _ =>
    let fields := match d.getAppFn with
      | .const s _ =>
        if isLocal env package s && isStructure env s then
          let params := match env.find? s with
            | some (.inductInfo v) => v.numParams
            | _ => 0
          (getStructureFields env s).filterMap fun f => do
            let proj ← getProjFnForField? env s f
            let info ← env.find? proj
            -- The field's type: under the structure's parameters and `self`
            -- only, so a function-valued field has no head.
            let h := headOf env package (dropForalls (params + 1) info.type)
            if h.isEmpty then none else some h
        else #[]
      | _ => #[]
    (headOf env package d, fields) :: binderTypes env package body
  | _ => []

/-- The type head of the field that projection function `proj` returns (`""`
when none or not local). -/
def projectionHead (env : Environment) (package : Name) (proj : Name) : String :=
  match env.getProjectionFnInfo? proj, env.find? proj with
  | some info, some c => headOf env package (dropForalls (info.numParams + 1) c.type)
  | _, _ => ""

/-- How the free variable `x` occurs in `e`: the projection functions it is
the structure argument of (`Profile.ontic m`, or a primitive `m.1`), and
whether it also occurs otherwise (bare: passed whole, or in a type). -/
partial def occurrences (env : Environment) (x : Expr) (e : Expr) :
    StateM (Array Name × Bool) Unit := do
  if e == x then
    modify fun (fs, _) => (fs, true)
    return
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if let .const c _ := fn then
      if let some info := env.getProjectionFnInfo? c then
        if h : info.numParams < args.size then
          if args[info.numParams] == x then
            modify fun (fs, b) => (if fs.contains c then fs else fs.push c, b)
            for a in args.extract 0 info.numParams do occurrences env x a
            for a in args.extract (info.numParams + 1) args.size do occurrences env x a
            return
    occurrences env x fn
    for a in args do occurrences env x a
  | .proj s i b =>
    if b == x then
      let fields := getStructureFields env s
      match fields[i]? >>= fun f => getProjFnForField? env s f with
      | some p => modify fun (fs, bare) => (if fs.contains p then fs else fs.push p, bare)
      | none => modify fun (fs, _) => (fs, true)
    else occurrences env x b
  | .lam _ d b _ | .forallE _ d b _ => do occurrences env x d; occurrences env x b
  | .letE _ t v b _ => do occurrences env x t; occurrences env x v; occurrences env x b
  | .mdata _ b => occurrences env x b
  | _ => pure ()

/-- For each binder of the declaration's type: when the binder occurs in the
statement only as the structure argument of field projections, the type heads
of those fields (`OnticFrameKT (m : Profile W B) := FrameSatisfies .KT
m.ontic.frame` uses `m` only through `ontic : Ontic W B`; occurrences in later
binders' types count alike); otherwise empty: it occurs bare somewhere (passed
whole, also within a later binder's type), through a field whose type has no
local head, or not at all. A premise that speaks of
its structure binder only through one field is a statement about that field's
value (#1845). The binders of a definition are read from its value's leading
lambdas, else from the type's `∀` binders. -/
def binderUses (env : Environment) (package : Name) (info : ConstantInfo) : List (Array String) := Id.run do
  let n := (binderNames info.type).length
  -- Open the binders with fresh free variables (no local context is needed
  -- for a syntactic scan).
  let open_ (e : Expr) (k : Nat) : Array Expr × Expr × Array Expr := Id.run do
    let mut e := e
    let mut xs : Array Expr := #[]
    let mut doms : Array Expr := #[]
    for i in [0:k] do
      match e with
      | .lam _ d b _ | .forallE _ d b _ =>
        let x := mkFVar ⟨Name.mkNum `_discoverBinder i⟩
        doms := doms.push (d.instantiateRev xs)
        xs := xs.push x
        e := b
      | _ => break
    return (xs, e.instantiateRev xs, doms)
  let (xs, body, doms) := match info with
    | .defnInfo d =>
      let (xs, body, doms) := open_ d.value n
      if xs.size == n then (xs, body, doms) else open_ info.type n
    | _ => open_ info.type n
  let mut out : List (Array String) := []
  for i in [0:n] do
    match xs[i]? with
    | none => out := out ++ [#[]]
    | some x =>
      let mut st : Array Name × Bool := (#[], false)
      for d in doms.extract (i + 1) doms.size do
        st := ((occurrences env x d).run st).2
      st := ((occurrences env x body).run st).2
      let (fs, bare) := st
      if bare || fs.isEmpty then out := out ++ [#[]]
      else
        let heads := fs.map (projectionHead env package)
        out := out ++ [if heads.any (·.isEmpty) then #[] else heads]
  return out

/-- The sorted TruthCore-local constants of a declaration's type and, for a
definition, its stored body (the declaration itself included). -/
def localConstants (env : Environment) (package : Name) (decl : Name) (info : ConstantInfo) :
    Array Name :=
  let body := match info with
    | .defnInfo d => d.value.getUsedConstants
    | _ => #[]
  let used := (info.type.getUsedConstants ++ body).push decl
  let owned := used.filter fun n => !n.isInternal && isLocal env package n
  let sorted := owned.qsort (·.toString < ·.toString)
  sorted.foldl (init := (#[] : Array Name)) fun acc n =>
    if acc.back? == some n then acc else acc.push n

def describe (env : Environment) (package : Name) (decl : Name) : Json :=
  match env.find? decl with
  | none => Json.mkObj [("declaration", Json.str decl.toString), ("error", Json.str "unknown declaration")]
  | some info =>
    let unique := (localConstants env package decl info).map toString
    let module := match env.getModuleIdxFor? decl with
      | some idx => (env.header.moduleNames[idx.toNat]?.map toString).getD ""
      | none => ""
    Json.mkObj [
      ("declaration", Json.str decl.toString),
      ("module", Json.str module),
      ("binders", Json.arr ((binderNames info.type).map Json.str).toArray),
      ("binder_types", Json.arr ((binderTypes env package info.type).map (Json.str ·.1)).toArray),
      ("binder_fields", Json.arr ((binderTypes env package info.type).map fun (_, fs) =>
        Json.arr (fs.map Json.str)).toArray),
      ("binder_uses", Json.arr ((binderUses env package info).map fun hs =>
        Json.arr (hs.map Json.str)).toArray),
      ("constants", Json.arr (unique.map Json.str))]

/-- The listed declarations followed by every local constant reachable from
them through `localConstants`, each once, in breadth-first order. -/
def closure (env : Environment) (package : Name) (decls : Array Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut order : Array Name := #[]
  for d in decls do
    if !seen.contains d then
      seen := seen.insert d
      order := order.push d
  let mut i := 0
  -- Each name enters `order` once, so the loop ends once `order` is exhausted.
  while i < order.size do
    let d := order[i]!
    i := i + 1
    if let some info := env.find? d then
      for c in localConstants env package d info do
        if !seen.contains c then
          seen := seen.insert c
          order := order.push c
  return order

def main (args : List String) : IO UInt32 := do
  let (root, file, transitive) ← match args with
    | [root, file] => pure (root, file, false)
    | [root, file, "--closure"] => pure (root, file, true)
    | _ =>
      IO.eprintln "usage: lean --run scripts/StatementConstants.lean <ROOT-MODULE> <declarations.txt> [--closure]"
      return 2
  let decls := (← IO.FS.lines file).filterMap fun line =>
    let line := line.trimAscii.toString
    if line.isEmpty then none else some line.toName
  initSearchPath (← findSysroot)
  let rootName := root.toName
  let env ← importModules #[{ module := rootName }] {}
  let decls := if transitive then closure env rootName.getRoot decls else decls
  let rows := decls.map (describe env rootName.getRoot)
  IO.println (Json.arr rows).compress
  return 0
