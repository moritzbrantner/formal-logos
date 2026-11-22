/-
Advisory vocabulary export for bridge-candidate ranking (#415).

Run after a normal lake build, without rebuilding:
  lake env lean --run scripts/StatementConstants.lean <ROOT-MODULE> <declarations.txt>

`<declarations.txt>` holds one fully qualified declaration name per line
(normally every statement `lean_declaration`). For each name the tool prints
one JSON object with the defining module, the binder names of its type, the
head constant of each binder's type and, for a binder whose type is a local
structure, the head constants of its fields' types (`truth discover` ranks a
premise whose structure binder projects to a target binder's type, #1819), and
the sorted TruthCore-local constants that occur syntactically in its type and,
for a definition, its stored body (the declaration itself included). Nothing
is unfolded. Shared constants are a ranking signal only: they are not
evidence of entailment, equivalence or a common interpretation.
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

def describe (env : Environment) (package : Name) (decl : Name) : Json :=
  match env.find? decl with
  | none => Json.mkObj [("declaration", Json.str decl.toString), ("error", Json.str "unknown declaration")]
  | some info =>
    let body := match info with
      | .defnInfo d => d.value.getUsedConstants
      | _ => #[]
    let used := (info.type.getUsedConstants ++ body).push decl
    let owned := used.filter fun n => !n.isInternal && isLocal env package n
    let names := (owned.map toString).qsort (· < ·)
    let unique := names.foldl (init := (#[] : Array String)) fun acc n =>
      if acc.back? == some n then acc else acc.push n
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
      ("constants", Json.arr (unique.map Json.str))]

def main (args : List String) : IO UInt32 := do
  let [root, file] := args
    | IO.eprintln "usage: lean --run scripts/StatementConstants.lean <ROOT-MODULE> <declarations.txt>"
      return 2
  let decls := (← IO.FS.lines file).filterMap fun line =>
    let line := line.trimAscii.toString
    if line.isEmpty then none else some line.toName
  initSearchPath (← findSysroot)
  let rootName := root.toName
  let env ← importModules #[{ module := rootName }] {}
  let rows := decls.map (describe env rootName.getRoot)
  IO.println (Json.arr rows).compress
  return 0
