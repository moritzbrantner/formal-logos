/-
Report what Lean settles about each definition record's `lean_declaration`
(#1652 L3, owner direction 2026-11-16: "A lot of truth should be settled by
Lean ... What we can't describe in Lean, or haven't yet, should be described
in prose").

Usage, after `lake build`:

    lake env lean --run scripts/DefinitionStatus.lean <input.json>

`<input.json>` is `{"root_module": "TruthCore", "declarations": [...]}`. The
tool imports the root module (which imports every library module, not the
Challenges) and prints one JSON object per declaration, in input order:

- `found`: whether the name is a constant of the environment. A section
  `variable` is not a constant, so a definition record naming one is
  reported as not found;
- `module`: the defining module;
- `kind`: the constant's kind as Lean stores it: `definition`, `abbrev`,
  `instance`, `structure`, `class`, `inductive`, `constructor`, `projection`,
  `recursor`, `quotient`, `opaque`, `axiom` or `theorem`;
- `proof`: whether the constant's type is itself a proposition, so that the
  constant is a proof (a premise, law or constraint) rather than a notion;
- `structure`: for a projection, the structure it belongs to;
- `parameter_wrapper`: for a definition, whether its body, under its leading
  lambdas, applies one of its own parameters or a structure field to at least
  one argument and no argument mentions a constant of the root package (as
  `CanBe x r`, `causableAtLeast 5` or `n.issued p`). Such a definition only renames a parameter (a section
  variable abstracted at the end of the section, say): the parameter carries
  the meaning. A body that is a bare parameter (`def sensor (o r : Bool) :=
  o`) is a complete function and does not count;
- `head`: for a definition, the head constant of its body under the leading
  lambdas, if any: the one-step unfolding;
- `constants`: for a definition, the sorted constants of the root package
  that occur in its body, excluding itself and compiler auxiliaries.

Nothing is unfolded beyond the stored body. The classification of these facts
into the formal statuses `defined`, `primitive`, `constraint` and `unresolved`
is the policy of `truth definitions status` (truth/src/definition_status.rs),
documented in docs/corpus-model.md, "Formal status of definitions".
-/
import Lean

open Lean Meta

/-- Whether `n` was declared in a module under the root package. -/
def isLocal (env : Environment) (package : Name) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => match env.header.moduleNames[idx.toNat]? with
    | some m => m.getRoot == package
    | none => false
  | none => false

def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]?.map toString).getD ""
  | none => ""

def kindOf (env : Environment) (n : Name) : ConstantInfo → String
  | .defnInfo d =>
    if isInstanceCore env n then "instance"
    else if d.hints.isAbbrev then "abbrev"
    else "definition"
  | .inductInfo _ =>
    if isClass env n then "class"
    else if isStructure env n then "structure"
    else "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"

def describe (package : Name) (decl : Name) : MetaM Json := do
  let env ← getEnv
  let some info := env.find? decl
    | return Json.mkObj [("declaration", Json.str decl.toString), ("found", Json.bool false)]
  let kind := if (env.getProjectionFnInfo? decl).isSome then "projection" else kindOf env decl info
  let proof ← isProp info.type
  let mut out := Json.mkObj [
    ("declaration", Json.str decl.toString),
    ("found", Json.bool true),
    ("module", Json.str (moduleOf env decl)),
    ("kind", Json.str kind),
    ("proof", Json.bool proof)]
  if let some proj := env.getProjectionFnInfo? decl then
    if let some (.ctorInfo c) := env.find? proj.ctorName then
      out := out.mergeObj (Json.mkObj [("structure", Json.str c.induct.toString)])
  if let .defnInfo d := info then
    let (wrapper, head) ← lambdaTelescope d.value fun xs body => do
      let body := body.consumeMData
      let fn := body.getAppFn.consumeMData
      let args := body.getAppArgs
      let plainArgs := !args.isEmpty &&
        args.all fun a => a.getUsedConstants.all fun c => !isLocal env package c
      -- The head is a parameter, or a field of a project structure (a
      -- primitive packaged in a frame, as `n.issued p`); library fields such
      -- as `LE.le` are notation with a meaning, not project primitives.
      let primitiveHead := (fn.isFVar && xs.contains fn) ||
        (match fn with
         | .const n _ => isLocal env package n && (env.getProjectionFnInfo? n).isSome
         | _ => false)
      let wrapper := primitiveHead && plainArgs
      let head := match fn with
        | .const n _ => Json.str n.toString
        | _ => Json.null
      return (wrapper, head)
    let owned := d.value.getUsedConstants.filter fun c =>
      c != decl && !c.isInternalDetail && isLocal env package c
    let names := (owned.map toString).qsort (· < ·)
    let unique := names.foldl (init := (#[] : Array String)) fun acc n =>
      if acc.back? == some n then acc else acc.push n
    out := out.mergeObj (Json.mkObj [
      ("parameter_wrapper", Json.bool wrapper),
      ("head", head),
      ("constants", Json.arr (unique.map Json.str))])
  return out

unsafe def main (args : List String) : IO UInt32 := do
  let [path] := args
    | IO.eprintln "usage: lean --run scripts/DefinitionStatus.lean <input.json>"; return 2
  let input ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let root ← IO.ofExcept (input.getObjValAs? String "root_module")
  let decls ← IO.ofExcept (input.getObjValAs? (Array String) "declarations")
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let rootName := root.toName
  let env ← importModules #[{ module := rootName }] {} (trustLevel := 1024) (loadExts := true)
  let ctx : Core.Context := { fileName := "<definition-status>", fileMap := default, maxHeartbeats := 0 }
  let state : Core.State := { env }
  let (out, _) ← (MetaM.run' (decls.mapM fun d => describe rootName.getRoot d.toName)).toIO ctx state
  IO.println (Json.arr out).compress
  return 0
