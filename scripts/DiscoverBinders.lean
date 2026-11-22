/-
Binder export for the agent-guided discovery recipe (#1832, docs/discover.md,
"Agent-guided blueprint pilot").

  lake env lean --run scripts/DiscoverBinders.lean <ROOT-MODULE> <declarations.txt>

For each declaration named in `<declarations.txt>` (one per line) it prints one
JSON line: the declaration, its module, and its binders in order, each as
`[name, isCarrier, isInstance]`, where a carrier is a binder whose type is a
sort (`B : Type`, `Being : Sort u`). It unfolds nothing and asserts nothing:
`scripts/discover_blueprint.py diagnose` uses it to say which binders of a
known derivation `truth discover` cannot identify with the target's (different
name or module, no shared whole-binder sense tag).
-/
import Lean

open Lean

def binders : Expr → List (String × Bool × Bool)
  | .forallE n d body bi => (n.toString, d.isSort, bi.isInstImplicit) :: binders body
  | _ => []

def main (args : List String) : IO UInt32 := do
  let [root, file] := args
    | IO.eprintln "usage: lean --run scripts/DiscoverBinders.lean <ROOT-MODULE> <declarations.txt>"
      return 2
  let decls := (← IO.FS.lines file).filterMap fun line =>
    let line := line.trimAscii.toString
    if line.isEmpty then none else some line.toName
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := root.toName }] {} (loadExts := false)
  for d in decls do
    match env.find? d with
    | none =>
      IO.println (Json.compress (Json.mkObj [("declaration", Json.str d.toString),
        ("error", Json.str "unknown declaration")]))
    | some info =>
      let module := match env.getModuleIdxFor? d with
        | some idx => (env.header.moduleNames[idx.toNat]?.map toString).getD ""
        | none => ""
      let bs := (binders info.type).map fun (n, carrier, inst) =>
        Json.arr #[Json.str n, Json.bool carrier, Json.bool inst]
      IO.println (Json.compress (Json.mkObj [("declaration", Json.str d.toString),
        ("module", Json.str module), ("binders", Json.arr bs.toArray)]))
  return 0
