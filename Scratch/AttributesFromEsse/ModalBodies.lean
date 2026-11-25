import Lean
open Lean

def marker (n : Name) : Bool :=
  ["NecessaryAt", "ContingentAt", "access", "Box", "Diamond", "box", "diamond",
   "NecessaryBeing", "IsNecessary", "NecessaryExistence"].contains n.getString!

def hasMarker (env : Environment) (n : Name) (depth : Nat) : Bool := Id.run do
  if marker n then return true
  match env.find? n with
  | some (.defnInfo d) =>
    let cs := d.value.getUsedConstants.filter (fun k => k.getRoot == `TruthCore)
    match depth with
    | 0 => return cs.any marker
    | k + 1 => return cs.any (fun c => hasMarker env c k)
  | _ => return false

/-- One declared name per line. Extra imports support replay against a prepared
snapshot whose root aggregator predates one of its modules. -/
def main (args : List String) : IO Unit := do
  let names :: extra := args | throw (IO.userError "expected the declaration-list path")
  initSearchPath (← findSysroot)
  let imports : Array Import := (("TruthCore" :: extra).map (fun s => {module := s.toName})).toArray
  let env ← importModules imports {}
  for line in ← IO.FS.lines names do
    let n := line.trimAscii.toString.toName
    if (env.find? n).isNone then throw (IO.userError ("missing declaration: " ++ toString n))
    else if hasMarker env n 2 then IO.println ("modal " ++ toString n)
