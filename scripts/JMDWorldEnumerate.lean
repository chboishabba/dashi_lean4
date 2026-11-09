/-
JMD Lean AST world: enumerate EXACT compiled module declarations.

Usage (in the selected repository's pinned Lean environment):
  lake env lean --run /path/to/JMDWorldEnumerate.lean My.Module Another.Module

Input modules must already compile to .olean under that environment.
No regexp source parsing, no LLM, no theorem promotion.
Output: module<TAB>constant-name<TAB>kind, lexicographically sorted.
-/
import Lean

namespace JMD.World.Enumerate

open Lean

private def constantKind (info : ConstantInfo) : String :=
  match info with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

unsafe def inspectModule (moduleString : String) : IO Unit := do
  if moduleString.isEmpty || moduleString.startsWith "-" then
    throw <| IO.userError "Module names must be nonempty and not flags"
  let moduleName := moduleString.toName
  let env ← importModules #[{module := moduleName}] {}
  let some idx := env.getModuleIdx? moduleName
    | throw <| IO.userError s!"Module was not loaded: {moduleString}"
  let some modData := env.header.moduleData[idx.toNat]?
    | throw <| IO.userError s!"Module data is absent: {moduleString}"
  let declarations := modData.constNames.qsort
    (fun a b => a.toString < b.toString)
  for name in declarations do
    let some info := env.checked.get.find? name
      | throw <| IO.userError s!"Indexed constant is not kernel checked: {name}"
    IO.println <| moduleString ++ "\t" ++ name.toString ++
      "\t" ++ constantKind info

end JMD.World.Enumerate

unsafe def main (args : List String) : IO Unit := do
  if args.isEmpty then
    throw <| IO.userError "Usage: JMDWorldEnumerate MODULE [MODULE ...]"
  for moduleString in args do
    JMD.World.Enumerate.inspectModule moduleString
