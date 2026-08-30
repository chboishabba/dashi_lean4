/-
Dump the real declaration-level dependency graph of the development.

Run from the repository root:

    lake env lean tools/DepDump.lean

It writes `docs/status/deps.json`: one record per declaration defined in a
`RequestProject.*` module, with the module it lives in, whether it is a
proposition (theorem) or data (definition), and the `RequestProject`
declarations it uses.  `tools/provenance.py` consumes this file.
-/
import RequestProject.All

open Lean

namespace DepDump

/-- Is `m` a module of this development? -/
def isProjectModule (m : Name) : Bool := (`RequestProject).isPrefixOf m

def escape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++ (match c with
      | '"' => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | c => c.toString)

unsafe def collect : CoreM String := do
  let env ← getEnv
  let mut records : Array String := #[]
  let moduleNames := env.header.moduleNames
  for (name, info) in env.constants.toList do
    if name.isInternal then continue
    let some idx := env.getModuleIdxFor? name | continue
    let mod := moduleNames[idx.toNat]!
    unless isProjectModule mod do continue
    let isThm :=
      match info with
      | .thmInfo _ => true
      | _ => false
    let mut used : NameSet := {}
    for c in info.type.getUsedConstants do
      used := used.insert c
    match info.value? with
    | some v => for c in v.getUsedConstants do used := used.insert c
    | none => pure ()
    let mut deps : Array String := #[]
    for c in used.toList do
      if c == name then continue
      if c.isInternal then continue
      match env.getModuleIdxFor? c with
      | some j =>
        if isProjectModule moduleNames[j.toNat]! then
          deps := deps.push s!"\"{escape c.toString}\""
      | none => pure ()
    records := records.push <|
      "{\"name\":\"" ++ escape name.toString ++ "\",\"module\":\"" ++ escape mod.toString ++
      "\",\"kind\":\"" ++ (if isThm then "thm" else "def") ++ "\",\"uses\":[" ++
      String.intercalate "," deps.toList ++ "]}"
  return "[\n" ++ String.intercalate ",\n" records.toList ++ "\n]\n"

end DepDump

unsafe def dump : IO Unit := do
  let env ← importModules #[{ module := `RequestProject.All }] {}
  let (out, _) ← (DepDump.collect).toIO { fileName := "<dump>", fileMap := default } { env := env }
  IO.FS.createDirAll "docs/status"
  IO.FS.writeFile "docs/status/deps.json" out
  IO.println s!"wrote docs/status/deps.json ({out.length} bytes)"

#eval dump
