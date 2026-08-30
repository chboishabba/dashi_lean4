/-
# AristotleExporter — a generic, drop-in NotebookLM exporter for Lean 4 projects

This file is a self-contained Lean 4 metaprogramming plugin. Drop it into any
active Lean project (it only needs `import Lean`), point it at a target
declaration, and it will:

1.  **Reflect** the full dependency graph of the target using Lean's environment
    metadata (`ConstantInfo`, `Expr.getUsedConstants`).
2.  **Partition** that graph into two pieces (graph partitioning / a *cut*):
    * the **project partition** — the declarations defined in your own source
      modules; and
    * the **core-library partition** — everything that lives in Mathlib / Std /
      the Lean core.
    The partition is decided by the *module each declaration is defined in*
    (`Environment.getModuleIdxFor?`), not by guessing from names — so core
    standard-library declarations such as `Nat.add` or `List.foldl`, whose names
    are not under `Lean.*`, are still correctly recognised as library code.
    The traversal recurses *through* project declarations but **stops at the
    boundary** the moment it reaches a core-library declaration. Those boundary
    declarations are recorded as a *frontier* (the "reasonable level" to stop at)
    instead of being followed all the way down to the foundational axioms. This
    means you do **not** re-export the bedrock of Mathlib on every run.
3.  **Order it top-down**: inside the project partition the target *result* is
    emitted first, followed by the lemmas/definitions it rests on. This is the
    reverse of the usual bottom-up build order, which is exactly what NotebookLM
    benefits from (the "crown jewels" are read first, then the premises that
    ground them). The core-library frontier is grouped *away* into its own files.
4.  **Chunk & write** the pretty-printed declarations into plain-text files,
    capped at a configurable number of words per file (default `500000`) and a
    configurable maximum number of files (default `50`). The project partition is
    written first (`notebook_lm_part_*.txt`) and always gets first claim on the
    file budget; the core-library frontier is written into its own group of files
    (`core_library_part_*.txt`) with whatever budget remains.

## Usage

Programmatic (full control over the configuration):

```
open AristotleExporter in
run_cmd Command.liftTermElabM do
  AristotleExporter.runExport `my_final_theorem
    { outputDir := "notebook_lm_files", maxWordsPerFile := 500000, maxFiles := 50 }
```

Quick command form (uses the default configuration):

```
#exportToNotebookLM my_final_theorem
```

Quick command form with a custom output directory:

```
#exportToNotebookLM my_final_theorem into "my_output_dir"
```
-/
import Lean

open Lean Meta Elab Command

namespace AristotleExporter

/-- Configuration for an export run. -/
structure ExportConfig where
  /-- Maximum number of (whitespace-separated) words written to a single file. -/
  maxWordsPerFile : Nat := 500000
  /-- Maximum number of output files (shared across both partitions). The project
      partition is written first, so it always gets first claim on this budget;
      foundational/frontier declarations beyond the ceiling are dropped. -/
  maxFiles        : Nat := 50
  /-- Directory the output `*.txt` files are written into. -/
  outputDir       : System.FilePath := "notebook_lm_files"
  /-- Module-name prefixes that define the **project partition**: a declaration
      belongs to the project iff it is defined locally (in the module under
      compilation) or in an imported module whose name starts with one of these
      prefixes. When left empty (the default) the project root is auto-derived
      from the module that defines the export target (e.g. targeting something in
      `MyProj.Foo` makes `MyProj` the project root). Everything outside the
      project is core library. -/
  projectModules  : List String := []
  /-- Declarations whose fully-qualified *name* starts with any of these prefixes
      are pure compiler/tooling noise: they are neither emitted nor recorded on
      the frontier (this keeps the metaprogramming API out of the export). -/
  ignorePrefixes  : List String :=
    ["Lean", "Init", "Core"]
  /-- If `true`, the boundary is ignored and the traversal recurses through the
      core library all the way down to the foundational axioms (the old,
      "go to bedrock" behaviour). Defaults to `false`: stop at the frontier. -/
  expandBoundary  : Bool := false
  deriving Inhabited

/-- Count whitespace-separated words in `s` (handles spaces, tabs, newlines). -/
def estimateWords (s : String) : Nat :=
  (s.foldl (fun (acc, inWord) c =>
      if c.isWhitespace then (acc, false)
      else (if inWord then acc else acc + 1, true)) (0, false)).1

/-- Human-readable tag for the kind of a declaration. -/
def kindTag : ConstantInfo → String
  | .axiomInfo _  => "AXIOM"
  | .thmInfo _    => "THEOREM"
  | .defnInfo _   => "DEFINITION"
  | .opaqueInfo _ => "OPAQUE"
  | .ctorInfo _   => "CONSTRUCTOR"
  | .inductInfo _ => "INDUCTIVE"
  | .recInfo _    => "RECURSOR"
  | .quotInfo _   => "QUOT"

/-- Does `name` start with any prefix in `prefixes`? -/
def matchesAny (name : Name) (prefixes : List String) : Bool :=
  let s := name.toString
  prefixes.any (fun p => s.startsWith p)

/-- The module in which `name` is defined, or `none` if it is declared locally in
the module currently being compiled. -/
def declModule (env : Environment) (name : Name) : Option Name :=
  (env.getModuleIdxFor? name).map (fun idx => env.header.moduleNames[idx.toNat]!)

/-- Is `name` part of the project partition? A declaration is "project" iff it is
local (defined in the module under compilation) or its defining module name
starts with one of `projectModules`. Everything else is core library. -/
def isProjectDecl (env : Environment) (name : Name) (projectModules : List String) : Bool :=
  match declModule env name with
  | none   => true
  | some m => projectModules.any (fun p => m.toString.startsWith p)

/-- The mutable state threaded through the partitioned traversal. -/
structure TraverseState where
  /-- Declarations already visited (cycle / re-visit guard). -/
  visited       : Array Name := #[]
  /-- Top-down ordered, fully formatted blocks for the project partition. -/
  projectBlocks : Array String := #[]
  /-- Names of the core-library declarations on the frontier (the graph cut),
      i.e. the boundary declarations the project directly rests on. -/
  frontier      : Array Name := #[]
  deriving Inhabited

/--
Trace the dependencies of `targetName`, partitioning the graph (by defining
module) into the project and the core library.

* Project declarations are emitted *before* their own dependencies are visited (a
  pre-order DFS), producing the result-first ordering, and the traversal recurses
  into them.
* Core-library declarations are recorded on the `frontier` and **not** recursed
  into — this is the graph cut that stops the walk at a reasonable level instead
  of descending to the Mathlib/Lean bedrock. (If `cfg.expandBoundary` is set,
  library declarations are treated as project code and fully expanded instead.)
* Declarations whose *name* matches `cfg.ignorePrefixes` are skipped entirely.

`projectModules` is the resolved (auto-derived if necessary) list of project
module prefixes. Cycles and re-visits are guarded by a `visited` set.
-/
partial def exportTopDown (targetName : Name) (cfg : ExportConfig)
    (projectModules : List String) : MetaM TraverseState := do
  let env ← getEnv
  let some info0 := env.find? targetName
    | return { projectBlocks :=
        #[s!"-- Error: identifier `{targetName}` not found in environment."] }
  let (_, st) ← (visit info0).run {}
  return st
where
  visit (info : ConstantInfo) : StateT TraverseState MetaM Unit := do
    if (← get).visited.contains info.name then return
    -- mark visited
    modify fun s => { s with visited := s.visited.push info.name }
    -- format this declaration (full block: type + proof/definition)
    let typeFmt ← ppExpr info.type
    let mut itemStr :=
      s!"\n=== [{kindTag info}] {info.name} ===\nType / Statement:\n{typeFmt}\n"
    match info.value? with
    | some val =>
        let valFmt ← ppExpr val
        itemStr := itemStr ++ s!"Proof / Definition:\n{valFmt}\n"
    | none =>
        itemStr := itemStr ++ "Proof / Definition: [primitive — axiom or core declaration]\n"
    itemStr := itemStr ++ "====================================================\n"
    -- push BEFORE recursing  =>  result-first (top-down) ordering
    modify fun s => { s with projectBlocks := s.projectBlocks.push itemStr }
    -- gather and recurse into dependencies, respecting the graph cut
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? then
      deps := deps ++ value.getUsedConstants
    let env ← getEnv
    for dep in deps do
      -- pure compiler/tooling noise: ignore completely
      if matchesAny dep cfg.ignorePrefixes then continue
      -- core-library boundary: record on the frontier and STOP (do not recurse)
      if !cfg.expandBoundary && !isProjectDecl env dep projectModules then
        if !(← get).frontier.contains dep then
          modify fun s => { s with frontier := s.frontier.push dep }
        continue
      if let some depInfo := env.find? dep then
        visit depInfo

/-- Format the core-library frontier into lightweight, grouped blocks (one per
boundary declaration). Only the *statement* is shown — the whole point of the cut
is that we stop here and do not expand the proof/definition of library lemmas.
Names are sorted so declarations cluster by namespace / module. -/
def formatFrontier (frontier : Array Name) : MetaM (Array String) := do
  let env ← getEnv
  let sorted := frontier.qsort (fun a b => a.toString < b.toString)
  let mut blocks := #[]
  for name in sorted do
    match env.find? name with
    | some info =>
        let typeFmt ← ppExpr info.type
        let modStr := match declModule env name with
          | some m => m.toString
          | none   => "<local>"
        blocks := blocks.push
          s!"\n--- [FRONTIER · {kindTag info}] {name}  (from {modStr}) ---\nStatement:\n{typeFmt}\n"
    | none =>
        blocks := blocks.push s!"\n--- [FRONTIER] {name} (not found) ---\n"
  return blocks

/--
Chunk the ordered text `blocks` into files named `{filePrefix}_{N}.txt` of at
most `cfg.maxWordsPerFile` words each, starting numbering at `startIdx` and
writing at most `budget` files. Returns the human-readable report together with
the number of files actually written. Each block is kept whole (never split). If
the blocks would need more than `budget` files, the lowest-priority tail is
dropped.
-/
def writeChunks (blocks : Array String) (cfg : ExportConfig)
    (filePrefix : String) (startIdx : Nat) (budget : Nat) : IO (String × Nat) := do
  if budget == 0 then
    if blocks.isEmpty then return ("", 0)
    return (s!"  WARNING: no file budget left; {blocks.size} block(s) dropped.\n", 0)
  IO.FS.createDirAll cfg.outputDir
  let mut filesWritten := 0
  let mut wc := 0
  let mut buf := ""
  let mut report := ""
  let mut truncated := false
  for block in blocks do
    let cw := estimateWords block
    -- flush when the current (non-empty) file would overflow
    if wc > 0 && wc + cw > cfg.maxWordsPerFile then
      let fname := cfg.outputDir / s!"{filePrefix}_{startIdx + filesWritten}.txt"
      IO.FS.writeFile fname buf
      report := report ++ s!"  wrote {fname} (~{wc} words)\n"
      filesWritten := filesWritten + 1
      buf := ""
      wc := 0
      if filesWritten ≥ budget then
        truncated := true
        break
    buf := buf ++ block
    wc := wc + cw
  if !truncated && !buf.isEmpty && filesWritten < budget then
    let fname := cfg.outputDir / s!"{filePrefix}_{startIdx + filesWritten}.txt"
    IO.FS.writeFile fname buf
    report := report ++ s!"  wrote {fname} (~{wc} words)\n"
    filesWritten := filesWritten + 1
  if truncated then
    report := report ++
      s!"  WARNING: reached file budget for '{filePrefix}'; remaining blocks truncated.\n"
  return (report, filesWritten)

/-- Programmatic entry point: export `targetName` under configuration `cfg`. -/
def runExport (targetName : Name) (cfg : ExportConfig := {}) : MetaM Unit := do
  let env ← getEnv
  -- Resolve the project module prefixes: auto-derive from the target if empty.
  let projectModules : List String :=
    if cfg.projectModules.isEmpty then
      match declModule env targetName with
      | some m => [m.getRoot.toString]
      | none   => []
    else cfg.projectModules
  let st ← exportTopDown targetName cfg projectModules
  -- Partition 1: the project's own declarations (top-down, full).
  let (projReport, projFiles) ←
    writeChunks st.projectBlocks cfg "notebook_lm_part" 1 cfg.maxFiles
  -- Partition 2: the core-library frontier (the graph cut), grouped away.
  let frontierBlocks ← formatFrontier st.frontier
  let remaining := cfg.maxFiles - projFiles
  let (frontReport, frontFiles) ←
    if cfg.expandBoundary then
      pure ("", 0)
    else
      writeChunks frontierBlocks cfg "core_library_part" 1 remaining
  let projRootStr := String.intercalate ", " projectModules
  let summary :=
    s!"[AristotleExporter] target `{targetName}`\n" ++
    s!"  project modules   : [{projRootStr}]\n" ++
    s!"  project partition : {st.projectBlocks.size} declaration(s), {projFiles} file(s)\n" ++
    (if cfg.expandBoundary then
        "  core library     : expanded inline (expandBoundary := true)\n"
      else
        s!"  core library     : {st.frontier.size} frontier declaration(s), {frontFiles} file(s)\n")
  logInfo (summary ++ projReport ++ frontReport)

/-- `#exportToNotebookLM target` — export `target` with the default config.

`#exportToNotebookLM target into "dir"` — export into a custom directory. -/
syntax (name := exportCmd) "#exportToNotebookLM " ident (" into " str)? : command

@[command_elab exportCmd]
def elabExportCmd : CommandElab := fun stx =>
  match stx with
  | `(command| #exportToNotebookLM $target:ident $[into $dir:str]?) =>
      Command.liftTermElabM do
        let cfg : ExportConfig :=
          match dir with
          | some d => { outputDir := d.getString }
          | none   => {}
        runExport target.getId cfg
  | _ => throwUnsupportedSyntax

end AristotleExporter
