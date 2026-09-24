import RequestProject.Agda.Verbatim

/-!
# The syntactic gate of the Agda front end, as a report

`AgdaCheck` measures how much of the upstream corpus Lean can *elaborate*
directly, which needs a full build.  This harness measures the cheaper half —
how much of it the front end can *normalise and parse* — over the corpus,
without elaborating anything.  It is both a fast way to work on the syntactic
fragment and the gate `tools/agdacheck.py` consults when it decides which
modules to hand to Lean, so that the generator and the front end cannot drift
apart: the answer comes from the front end itself rather than from a mirror of
it written in another language.

    lake env lean tools/AgdaParse.lean > docs/AGDA_FRONTEND_PARSE.txt
    AGDA_FILES="a.agda b.agda" lake env lean tools/AgdaParse.lean
    AGDA_SHOW=1 AGDA_FILES="a.agda" lake env lean tools/AgdaParse.lean

Each file is reported as `ok <path>` or `skip <path> [reason]`.
-/

open Lean Elab Command AgdaFront.Verbatim

/-- All `.agda` files under a directory, recursively. -/
partial def agdaFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for e in (← dir.readDir) do
    if (← e.path.isDir) then
      out := out ++ (← agdaFiles e.path)
    else if e.path.extension == some "agda" then
      out := out.push e.path
  return out

/-- Normalise a file and parse the commands it produces; `none` on success.

A module that defines a mixfix operator emits a notation command, and the
declarations after it use the operator as a token.  Parsing them therefore needs
that notation to be in scope, so each notation the front end emits is declared
here too — with a placeholder right-hand side, since the harness only parses and
the token is all that matters. -/
def checkAgdaFile (p : System.FilePath) : CommandElabM (Option String) := do
  let src ← IO.FS.readFile p
  match normalize src with
  | .error e => return some (e.replace "\n" " ")
  | .ok cmds =>
      for txt in cmds do
        match Lean.Parser.runParserCategory (← getEnv) `command txt "<agda>" with
        | .error e =>
            let show? ← IO.getEnv "AGDA_SHOW"
            return some (if show?.isSome then s!"parse: {e}\nin:\n{txt}"
                         else s!"parse: {e.replace "\n" " "}")
        | .ok _ =>
            if txt.startsWith "infix" then
              let head := (txt.splitOn " =>").headD txt
              match Lean.Parser.runParserCategory (← getEnv) `command
                  (head ++ " => (fun a _ => a)") "<agda>" with
              | .ok stx => try elabCommand stx catch _ => pure ()
              | .error _ => pure ()
      return none

run_cmd do
  let sel ← liftM (IO.getEnv "AGDA_FILES")
  let files : Array System.FilePath ←
    match sel with
    | some s => pure ((s.splitOn " ").filter (· != "") |>.toArray.map (⟨·⟩))
    | none => do
        let fs ← liftM (agdaFiles ⟨"upstream/dashi_agda"⟩)
        pure (fs.qsort (fun a b => a.toString < b.toString))
  let mut okCount := 0
  for f in files do
    match ← withoutModifyingEnv (checkAgdaFile f) with
    | none =>
        okCount := okCount + 1
        liftM (IO.println s!"ok   {f}" : IO Unit)
    | some e => liftM (IO.println s!"skip {f}   [{e}]" : IO Unit)
  liftM (IO.println s!"-- the front end reads {okCount} of {files.size} Agda files" : IO Unit)
