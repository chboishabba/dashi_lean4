import RequestProject.Agda.Verbatim

/-!
# What the front end makes of an Agda file

`tools/AgdaParse.lean` reports whether a file is read; this one shows *what* it
is read as.  It prints the Lean commands the front end normalises a file into,
which is what one wants when a module parses but does not elaborate.

    AGDA_FILES="a.agda b.agda" lake env lean tools/AgdaDump.lean
-/

open Lean Elab Command AgdaFront.Verbatim

run_cmd do
  let sel ← liftM (IO.getEnv "AGDA_FILES")
  let files : List String := ((sel.getD "").splitOn " ").filter (· != "")
  for f in files do
    liftM (IO.println s!"-- ==== {f}" : IO Unit)
    let src ← liftM (IO.FS.readFile ⟨f⟩ : IO String)
    match normalize src with
    | .error e => liftM (IO.println s!"-- refused: {e}" : IO Unit)
    | .ok cmds => for c in cmds do liftM (IO.println c : IO Unit)
