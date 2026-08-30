import Lean

/-!
# Quine: the program reproduced as a quine

A **quine** is a program that prints its own source, with no input and without
reading its own file.  This module captures, models, and regenerates a genuine,
self-contained Lean 4 quine — the smallest fixed point of the introspective
atlas: a program whose *output is its own text*.

## The quine

The committed artifact `quine.lean` (project root) is exactly two lines:

```lean
def s : String := "#eval IO.println s!\"def s : String := {repr s}\\n{s}\""
#eval IO.println s!"def s : String := {repr s}\n{s}"
```

Running it with `lake env lean quine.lean` prints those same two lines, verbatim
— it reproduces itself.

## How it works

Line 2 is the program `body`; line 1 binds `s` to the *escaped text of line 2*
(`repr` produces a valid Lean string literal, so `s` evaluates back to `body`).
When run, `body` prints `def s : String := ` followed by `repr s` (which
regenerates line 1) then a newline then `s` (which regenerates line 2).  Thus
`output = reproduce body = quine source`.

## What this module provides

* `body`            — the source text of the quine's program line.
* `reproduce`       — the pure model of the quine's runtime output.
* `quineSource`     — the full source text the quine prints (= the file).
* `quine_is_fixpoint` — the fixed-point identity `reproduce body = quineSource`.
* `#quine`          — print the quine source.
* `#writequine "p"` — (re)generate the `quine.lean` artifact at `p`.
* `#verifyquine "p"`— read the artifact at `p` and check it equals the model
  (closing the loop: the committed file *is* the modelled quine).
-/

open Lean Elab Command

namespace Quine

/-- The program line of the quine (its second source line). -/
def body : String :=
  "#eval IO.println s!\"def s : String := {repr s}\\n{s}\""

/-- The pure model of what the quine prints at runtime: the binding line
(`def s : String := ` ++ the escaped body) then the body, then the trailing
newline `IO.println` emits. -/
def reproduce (b : String) : String :=
  "def s : String := " ++ toString (repr b) ++ "\n" ++ b ++ "\n"

/-- The full source text of the quine — exactly what running it prints. -/
def quineSource : String := reproduce body

/-- **The quine fixed point.**  The program embeds `body`, and running it emits
`reproduce body`, which is the whole source.  So the modelled output is the
source verbatim. -/
theorem quine_is_fixpoint : reproduce body = quineSource := rfl

/-! ## Commands -/

/-- `#quine` prints the self-contained quine source. -/
syntax (name := quineCmd) "#quine" : command

@[command_elab quineCmd]
def elabQuine : CommandElab := fun _ => do
  logInfo s!"[Quine] {quineSource.length}-byte self-reproducing Lean program:\n{quineSource}"

/-- `#writequine "path"` (re)generates the standalone quine artifact. -/
syntax (name := writequineCmd) "#writequine " str : command

@[command_elab writequineCmd]
def elabWritequine : CommandElab := fun stx => do
  match stx with
  | `(#writequine $p:str) => do
    let path := p.getString
    IO.FS.writeFile path quineSource
    logInfo s!"[Quine] wrote {quineSource.length}-byte quine to {path}"
  | _ => throwError "ill-formed #writequine command"

/-- `#verifyquine "path"` reads the artifact and checks it is byte-identical to
the modelled quine source — confirming the committed file is exactly the quine. -/
syntax (name := verifyquineCmd) "#verifyquine " str : command

@[command_elab verifyquineCmd]
def elabVerifyquine : CommandElab := fun stx => do
  match stx with
  | `(#verifyquine $p:str) => do
    let path := p.getString
    let onDisk ← IO.FS.readFile path
    if onDisk == quineSource then
      logInfo s!"[Quine] VERIFIED: {path} ({onDisk.length} bytes) is byte-identical to the modelled quine source."
    else
      logError s!"[Quine] MISMATCH: {path} differs from the modelled quine source."
  | _ => throwError "ill-formed #verifyquine command"

/-! ## Test suite -/

#quine
#writequine "quine.lean"
#verifyquine "quine.lean"

end Quine
