import Mathlib

/-!
# Lean mirror of `JFixedPoint.agda` (genuine, fully proved)

Faithful transcription of `JFixedPoint.agda`.  An `Observation` records the three
trivector-prime exponents; `contract` maps it through the moonshine map to a
scalar.  The unit observation contracts to `196884`, and the `stack` tower is
`j`-fixed: every layer contracts to `196884` regardless of depth.  The Agda
module only checks finitely many depths (`fixed-0 … fixed-100`); here we prove
the genuinely general statement `stack_converges` for all `n`.
-/

namespace AgdaMirror.JFixedPoint

/-- An observation is a triple of exponent counts at `p47, p59, p71`. -/
structure Observation where
  e47 : Nat
  e59 : Nat
  e71 : Nat

/-- Contract an observation to a scalar via the moonshine map. -/
def contract (o : Observation) : Nat :=
  o.e47 * 47 * (o.e59 * 59) * (o.e71 * 71) + 1

/-- The minimal observation (the observer itself). -/
def unitObs : Observation := ⟨1, 1, 1⟩

/-- Contraction of the unit observation is `196884`. -/
theorem unit_converges : contract unitObs = 196884 := rfl

/-- The tower of `n` layers; each layer stays `j`-fixed (`e47 = e59 = e71 = 1`). -/
def stack : Nat → Observation
  | 0      => unitObs
  | (_ + 1) => unitObs

/-- The fixed-point theorem: every layer contracts to the same value `196884`
(generalising the Agda module's finitely many `fixed-k` checks). -/
theorem stack_converges (n : Nat) : contract (stack n) = 196884 := by
  cases n with
  | zero => exact unit_converges
  | succ k => exact unit_converges

/-- A tower is a list of observation layers. -/
abbrev Tower := List Observation

/-- Expand: prepend a new observation layer. -/
def expand (t : Tower) : Tower := unitObs :: t

/-- Contract all layers. -/
def contractAll : Tower → List Nat
  | []      => []
  | o :: os => contract o :: contractAll os

theorem all_196884 :
    contractAll (expand (expand (expand []))) = [196884, 196884, 196884] := by
  show [contract unitObs, contract unitObs, contract unitObs] = [196884, 196884, 196884]
  rw [unit_converges]

end AgdaMirror.JFixedPoint
