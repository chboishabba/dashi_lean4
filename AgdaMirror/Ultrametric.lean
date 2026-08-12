import Mathlib

/-!
# Lean mirror of `Ultrametric.agda` (definitional scaffolding, faithful)

Faithful transcription of `Ultrametric.agda`: a discrete ultrametric is a
`ℕ`-valued distance satisfying identity-of-indiscernibles (`d x x = 0`),
symmetry, and the strong (ultrametric) triangle inequality.  This is a pure
definition (a `record` in Agda); no proof obligation, axiom-clean.
-/

namespace AgdaMirror

/-- Discrete ultrametric: distance into `ℕ`. -/
structure Ultrametric (S : Type) where
  d : S → S → Nat
  id_zero : ∀ x, d x x = 0
  symmetric : ∀ x y, d x y = d y x
  ultratriangle : ∀ x y z, d x z ≤ max (d x y) (d y z)

end AgdaMirror
