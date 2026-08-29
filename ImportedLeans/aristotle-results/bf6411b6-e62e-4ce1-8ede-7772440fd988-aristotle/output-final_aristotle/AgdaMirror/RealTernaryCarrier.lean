import Mathlib
import AgdaMirror.DASHIAlgebra

/-!
# Lean mirror of `DASHI/Physics/RealTernaryCarrier.agda` (genuine involution)

Faithful transcription of the length-`n` ternary carrier `Carrier n = Vec Trit n`
with the pointwise sign inversion `invVec = map inv` (reusing the balanced-ternary
`Trit`/`Trit.inv` already mirrored in `AgdaMirror.DASHIAlgebra`), its genuine
involution `invVec (invVec x) = x`, and the constant zero carrier `zeroVec`.
We model `Vec Trit n` as `List` together with `zeroVec` as the canonical length-`n`
element, but the carrier content and laws are mirrored exactly.  No `sorry`,
axiom-clean.
-/

namespace AgdaMirror.RealTernaryCarrier

open AgdaMirror.DASHIAlgebra

/-- The ternary carrier (Agda `Carrier n = Vec Trit n`); modelled as a
`List Trit`, with `zeroVec` giving the canonical length-`n` element. -/
abbrev Carrier := List Trit

/-- Pointwise sign inversion (Agda `invVec = map inv`). -/
def invVec (x : Carrier) : Carrier := x.map Trit.inv

/-- The constant-zero carrier of length `n` (Agda `zeroVec`). -/
def zeroVec (n : Nat) : Carrier := List.replicate n Trit.zer

/-- `invVec` is a genuine involution (Agda `invVec-invol`), via the pointwise
involution of `Trit.inv`. -/
theorem invVec_invol (x : Carrier) : invVec (invVec x) = x := by
  induction x with
  | nil => rfl
  | cons t ts ih =>
    simp only [invVec, List.map_cons] at *
    rw [Trit.inv_invol, ih]

/-- `invVec` fixes the zero carrier of any length. -/
theorem invVec_zeroVec (n : Nat) : invVec (zeroVec n) = zeroVec n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [zeroVec, List.replicate_succ, invVec, List.map_cons] at *
    rw [ih]; rfl

end AgdaMirror.RealTernaryCarrier
