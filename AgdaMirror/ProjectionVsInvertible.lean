import AgdaMirror.OperatorTypes

/-!
# Lean mirror of `DASHI/Algebra/ProjectionVsInvertible.agda` (genuine theorem)

Faithful transcription of the genuine algebraic fact: an operator that is both a
projection (idempotent) and invertible must be the identity.

> If `K` is idempotent and invertible then `K x = x` for all `x`.

The Agda proof is the short calculation
`K x = inv (K (K x)) = inv (K x) = x` (using `left`, `idem`, `left`); we mirror
it exactly.  No `sorry`, axiom-clean.
-/

namespace AgdaMirror.ProjectionVsInvertible

open AgdaMirror.OperatorTypes

variable {S : Type} {K : S → S}

/-- A projection that is also invertible is the identity (mirrors
`projection+invertible→identity`). -/
theorem projection_invertible_identity
    (P : Projection K) (I : Invertible K) (x : S) : K x = x := by
  calc K x = I.inv (K (K x)) := (I.left (K x)).symm
    _ = I.inv (K x) := by rw [P.idem]
    _ = x := I.left x

/-- Consequently, a projection that is also invertible cannot be nontrivial. -/
theorem projection_invertible_not_nontrivial
    (P : Projection K) (I : Invertible K) : ¬ Nontrivial K :=
  fun h => h (projection_invertible_identity P I)

end AgdaMirror.ProjectionVsInvertible
