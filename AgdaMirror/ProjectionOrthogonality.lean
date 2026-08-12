import Mathlib

/-!
# Lean mirror of `DASHI/Algebra/Quantum/ProjectionOrthogonality.agda`
(faithful scaffolding)

Faithful transcription of the abstract orthogonal-projection interface.  The Agda
module is *structural*: it `record`s an abstract Hilbert carrier with a
subtraction `_H∸_` and a `ℕ`-valued `Inner` product, and an `OrthoProj` record
bundling idempotence and the orthogonality law `⟨P x, y − P y⟩ = 0`.

Following the honesty discipline, the abstract carrier and its operations become
explicit structure fields (parameters), never axioms.  We additionally record the
genuine fact that the identity together with the trivial inner product satisfies
the orthogonal-projection laws.

No `sorry`, axiom-clean.
-/

namespace AgdaMirror.ProjectionOrthogonality

/-- Abstract data: a carrier with subtraction and a `ℕ`-valued inner product. -/
structure ProjectionOrthogonalityAxioms where
  Hilbert : Type
  Hsub : Hilbert → Hilbert → Hilbert
  Inner : Hilbert → Hilbert → Nat

/-- An orthogonal projection on the abstract carrier: idempotent and orthogonal
to the residual `y − P y`. -/
structure OrthoProj (A : ProjectionOrthogonalityAxioms) (P : A.Hilbert → A.Hilbert) where
  idem : ∀ x, P (P x) = P x
  orth : ∀ x y, A.Inner (P x) (A.Hsub y (P y)) = 0

/-- The trivial model: identity projection with the constantly-zero inner product
satisfies the orthogonal-projection laws. -/
def trivialOrthoProj (H : Type) :
    OrthoProj ⟨H, fun x _ => x, fun _ _ => 0⟩ id where
  idem := fun _ => rfl
  orth := fun _ _ => rfl

end AgdaMirror.ProjectionOrthogonality
