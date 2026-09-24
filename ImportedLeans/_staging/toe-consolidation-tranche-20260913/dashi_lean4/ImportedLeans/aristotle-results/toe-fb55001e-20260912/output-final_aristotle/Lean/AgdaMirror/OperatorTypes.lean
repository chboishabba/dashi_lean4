import Mathlib

/-!
# Lean mirror of `DASHI/Core/OperatorTypes.agda` (genuine definitions + lemmas)

Faithful transcription of the operator-classification core: endo-operators on a
carrier `S` and the three structural predicates

* `Invertible K`  — `K` has a two-sided inverse,
* `Projection K`  — `K` is idempotent,
* `Regularizer K` — `K` is von Neumann regular (`K = K ∘ R ∘ K`),

together with `Nontrivial` and the `OpClass` tag.  These are pure definitions
(records → structures), and we additionally prove the genuine fact that the
identity operator is simultaneously invertible, a projection and regular.

No `sorry`, axiom-clean.
-/

namespace AgdaMirror.OperatorTypes

variable {S : Type}

/-- `K` is invertible: it has a two-sided inverse. -/
structure Invertible (K : S → S) where
  inv : S → S
  left : ∀ x, inv (K x) = x
  right : ∀ x, K (inv x) = x

/-- `K` is a projection: it is idempotent. -/
structure Projection (K : S → S) where
  idem : ∀ x, K (K x) = K x

/-- `K` is nontrivial: it is not the identity. -/
def Nontrivial (K : S → S) : Prop := ¬ (∀ x, K x = x)

/-- `K` is von Neumann regular: `K = K ∘ R ∘ K` for some regularizer `R`. -/
structure Regularizer (K : S → S) where
  R : S → S
  law : ∀ x, K x = K (R (K x))

/-- Operator class tag. -/
inductive OpClass | invertible | projection | regular | other
  deriving DecidableEq, Repr

/-- The identity operator is invertible. -/
def idInvertible : Invertible (id : S → S) where
  inv := id
  left := fun _ => rfl
  right := fun _ => rfl

/-- The identity operator is a projection. -/
def idProjection : Projection (id : S → S) where
  idem := fun _ => rfl

/-- The identity operator is von Neumann regular. -/
def idRegularizer : Regularizer (id : S → S) where
  R := id
  law := fun _ => rfl

end AgdaMirror.OperatorTypes
