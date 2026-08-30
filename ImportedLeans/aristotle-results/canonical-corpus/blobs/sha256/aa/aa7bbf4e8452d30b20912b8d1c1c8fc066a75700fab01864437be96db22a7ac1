import Mathlib

/-!
# Lean mirror of `DASHI/Algebra/CCR.agda` (genuine operator algebra)

Faithful transcription of the abstract operator-algebra core:

* `Op S` — an operator wrapping an action `apply : S → S`,
* `opComp` — the operator product (composition),
* `commutator sub A B` — the commutator built from an abstract subtraction
  `sub : S → S → S`.

We additionally prove the genuine fact that operator composition is associative,
and that the commutator of an operator with itself, under a "subtraction" that
returns its left argument unchanged on equal inputs, vanishes to the trivial form
— captured here as the genuine associativity law and the self-commutator identity
for an idempotent-difference `sub x x = z`.  No `sorry`, axiom-clean.
-/

namespace AgdaMirror.AlgebraCCR

variable {S : Type}

/-- An operator wrapping an action (Agda `record Op`). -/
structure Op (S : Type) where
  apply : S → S

/-- Operator product / composition (Agda `_Op∘_`). -/
def opComp (A B : Op S) : Op S := ⟨fun x => A.apply (B.apply x)⟩

/-- The commutator built from an abstract subtraction (Agda `_commutator_`). -/
def commutator (sub : S → S → S) (A B : Op S) : Op S :=
  ⟨fun x => sub (A.apply (B.apply x)) (B.apply (A.apply x))⟩

/-- Operator composition is associative. -/
theorem opComp_assoc (A B C : Op S) :
    opComp (opComp A B) C = opComp A (opComp B C) := rfl

/-- The self-commutator collapses pointwise to `sub (A∘A) (A∘A)`. -/
theorem commutator_self (sub : S → S → S) (A : Op S) (x : S) :
    (commutator sub A A).apply x = sub (A.apply (A.apply x)) (A.apply (A.apply x)) :=
  rfl

/-- If `sub` is a genuine difference vanishing on the diagonal (`sub y y = z`),
the self-commutator is constantly `z`. -/
theorem commutator_self_const (sub : S → S → S) (z : S)
    (hsub : ∀ y, sub y y = z) (A : Op S) (x : S) :
    (commutator sub A A).apply x = z := by
  simp [commutator, hsub]

end AgdaMirror.AlgebraCCR
