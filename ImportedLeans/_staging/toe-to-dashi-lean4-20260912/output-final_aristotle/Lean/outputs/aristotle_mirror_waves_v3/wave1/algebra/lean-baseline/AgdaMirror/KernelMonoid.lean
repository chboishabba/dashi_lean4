import Mathlib

/-!
# Lean mirror of `DASHI/Core/KernelMonoid.agda` (genuine monoid laws)

Faithful transcription of the generic *kernel* (endomorphism) monoid: a `Kernel S`
wraps an endofunction `K : S → S`, with composition `∘K`, identity `idK`, and the
extensional (pointwise) equality `KernelEq`.  The three monoid laws

* `compose_assoc` — associativity of composition,
* `left_id`, `right_id` — `idK` is a two-sided unit,

are proved pointwise.  No `sorry`, axiom-clean.
-/

namespace AgdaMirror.KernelMonoid

variable {S : Type}

/-- Generic kernel as an endomorphism (Agda `record Kernel`). -/
structure Kernel (S : Type) where
  K : S → S

/-- Composition of kernels (Agda `_∘K_`). -/
def comp (A B : Kernel S) : Kernel S := ⟨fun x => A.K (B.K x)⟩

/-- Identity kernel (Agda `idK`). -/
def idK : Kernel S := ⟨fun x => x⟩

/-- Extensional (pointwise) equality of kernels (Agda `KernelEq`). -/
def KernelEq (A B : Kernel S) : Prop := ∀ x, A.K x = B.K x

/-- Associativity of kernel composition. -/
theorem compose_assoc (A B C : Kernel S) :
    KernelEq (comp (comp A B) C) (comp A (comp B C)) := fun _ => rfl

/-- `idK` is a left unit. -/
theorem left_id (A : Kernel S) : KernelEq (comp idK A) A := fun _ => rfl

/-- `idK` is a right unit. -/
theorem right_id (A : Kernel S) : KernelEq (comp A idK) A := fun _ => rfl

end AgdaMirror.KernelMonoid
