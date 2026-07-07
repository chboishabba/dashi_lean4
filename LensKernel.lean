import Mathlib

/-!
# Lean mirror of `DASHI/Core/LensKernel.agda` (genuine interface + witness)

Faithful transcription of the lens / kernel-invariance interface:

* `Lens S A` — an observation `observe : S → A`,
* `LensInvariant L K` — exact commutation `observe (K x) = observe x`,
* `Preorder A` and `LensMonotone P L K` — the monotone variant.

These are pure interface records (Agda `record`s).  We additionally provide a
genuine *witness*: any lens is invariant under the identity kernel, and any lens
into a preorder is monotone under the identity kernel.  No `sorry`, axiom-clean.
-/

namespace AgdaMirror.LensKernel

variable {S A : Type}

/-- A lens is an observation `S → A` (Agda `record Lens`). -/
structure Lens (S A : Type) where
  observe : S → A

/-- Exact commutation invariant `observe (K x) = observe x`. -/
structure LensInvariant (L : Lens S A) (K : S → S) : Prop where
  inv : ∀ x, L.observe (K x) = L.observe x

/-- Order interface on observations (Agda `record Preorder`). -/
structure Preorder (A : Type) where
  le : A → A → Prop
  refl : ∀ a, le a a
  trans : ∀ a b c, le a b → le b c → le a c

/-- Monotone-observation variant. -/
structure LensMonotone (P : Preorder A) (L : Lens S A) (K : S → S) : Prop where
  mono : ∀ x, P.le (L.observe (K x)) (L.observe x)

/-- Genuine witness: every lens is invariant under the identity kernel. -/
def idLensInvariant (L : Lens S A) : LensInvariant L (id) := ⟨fun _ => rfl⟩

/-- Genuine witness: every lens into a preorder is monotone under the identity
kernel. -/
def idLensMonotone (P : Preorder A) (L : Lens S A) :
    LensMonotone P L (id) := ⟨fun x => P.refl (L.observe x)⟩

end AgdaMirror.LensKernel
