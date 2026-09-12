import Mathlib

/-!
# Lean mirror of `DASHI/Energy/Core.agda` and
`DASHI/Energy/TranslationInvariantMetric.agda` (genuine interface + witness)

Faithful transcription of the energy-space and translation-invariant-metric
interfaces:

* `Preorder`, `EnergySpace`, `Endo` from `Energy/Core`,
* `AddGroup`, `TI` (translation-invariant distance) from
  `Energy/TranslationInvariantMetric`.

We additionally provide a *genuine witness* for the translation-invariant metric:
on `ℤ`, the distance `d x y = |x - y|` is translation invariant
(`|(x+z) - (y+z)| = |x - y|`), proved over Mathlib's integers.  No `sorry`,
axiom-clean.
-/

namespace AgdaMirror.EnergyMetric

universe u v

/-- Preorder interface (Agda `record Preorder`). -/
structure Preorder (A : Type u) where
  le : A → A → Prop
  refl : ∀ x, le x x
  trans : ∀ {x y z}, le x y → le y z → le x z

/-- Energy space: a preorder on energies plus an energy assignment. -/
structure EnergySpace (X : Type u) (E : Type v) where
  P : Preorder E
  energy : X → E

/-- Endo-operator interface (Agda `record Endo`). -/
structure Endo (X : Type u) where
  T : X → X

/-- Additive group interface (Agda `record AddGroup`). -/
structure AddGroup (X : Type u) where
  add : X → X → X
  sub : X → X → X
  zero : X

/-- Translation-invariant distance interface (Agda `record TI`). -/
structure TI (X : Type u) (E : Type v) where
  G : AddGroup X
  d : X → X → E
  transInv : ∀ x y z, d (G.add x z) (G.add y z) = d x y

/-- The additive group of integers as an `AddGroup` witness. -/
def intAddGroup : AddGroup ℤ where
  add := (· + ·)
  sub := (· - ·)
  zero := 0

/-- Genuine witness: on `ℤ`, `d x y = |x - y|` is a translation-invariant
distance. -/
def intTI : TI ℤ ℤ where
  G := intAddGroup
  d := fun x y => |x - y|
  transInv := by
    intro x y z
    simp [intAddGroup, abs, add_sub_add_right_eq_sub]

end AgdaMirror.EnergyMetric
