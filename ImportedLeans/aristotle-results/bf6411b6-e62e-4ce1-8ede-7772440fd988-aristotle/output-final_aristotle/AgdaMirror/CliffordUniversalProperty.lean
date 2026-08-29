import Mathlib

/-!
# Lean mirror of `DASHI/Algebra/Clifford/UniversalProperty.agda`
(genuine interface + witness)

Faithful transcription of the Clifford-algebra universal-property interface:

* `CliffordData` — the carrier data (quadratic space `V`/`Q`, tensor algebra
  `TAlg`, quotient `Cl`, the embedding `ι`, scalar action, and the Clifford
  relation `ι v ∙ ι v = Q v • 1c`),
* `CliffordUP` — the universal property (factorization through `TAlg`),
* `CliffordAxioms` — the genuine anti-commutation law (an honest field, not a
  `refl` assumption, exactly as in the Agda).

These are pure interface records.  We give a genuine *witness* `trivialClifford`
on the trivial one-point algebra, so the interface is inhabited.  No `sorry`,
axiom-clean.
-/

namespace AgdaMirror.CliffordUniversalProperty

universe u

/-- The carrier data of a Clifford construction (Agda `record CliffordData`). -/
structure CliffordData where
  V : Type u
  Scalar : Type u
  Q : V → Scalar
  two : Scalar
  mulS : Scalar → Scalar → Scalar
  TAlg : Type u
  inj : V → TAlg
  Cl : Type u
  smul : Scalar → Cl → Cl
  one_c : Cl
  ι : V → Cl
  cliffMul : Cl → Cl → Cl
  add : Cl → Cl → Cl
  cliff_rel : ∀ v, cliffMul (ι v) (ι v) = smul (Q v) one_c
  inner : V → V → Scalar
  orth : V → V → Prop

/-- The universal property: any quadratic-relation-respecting map out of `V`
factors through the tensor algebra (Agda `record CliffordUP`). -/
structure CliffordUP (C : CliffordData) where
  universal :
    ∀ {A : Type u} (ιA : C.V → A) (mulA : A → A → A) (oneA : A)
      (smulA : C.Scalar → A → A),
      (∀ v, mulA (ιA v) (ιA v) = smulA (C.Q v) oneA) →
      { f : C.TAlg → A // ∀ v, f (C.inj v) = ιA v }

/-- The genuine anti-commutation law for orthogonal vectors (Agda
`record CliffordAxioms`); an honest field, not assumed by `refl`. -/
structure CliffordAxioms (C : CliffordData) where
  orth_anticomm :
    ∀ u v, C.orth u v →
      C.add (C.cliffMul (C.ι u) (C.ι v)) (C.cliffMul (C.ι v) (C.ι u))
        = C.smul (C.mulS C.two (C.inner u v)) C.one_c

/-- A genuine witness: the trivial Clifford data on one-point carriers. -/
def trivialClifford : CliffordData where
  V := PUnit
  Scalar := PUnit
  Q := fun _ => PUnit.unit
  two := PUnit.unit
  mulS := fun _ _ => PUnit.unit
  TAlg := PUnit
  inj := fun _ => PUnit.unit
  Cl := PUnit
  smul := fun _ _ => PUnit.unit
  one_c := PUnit.unit
  ι := fun _ => PUnit.unit
  cliffMul := fun _ _ => PUnit.unit
  add := fun _ _ => PUnit.unit
  cliff_rel := fun _ => rfl
  inner := fun _ _ => PUnit.unit
  orth := fun _ _ => True

/-- The trivial Clifford data satisfies the anti-commutation axioms. -/
def trivialCliffordAxioms : CliffordAxioms trivialClifford where
  orth_anticomm := fun _ _ _ => rfl

end AgdaMirror.CliffordUniversalProperty
