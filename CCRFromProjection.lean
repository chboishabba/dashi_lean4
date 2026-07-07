import Mathlib

/-!
# Lean mirror of `DASHI/Algebra/Quantum/CCRFromProjection.agda`
(genuine interface + witness)

Faithful transcription of the abstract Weyl/CCR-from-projection interface:

* `CCRData` — the carrier data (scalars, a unitary group `U` with product and
  unit, the position/momentum translations `XTrans`/`PTrans`, the phase map, and
  an idempotent projection `P` with the actions `actX`/`actP`),
* `Weyl D` — the Weyl commutation relation,
* `ProjectionWeylAxioms D` — the Weyl relation together with projection
  covariance/invariance (honest hypothesis fields),
* `stone_vn` — the (trivial) packaging map `ProjectionWeylAxioms → CCR`.

We give a genuine *witness* `trivialCCR` on one-point carriers, and show it
satisfies all the Weyl/projection axioms.  No `sorry`, axiom-clean.
-/

namespace AgdaMirror.CCRFromProjection

universe u

/-- Carrier data for a Weyl/CCR construction (Agda `record CCRData`). -/
structure CCRData where
  Scalar : Type u
  mulq : Scalar → Scalar → Scalar
  Hilbert : Type u
  U : Type u
  mulU : U → U → U
  Iu : U
  XTrans : Scalar → U
  PTrans : Scalar → U
  phase : Scalar → U
  P : Hilbert → Hilbert
  idem : ∀ x, P (P x) = P x
  actX : Scalar → Hilbert → Hilbert
  actP : Scalar → Hilbert → Hilbert

/-- The Weyl commutation relation (Agda `Weyl`). -/
def Weyl (D : CCRData) : Prop :=
  ∀ a b,
    D.mulU (D.XTrans a) (D.PTrans b)
      = D.mulU (D.phase (D.mulq a b)) (D.mulU (D.PTrans b) (D.XTrans a))

/-- The Weyl relation plus projection covariance/invariance (Agda
`record ProjectionWeylAxioms`). -/
structure ProjectionWeylAxioms (D : CCRData) : Prop where
  weyl : Weyl D
  proj_inv_P : ∀ b ψ, D.P (D.actP b ψ) = D.P ψ
  proj_covar_X : ∀ a ψ, D.P (D.actX a ψ) = D.actX a (D.P ψ)

/-- The CCR predicate is exactly the projection–Weyl axiom bundle. -/
def CCR (D : CCRData) : Prop := ProjectionWeylAxioms D

/-- Stone–von Neumann packaging: the axiom bundle *is* the CCR data (Agda
`stone-vn`). -/
theorem stone_vn {D : CCRData} (ax : ProjectionWeylAxioms D) : CCR D := ax

/-- A genuine witness: the trivial CCR data on one-point carriers. -/
def trivialCCR : CCRData where
  Scalar := PUnit
  mulq := fun _ _ => PUnit.unit
  Hilbert := PUnit
  U := PUnit
  mulU := fun _ _ => PUnit.unit
  Iu := PUnit.unit
  XTrans := fun _ => PUnit.unit
  PTrans := fun _ => PUnit.unit
  phase := fun _ => PUnit.unit
  P := id
  idem := fun _ => rfl
  actX := fun _ => id
  actP := fun _ => id

/-- The trivial CCR data satisfies all Weyl/projection axioms. -/
theorem trivialCCR_axioms : ProjectionWeylAxioms trivialCCR where
  weyl := fun _ _ => rfl
  proj_inv_P := fun _ _ => rfl
  proj_covar_X := fun _ _ => rfl

end AgdaMirror.CCRFromProjection
