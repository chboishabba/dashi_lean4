import Synthesis.MillenniumBSDExplicitSelmerCokernelExact
import Mathlib.RepresentationTheory.Homological.ContCohomology.Sha
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic

/-!
# The actual rational local-field Sha target

Mathlib now defines Tate–Shafarevich groups for arbitrary continuous Galois
modules as intersections of localization kernels, but does not yet define the
classical elliptic-curve specialization.

This file pays the global-field plumbing honestly: the place family is the
real place together with one p-adic field Q_p for every rational prime.  For
any supplied representation of Gal(Qbar/Q), we therefore obtain the literal
degree-one global-to-local Sha kernel and its 2-torsion subgroup.

The remaining BSD arithmetic same-object theorem is sharply isolated:
construct the elliptic E[2] (or E(Qbar)) TopRep and identify the explicit
square-class 2-descent cokernel with this cohomological 2-torsion target.
-/

namespace Synthesis.Millennium.BSD

open CategoryTheory

inductive RationalPlace where
  | infinite : RationalPlace
  | padic : Nat.Primes → RationalPlace

noncomputable def rationalLocalField : RationalPlace → Type
  | .infinite => ℝ
  | .padic p => ℚ_[p.1]

noncomputable instance rationalLocalFieldField (v : RationalPlace) :
    Field (rationalLocalField v) := by
  cases v with
  | infinite =>
      dsimp [rationalLocalField]
      infer_instance
  | padic p =>
      letI : Fact p.1.Prime := ⟨p.2⟩
      dsimp [rationalLocalField]
      infer_instance

noncomputable instance rationalLocalFieldAlgebra (v : RationalPlace) :
    Algebra ℚ (rationalLocalField v) := by
  cases v with
  | infinite =>
      dsimp [rationalLocalField]
      infer_instance
  | padic p =>
      letI : Fact p.1.Prime := ⟨p.2⟩
      dsimp [rationalLocalField]
      infer_instance

abbrev RationalAbsoluteGalois := Field.absoluteGaloisGroup ℚ

/--
The literal degree-one Tate–Shafarevich localization kernel over all rational
places, for a supplied continuous absolute-Galois representation.
-/
noncomputable def rationalTateShafarevichOne
    (A : TopRep ℤ RationalAbsoluteGalois) :
    AddSubgroup (ContinuousCohomology.continuousCohomology 1 A) :=
  ContinuousCohomology.tateShafarevich rationalLocalField A 1

theorem mem_rationalTateShafarevichOne_iff
    (A : TopRep ℤ RationalAbsoluteGalois)
    (x : ContinuousCohomology.continuousCohomology 1 A) :
    x ∈ rationalTateShafarevichOne A ↔
      ∀ v : RationalPlace,
        (ContinuousCohomology.map
          (Field.absoluteGaloisGroup.map
            (algebraMap ℚ (rationalLocalField v)))
          (𝟙 _) 1).hom x = 0 := by
  exact ContinuousCohomology.mem_tateShafarevich
    rationalLocalField A 1 x

/-- The 2-torsion subgroup of the degree-one rational Sha kernel. -/
noncomputable def rationalTateShafarevichTwoTorsion
    (A : TopRep ℤ RationalAbsoluteGalois) :
    AddSubgroup (rationalTateShafarevichOne A) where
  carrier := {x | (2 : ℕ) • x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    rw [smul_add, hx, hy, add_zero]
  neg_mem' := by
    intro x hx
    rw [smul_neg, hx, neg_zero]

@[simp] theorem mem_rationalTateShafarevichTwoTorsion_iff
    (A : TopRep ℤ RationalAbsoluteGalois)
    (x : rationalTateShafarevichOne A) :
    x ∈ rationalTateShafarevichTwoTorsion A ↔
      (2 : ℕ) • x = 0 := Iff.rfl

/--
The exact missing elliptic specialization data.  No equivalence is asserted:
this record names the two genuinely absent producers required before the
existing explicit Selmer cokernel can be called classical Sha[2].
-/
structure EllipticShaTwoComparisonBoundary where
  ellipticTwoTorsionRepresentation : TopRep ℤ RationalAbsoluteGalois
  explicitCokernelToCohomologicalShaTwo :
    ExplicitTwoSelmerCokernel →
      rationalTateShafarevichTwoTorsion ellipticTwoTorsionRepresentation
  cohomologicalShaTwoToExplicitCokernel :
    rationalTateShafarevichTwoTorsion ellipticTwoTorsionRepresentation →
      ExplicitTwoSelmerCokernel
  leftInverse : Function.LeftInverse
    cohomologicalShaTwoToExplicitCokernel
    explicitCokernelToCohomologicalShaTwo
  rightInverse : Function.RightInverse
    cohomologicalShaTwoToExplicitCokernel
    explicitCokernelToCohomologicalShaTwo

noncomputable def explicitSelmerCokernelEquivShaTwo
    (comparison : EllipticShaTwoComparisonBoundary) :
    ExplicitTwoSelmerCokernel ≃
      rationalTateShafarevichTwoTorsion
        comparison.ellipticTwoTorsionRepresentation where
  toFun := comparison.explicitCokernelToCohomologicalShaTwo
  invFun := comparison.cohomologicalShaTwoToExplicitCokernel
  left_inv := comparison.leftInverse
  right_inv := comparison.rightInverse

end Synthesis.Millennium.BSD
