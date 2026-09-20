import Synthesis.MillenniumBSDLiteralReductionZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic

/-!
# The mathlib reduction point count is the explicit fibrewise point count

We now close the counting layer completely.

For the literal ZMod p equation, affine solutions are equivalent to the sigma
type obtained by first choosing x and then choosing y with
y² = x³ - x.  Its cardinal is therefore exactly the previously defined
`affineFiberCount p`.

For mathlib's chosen minimal reduction, `Affine.pointEquiv` identifies the
full elliptic point type with the affine equation subtype plus the unique point
at infinity.  Combining this with the reduction/variable-change weld proves

  Nat.card E_min(F_p) = projectivePointCount p.

Thus the coefficient q+1-#E(F_q) used by mathlib is literally our explicit
point-count coefficient once q=p.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve
open IsLocalRing

def cmZModAffineSigmaEquiv
    (p : ℕ) [Fact p.Prime] :
    AffineEquationPoint (cmZModWeierstrass p)
      ≃
    (Σ x : ZMod p,
      {y : ZMod p // y ^ 2 = cmCubic x}) where
  toFun := fun P =>
    ⟨P.1.1, ⟨P.1.2,
      (cmZMod_equation_iff P.1.1 P.1.2).mp P.2⟩⟩
  invFun := fun P =>
    ⟨(P.1, P.2.1),
      (cmZMod_equation_iff P.1 P.2.1).mpr P.2.2⟩
  left_inv := by
    intro P
    rfl
  right_inv := by
    intro P
    cases P
    rfl

theorem cmZMod_affine_card_eq_fiberCount
    (p : ℕ) [Fact p.Prime] :
    Fintype.card
      (AffineEquationPoint (cmZModWeierstrass p))
      =
    affineFiberCount p := by
  rw [Fintype.card_congr (cmZModAffineSigmaEquiv p)]
  rw [Fintype.card_sigma]
  unfold affineFiberCount
  apply Finset.sum_congr rfl
  intro x hx
  simp

theorem chosenReduction_affine_card_eq_fiberCount
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    Fintype.card
      (AffineEquationPoint
        ((cmChosenMinimal p).reduction ℤ_[p]))
      =
    affineFiberCount p := by
  calc
    Fintype.card
      (AffineEquationPoint
        ((cmChosenMinimal p).reduction ℤ_[p]))
      =
    Fintype.card
      (AffineEquationPoint
        ((cmPadicWeierstrass p).reduction ℤ_[p])) :=
      chosenReduction_affineEquationPoint_card_eq_literal hp2
    _ =
    Fintype.card
      (AffineEquationPoint (cmZModWeierstrass p)) :=
      literalReduction_affine_card_eq_ZMod p
    _ = affineFiberCount p :=
      cmZMod_affine_card_eq_fiberCount p

theorem chosenReduction_point_card_eq_affine_add_one
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    Nat.card
      ((cmChosenMinimal p).reduction ℤ_[p]).toAffine.Point
      =
    Fintype.card
      (AffineEquationPoint
        ((cmChosenMinimal p).reduction ℤ_[p]))
      + 1 := by
  letI :
      WeierstrassCurve.IsElliptic
        ((cmChosenMinimal p).reduction ℤ_[p]) :=
    WeierstrassCurve.HasGoodReduction.reduction_isElliptic
      (R := ℤ_[p]) (W := cmChosenMinimal p)
  rw [Nat.card_congr
    (((cmChosenMinimal p).reduction ℤ_[p]).toAffine.pointEquiv)]
  simp [Nat.card_eq_fintype_card]

theorem chosenReduction_point_card_eq_projectivePointCount
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    Nat.card
      ((cmChosenMinimal p).reduction ℤ_[p]).toAffine.Point
      =
    projectivePointCount p := by
  rw [chosenReduction_point_card_eq_affine_add_one hp2]
  rw [chosenReduction_affine_card_eq_fiberCount hp2]
  rfl

end Synthesis.Millennium.BSD
