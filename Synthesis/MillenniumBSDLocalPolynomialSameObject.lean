import Synthesis.MillenniumBSDReductionPointCountExact
import Synthesis.MillenniumBSDExplicitLocalRecurrence
import Synthesis.MillenniumBSDMathlibLFunctionWeld
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Tactic

/-!
# Explicit point-count local polynomial = mathlib localPolynomial at odd primes

This is the analytic same-object theorem.

For the literal curve E : y² = x³ - x and every odd prime p:

* the chosen mathlib minimal model has good reduction;
* its residue field has cardinality p;
* its reduction point count is exactly the explicit projectivePointCount p.

Therefore mathlib's internal local polynomial is literally

  1 - a_p X + p X²,

where a_p = p+1-#E(F_p), exactly the polynomial used by the explicit Euler
construction and prime-power recurrence.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve
open Polynomial
open IsLocalRing

theorem padicResidueField_natCard
    (p : ℕ) [Fact p.Prime] :
    Nat.card (IsLocalRing.ResidueField ℤ_[p]) = p := by
  rw [Nat.card_congr (padicResidueEquivZMod p).toEquiv]
  simp

theorem mathlibLocalTrace_eq_frobeniusCoefficient
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    ((Nat.card (IsLocalRing.ResidueField ℤ_[p]) : ℤ)
      + 1
      - Nat.card
          ((cmChosenMinimal p).reduction ℤ_[p]).toAffine.Point)
      =
    frobeniusCoefficient p := by
  rw [padicResidueField_natCard]
  rw [chosenReduction_point_card_eq_projectivePointCount hp2]
  rfl

theorem cmPadic_localPolynomial_eq_explicit
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    (cmPadicWeierstrass p).localPolynomial ℤ_[p]
      =
    explicitGoodLocalPolynomial p := by
  letI :
      WeierstrassCurve.HasGoodReduction ℤ_[p]
        (cmChosenMinimal p) :=
    cmChosenMinimal_hasGoodReduction hp2
  rw [WeierstrassCurve.localPolynomial]
  dsimp only
  rw [if_pos (by infer_instance :
    WeierstrassCurve.HasGoodReduction ℤ_[p]
      (cmChosenMinimal p))]
  rw [padicResidueField_natCard]
  rw [chosenReduction_point_card_eq_projectivePointCount hp2]
  unfold explicitGoodLocalPolynomial frobeniusCoefficient
  congr 1 <;> norm_num

theorem inert_mathlibLocalPolynomial
    {p : ℕ} [Fact p.Prime]
    (hmod : p % 4 = 3) :
    (cmPadicWeierstrass p).localPolynomial ℤ_[p]
      =
    1 + C (p : ℤ) * X ^ 2 := by
  have hp2 : p ≠ 2 := by
    intro hp
    subst p
    norm_num at hmod
  rw [cmPadic_localPolynomial_eq_explicit hp2]
  unfold explicitGoodLocalPolynomial
  rw [inert_frobeniusCoefficient_eq_zero hmod]
  simp

end Synthesis.Millennium.BSD
