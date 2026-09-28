import Synthesis.RiemannZetaMuExactAbel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Absolutely-continuous exact N-mu Abel identity

The historical exact Abel theorem asks for a pointwise derivative of the test
function on the whole interval. The quartic cap arising from the fourth
symmetric-discrepancy primitive is continuous and absolutely continuous but
has a derivative kink at the inner canonical cut.

This file weakens the exact atomic/RvM Abel compiler to the natural AC
hypothesis. Derivatives are interpreted through deriv phi, which is integrable
for absolutely continuous phi; no derivative is asserted at kink points.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Interval Real

namespace Synthesis

open Zeta23

theorem zetaWindowWeightedPair_eq_endpoint_sub_tail_ac
    {A B : ℝ}
    (hAB : A <= B)
    {phi : ℝ -> ℝ}
    (hphi : AbsolutelyContinuousOnInterval phi A B) :
    zetaWindowWeightedPair A B phi
      =
    phi B * (Ncount A B : ℝ)
      - zetaWindowWeightedTailIntegral A B (deriv phi) := by
  classical
  let hfin : (zetaZeroConfig.window A B).Finite :=
    zetaZeroConfig.finite_window A B
  let F : Finset ℂ := hfin.toFinset

  have hpair :
      zetaWindowWeightedPair A B phi
        =
      ∑ rho ∈ F,
        (zetaZeroConfig.mult rho : ℝ) * phi rho.im := by
    unfold zetaWindowWeightedPair
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    rfl

  have htail :
      zetaWindowWeightedTailIntegral A B (deriv phi)
        =
      ∑ rho ∈ F,
        (zetaZeroConfig.mult rho : ℝ)
          * (∫ x in rho.im..B, deriv phi x) := by
    unfold zetaWindowWeightedTailIntegral
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    rfl

  have hN :
      (Ncount A B : ℝ)
        =
      ∑ rho ∈ F, (zetaZeroConfig.mult rho : ℝ) := by
    rw [← zetaZeroConfig_N]
    unfold ZeroConfig.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    push_cast
    rfl

  rw [hpair, htail, hN]
  have hatom :
      ∀ rho ∈ F,
        phi rho.im
          =
        phi B - ∫ x in rho.im..B, deriv phi x := by
    intro rho hrho
    have hrhoSet :
        rho ∈ zetaZeroConfig.window A B := by
      simpa [F,hfin] using hrho
    have hrange : rho.im ∈ Set.Icc A B :=
      ⟨le_of_lt hrhoSet.2.1, hrhoSet.2.2⟩
    have hsubAC :
        AbsolutelyContinuousOnInterval phi rho.im B := by
      apply hphi.mono
      rw [Set.uIcc_of_le hrange.2, Set.uIcc_of_le hAB]
      intro x hx
      exact ⟨hrange.1.trans hx.1, hx.2⟩
    have hFTC := hsubAC.integral_deriv_eq_sub
    linarith

  calc
    (∑ rho ∈ F,
      (zetaZeroConfig.mult rho : ℝ) * phi rho.im)
      =
    ∑ rho ∈ F,
      (zetaZeroConfig.mult rho : ℝ)
        * (phi B - ∫ x in rho.im..B, deriv phi x) := by
          apply Finset.sum_congr rfl
          intro rho hrho
          rw [hatom rho hrho]
    _ =
      phi B * (∑ rho ∈ F, (zetaZeroConfig.mult rho : ℝ))
        -
      ∑ rho ∈ F,
        (zetaZeroConfig.mult rho : ℝ)
          * (∫ x in rho.im..B, deriv phi x) := by
          rw [Finset.mul_sum]
          ring

theorem zetaMu_integrationByParts_ac
    {A B : ℝ}
    {phi : ℝ -> ℝ}
    (hphi : AbsolutelyContinuousOnInterval phi A B) :
    (∫ x in A..B, phi x * Zeta23.mu x)
      =
    phi B * zetaMuPrimitive A B
      - ∫ x in A..B, deriv phi x * zetaMuPrimitive A x := by
  have hmuCont : Continuous Zeta23.mu :=
    Zeta23.RvM.mu_continuous Zeta23.gammaFacts
  have hMInt :
      IntervalIntegrable Zeta23.mu volume A B :=
    hmuCont.intervalIntegrable A B
  have hA : A ∈ Set.uIcc A B := by
    simp [Set.mem_uIcc]
  have hMac :
      AbsolutelyContinuousOnInterval (zetaMuPrimitive A) A B := by
    unfold zetaMuPrimitive
    exact hMInt.absolutelyContinuousOnInterval_intervalIntegral hA
  have hibp :=
    hphi.integral_mul_deriv_eq_deriv_mul hMac
  have hMderiv :
      deriv (zetaMuPrimitive A) = Zeta23.mu := by
    funext x
    exact (zetaMuPrimitive_hasDerivAt A x).deriv
  rw [hMderiv, zetaMuPrimitive_self] at hibp
  simpa using hibp

theorem zetaWindowMinusMuPair_eq_discrepancyAbel_ac
    {A B : ℝ}
    (hAB : A <= B)
    {phi : ℝ -> ℝ}
    (hphi : AbsolutelyContinuousOnInterval phi A B) :
    zetaWindowMinusMuPair A B phi
      =
    phi B * zetaMuCumulativeDiscrepancy A B
      -
    ∫ x in A..B,
      deriv phi x * zetaMuCumulativeDiscrepancy A x := by
  have hzero :=
    zetaWindowWeightedPair_eq_endpoint_sub_tail_ac
      hAB hphi
  have hderInt :
      IntervalIntegrable (deriv phi) volume A B :=
    hphi.intervalIntegrable_deriv
  have htail :=
    zetaWindowWeightedTailIntegral_eq_cumulativeCountIntegral
      (A:=A) (B:=B) hAB hderInt
  have hmu := zetaMu_integrationByParts_ac hphi
  have hNint :
      IntervalIntegrable
        (fun x => deriv phi x * (Ncount A x : ℝ))
        volume A B :=
    phi_mul_Ncount_intervalIntegrable hAB hderInt
  have hMint :
      IntervalIntegrable
        (fun x => deriv phi x * zetaMuPrimitive A x)
        volume A B :=
    phi_mul_zetaMuPrimitive_intervalIntegrable hderInt
  unfold zetaWindowMinusMuPair
  rw [hzero, htail, hmu]
  unfold zetaMuCumulativeDiscrepancy
  rw [← intervalIntegral.integral_sub hNint hMint]
  ring

end Synthesis
