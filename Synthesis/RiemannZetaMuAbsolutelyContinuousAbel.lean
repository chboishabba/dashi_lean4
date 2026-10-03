import Synthesis.RiemannZetaMuExactAbel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

/-!
# Exact literal N-mu Abel identity for absolutely continuous tests

The sign-preserving adverse envelopes arising later are naturally absolutely
continuous but need not be C1 at phase crossings.  The existing exact Abel
owner asked for an everywhere derivative.  This file removes that unnecessary
regularity restriction without changing the literal zero carrier or the
RvM density.

For an absolutely continuous `phi` on `[A,B]`,

  Z_phi(A,B) - integral phi mu
    = phi(B) D_A(B) - integral (deriv phi)(x) D_A(x) dx.

The proof uses the AC fundamental theorem atom-by-atom on the finite literal
zero window and Mathlib's AC integration-by-parts theorem on the mu side.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set
open scoped BigOperators Interval Real
open Zeta23

/-- The theorem-bearing mu primitive is absolutely continuous on every finite
interval. -/
theorem zetaMuPrimitive_absolutelyContinuousOnInterval
    (A B : ℝ) :
    AbsolutelyContinuousOnInterval (zetaMuPrimitive A) A B := by
  have hmu : IntervalIntegrable Zeta23.mu volume A B :=
    Zeta23.gammaFacts.smooth.continuous.intervalIntegrable A B
  exact hmu.absolutelyContinuousOnInterval_intervalIntegral (by simp)

/-- AC integration by parts against the literal RvM density. -/
theorem zetaMu_integrationByParts_ac
    {A B : ℝ} {phi : ℝ → ℝ}
    (hphi : AbsolutelyContinuousOnInterval phi A B) :
    (∫ x in A..B, phi x * Zeta23.mu x)
      =
    phi B * zetaMuPrimitive A B
      - ∫ x in A..B, deriv phi x * zetaMuPrimitive A x := by
  have hM := zetaMuPrimitive_absolutelyContinuousOnInterval A B
  have hibp :=
    AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul
      hphi hM
  have hderivM :
      (fun x : ℝ => deriv (zetaMuPrimitive A) x)
        = Zeta23.mu := by
    funext x
    exact (zetaMuPrimitive_hasDerivAt A x).deriv
  rw [hderivM, zetaMuPrimitive_self] at hibp
  simpa using hibp

/-- Finite literal atomic Abel formula for an AC test. -/
theorem zetaWindowWeightedPair_eq_endpoint_sub_tail_ac
    {A B : ℝ} {phi : ℝ → ℝ}
    (hAB : A <= B)
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
        = ∑ rho ∈ F, (zetaZeroConfig.mult rho : ℝ) := by
    rw [← zetaZeroConfig_N]
    unfold ZeroConfig.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    push_cast
    rfl
  rw [hpair, htail, hN]
  have hatom :
      ∀ rho ∈ F,
        phi rho.im
          = phi B - ∫ x in rho.im..B, deriv phi x := by
    intro rho hrho
    have hrhoSet : rho ∈ zetaZeroConfig.window A B := by
      simpa [F, hfin] using hrho
    have hrange : rho.im ∈ Set.Icc A B :=
      ⟨le_of_lt hrhoSet.2.1, hrhoSet.2.2⟩
    have hsub :
        AbsolutelyContinuousOnInterval phi rho.im B := by
      apply hphi.mono
      rw [uIcc_of_le hAB, uIcc_of_le hrange.2]
      intro x hx
      exact ⟨hrange.1.trans hx.1, hx.2⟩
    have hFTC := hsub.integral_deriv_eq_sub
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

/-- Exact same-object N-mu Abel identity at AC regularity. -/
theorem zetaWindowMinusMuPair_eq_discrepancyAbel_ac
    {A B : ℝ} {phi : ℝ → ℝ}
    (hAB : A <= B)
    (hphi : AbsolutelyContinuousOnInterval phi A B) :
    zetaWindowMinusMuPair A B phi
      =
    phi B * zetaMuCumulativeDiscrepancy A B
      -
    ∫ x in A..B,
      deriv phi x * zetaMuCumulativeDiscrepancy A x := by
  have hderivInt : IntervalIntegrable (deriv phi) volume A B :=
    hphi.intervalIntegrable_deriv
  have hzero :=
    zetaWindowWeightedPair_eq_endpoint_sub_tail_ac hAB hphi
  have htail :=
    zetaWindowWeightedTailIntegral_eq_cumulativeCountIntegral
      hAB hderivInt
  have hmu := zetaMu_integrationByParts_ac hphi
  have hNint :
      IntervalIntegrable
        (fun x => deriv phi x * (Ncount A x : ℝ))
        volume A B :=
    phi_mul_Ncount_intervalIntegrable hAB hderivInt
  have hMint :
      IntervalIntegrable
        (fun x => deriv phi x * zetaMuPrimitive A x)
        volume A B :=
    phi_mul_zetaMuPrimitive_intervalIntegrable hderivInt
  unfold zetaWindowMinusMuPair
  rw [hzero, htail, hmu]
  unfold zetaMuCumulativeDiscrepancy
  rw [← intervalIntegral.integral_sub hNint hMint]
  ring

end Synthesis
