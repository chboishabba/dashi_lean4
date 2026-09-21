import Synthesis.RiemannZetaFiniteAtomicAbel

/-!
# Uniformly negative tests give negative zero mass

For the literal finite zero window (A,B], if a real test satisfies

  phi(gamma) <= -eta

at every zero ordinate in that window, with eta >= 0, then its multiplicity
weighted zero pairing satisfies

  Z_phi(A,B) <= -eta * N(A,B).

This is the finite atomic monotonicity statement needed by the quartic negative
window argument.  It keeps the exact Zeta23 multiplicities and uses no counting
approximation.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Interval Real

namespace Synthesis

open Zeta23

theorem zetaWindowWeightedPair_le_neg_mul_Ncount
    {A B eta : ℝ}
    {phi : ℝ -> ℝ}
    (heta : 0 <= eta)
    (hphi :
      ∀ rho : ℂ,
        rho ∈ zetaZeroConfig.window A B ->
        phi rho.im <= -eta) :
    zetaWindowWeightedPair A B phi
      <=
    -eta * (Ncount A B : ℝ) := by
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

  have hN :
      (Ncount A B : ℝ)
        =
      ∑ rho ∈ F, (zetaZeroConfig.mult rho : ℝ) := by
    rw [← zetaZeroConfig_N]
    unfold ZeroConfig.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    push_cast
    rfl

  rw [hpair, hN, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro rho hrho
  have hrhoSet :
      rho ∈ zetaZeroConfig.window A B := by
    simpa [F, hfin] using hrho
  have hm : 0 <= (zetaZeroConfig.mult rho : ℝ) := by
    positivity
  exact mul_le_mul_of_nonneg_left (hphi rho hrhoSet) hm

end Synthesis
