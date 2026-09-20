import Synthesis.RiemannRvMMuIntegrationByParts
import Zeta23.Statement.SeamClosed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exact finite atomic Abel identity on the literal Zeta23 zero window

For the actual finite window of nontrivial zeros

  A < Im rho <= B,

define the multiplicity-weighted test pairing

  Z_phi(A,B) = sum_rho m_rho phi(Im rho).

No counting approximation enters.  FTC at each atom gives

  phi(Im rho)
    = phi(B) - integral_(Im rho)^B phi'(x) dx,

and because the literal window is finite these identities sum exactly:

  Z_phi(A,B)
    = phi(B) N(A,B)
      - sum_rho m_rho integral_(Im rho)^B phi'(x) dx.

The next theorem layer identifies the final finite sum of tails with
integral_A^B phi'(x) N(A,x) dx.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Interval Real

namespace Synthesis

open Zeta23

def zetaWindowWeightedPair
    (A B : ℝ) (phi : ℝ -> ℝ) : ℝ :=
  ∑ᶠ rho ∈ zetaZeroConfig.window A B,
    (zetaZeroConfig.mult rho : ℝ) * phi rho.im

def zetaWindowWeightedTailIntegral
    (A B : ℝ) (phi' : ℝ -> ℝ) : ℝ :=
  ∑ᶠ rho ∈ zetaZeroConfig.window A B,
    (zetaZeroConfig.mult rho : ℝ)
      * (∫ x in rho.im..B, phi' x)

theorem zetaWindowWeightedPair_eq_endpoint_sub_tail
    {A B : ℝ}
    {phi phi' : ℝ -> ℝ}
    (hderiv : ∀ x ∈ Set.Icc A B, HasDerivAt phi (phi' x) x)
    (hint : IntervalIntegrable phi' volume A B) :
    zetaWindowWeightedPair A B phi
      =
    phi B * (Ncount A B : ℝ)
      - zetaWindowWeightedTailIntegral A B phi' := by
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
      zetaWindowWeightedTailIntegral A B phi'
        =
      ∑ rho ∈ F,
        (zetaZeroConfig.mult rho : ℝ)
          * (∫ x in rho.im..B, phi' x) := by
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
        phi B - ∫ x in rho.im..B, phi' x := by
    intro rho hrho
    have hrhoSet :
        rho ∈ zetaZeroConfig.window A B := by
      simpa [F, hfin] using hrho
    have hrange : rho.im ∈ Set.Icc A B := by
      exact ⟨le_of_lt hrhoSet.2.1, hrhoSet.2.2⟩
    have hsub :
        (∫ x in rho.im..B, phi' x)
          = phi B - phi rho.im := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x hx
        have hx' : x ∈ Set.Icc A B := by
          rw [Set.uIcc_of_le hrange.2] at hx
          exact ⟨hrange.1.trans hx.1, hx.2⟩
        exact hderiv x hx'
      · exact hint.mono_set
          (by
            rw [Set.uIcc_of_le hrange.2,
                Set.uIcc_of_le (le_trans hrange.1 hrange.2)]
            intro x hx
            exact ⟨hrange.1.trans hx.1, hx.2⟩)
    linarith

  calc
    (∑ rho ∈ F,
      (zetaZeroConfig.mult rho : ℝ) * phi rho.im)
      =
    ∑ rho ∈ F,
      (zetaZeroConfig.mult rho : ℝ)
        * (phi B - ∫ x in rho.im..B, phi' x) := by
          apply Finset.sum_congr rfl
          intro rho hrho
          rw [hatom rho hrho]
    _ =
      phi B * (∑ rho ∈ F, (zetaZeroConfig.mult rho : ℝ))
        -
      ∑ rho ∈ F,
        (zetaZeroConfig.mult rho : ℝ)
          * (∫ x in rho.im..B, phi' x) := by
          rw [Finset.mul_sum]
          ring

end Synthesis
