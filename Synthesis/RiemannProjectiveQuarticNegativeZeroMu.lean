import Synthesis.RiemannProjectiveQuarticNegativeZeroWindow
import Synthesis.RiemannRvMMuHighPositive

/-!
# Quartic negative zero mass from exact mu minus Backlund error

The physical quartic negative window lies strictly to the right of the target
ordinate t because delta < q0.  Hence for high t the arbitrary-endpoint
N-mu discrepancy theorem applies directly on this window.

Combining

  Z_Q(A_t,B_t) <= -(eta/r^2) N(A_t,B_t)

with

  N(A_t,B_t)
    >= integral_A_t^B_t mu
       - C (log(A_t+3)+log(B_t+4))

gives the signed estimate

  Z_Q(A_t,B_t)
    <= -(eta/r^2)
       * ( integral_A_t^B_t mu - logarithmic error ).

This is the first theorem-bearing quantitative negative contribution in the
quartic high route.  The remaining asymptotic task is to show that the mu mass
of the O(t)-wide window dominates the O(log t) discrepancy and the surviving
external tails.
-/

noncomputable section

open MeasureTheory Set
open scoped Real

namespace Synthesis

open Zeta23

theorem quarticNegativeWindow_t_lt_A
    {W : QuarticHighWitness}
    (U : QuarticBaseUniformNegativeWindow W)
    {t : ℝ} (ht : 0 < t) :
    t < quarticNegativeWindowA U t := by
  unfold quarticNegativeWindowA quarticNegativeWindowRadius
  have hr : 0 < t/16 := by positivity
  have hcenter : 0 < U.q0 - U.delta/2 := by
    linarith [U.q0Pos, U.deltaLtQ0]
  nlinarith

theorem quarticNegativeWindow_t_lt_B
    {W : QuarticHighWitness}
    (U : QuarticBaseUniformNegativeWindow W)
    {t : ℝ} (ht : 0 < t) :
    t < quarticNegativeWindowB U t :=
  lt_trans (quarticNegativeWindow_t_lt_A U ht)
    (quarticNegativeWindowA_lt_B U ht)

/--
The quartic negative window bound centered by the exact theorem-bearing mu
measure, with only the arbitrary-endpoint Backlund discrepancy left as error.
-/
theorem exists_quarticNegativeWindow_zeroPair_le_mu_sub_error
    (W : QuarticHighWitness)
    (U : QuarticBaseUniformNegativeWindow W) :
    ∃ C T0 : ℝ, 0 <= C ∧
      ∀ t : ℝ,
        max T0 4 <= t ->
        zetaWindowWeightedPair
            (quarticNegativeWindowA U t)
            (quarticNegativeWindowB U t)
            (quarticNegativeOrdinateTest W t)
          <=
        -(U.eta / (quarticNegativeWindowRadius t)^2)
          *
        ((∫ tau in
            quarticNegativeWindowA U t..
            quarticNegativeWindowB U t,
            Zeta23.mu tau)
          -
          C *
            (Real.log (quarticNegativeWindowA U t + 3)
              + Real.log (quarticNegativeWindowB U t + 4))) := by
  obtain ⟨C, T0, hC, hcount⟩ :=
    exists_zetaCount_ge_muIntegral_sub_logError
  refine ⟨C, T0, hC, ?_⟩
  intro t ht
  have ht4 : 4 <= t := (le_max_right T0 4).trans ht
  have htpos : 0 < t := by linarith
  let A := quarticNegativeWindowA U t
  let B := quarticNegativeWindowB U t
  have htA : t < A := by
    dsimp [A]
    exact quarticNegativeWindow_t_lt_A U htpos
  have hAB : A < B := by
    dsimp [A,B]
    exact quarticNegativeWindowA_lt_B U htpos
  have hA : max T0 4 <= A := by
    exact ht.trans htA.le
  have hN :=
    hcount A B hA hAB
  have hpair :=
    quarticNegativeWindow_zeroPair_le W U htpos
  let k : ℝ :=
    U.eta / (quarticNegativeWindowRadius t)^2
  have hk : 0 <= k := by
    dsimp [k]
    positivity
  have hscaled :
      (-k) * (Ncount A B : ℝ)
        <=
      (-k) *
        ((∫ tau in A..B, Zeta23.mu tau)
          - C * (Real.log (A+3) + Real.log (B+4))) := by
    exact mul_le_mul_of_nonpos_left hN (by linarith)
  dsimp [A,B,k] at hpair hscaled ⊢
  exact hpair.trans hscaled

end Synthesis
