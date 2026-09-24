import Synthesis.RiemannProjectiveQuarticNegativeZeroMu
import Synthesis.RiemannRvMMuIntervalLower

/-!
# Explicit count and negative-mass scale on the quartic window

For the physical inner quartic window

  A_t = t + r(q0-delta/2),
  B_t = t + r(q0+delta/2),   r=t/16,

the width is exactly

  B_t-A_t = r*delta = delta*t/16.

Since A_t>t, for t above the fixed RvM thresholds and t>=100 the exact mu
lower bound gives

  N(A_t,B_t)
    >= r*delta/20
       - C(log(A_t+3)+log(B_t+4)).

Combining this with the uniform negative kernel margin gives

  Z_Q(A_t,B_t)
    <= -(eta/r^2)
       * (r*delta/20 - C logs).

Thus the favourable main term is explicitly of order -1/t, while the counting
error enters at order log(t)/t^2.  This is the first target-independent strict
negative margin with the correct asymptotic separation in the quartic route.
-/

noncomputable section

open MeasureTheory Set
open scoped Real

namespace Synthesis

open Zeta23

theorem quarticNegativeWindow_width
    {W : QuarticHighWitness}
    (U : QuarticBaseUniformNegativeWindow W)
    (t : ℝ) :
    quarticNegativeWindowB U t
      - quarticNegativeWindowA U t
      =
    quarticNegativeWindowRadius t * U.delta := by
  unfold quarticNegativeWindowA quarticNegativeWindowB
    quarticNegativeWindowRadius
  ring

theorem exists_quarticNegativeWindow_Ncount_lower
    {W : QuarticHighWitness}
    (U : QuarticBaseUniformNegativeWindow W) :
    ∃ C T0 : ℝ, 0 <= C ∧
      ∀ t : ℝ,
        max T0 100 <= t ->
        quarticNegativeWindowRadius t * U.delta / 20
          - C *
            (Real.log (quarticNegativeWindowA U t + 3)
              + Real.log (quarticNegativeWindowB U t + 4))
          <=
        (Ncount
          (quarticNegativeWindowA U t)
          (quarticNegativeWindowB U t) : ℝ) := by
  obtain ⟨C, T0, hC, hcount⟩ :=
    exists_zetaCount_ge_muIntegral_sub_logError
  refine ⟨C, T0, hC, ?_⟩
  intro t ht
  have ht100 : 100 <= t := (le_max_right T0 100).trans ht
  have htpos : 0 < t := by linarith
  let A := quarticNegativeWindowA U t
  let B := quarticNegativeWindowB U t
  have htA : t < A := by
    dsimp [A]
    exact quarticNegativeWindow_t_lt_A U htpos
  have hAB : A < B := by
    dsimp [A,B]
    exact quarticNegativeWindowA_lt_B U htpos
  have hA100 : 100 <= A := ht100.trans htA.le
  have hAcount : max T0 4 <= A := by
    apply max_le
    · exact (le_max_left T0 100).trans ht |>.trans htA.le
    · linarith
  have hN := hcount A B hAcount hAB
  have hmu :=
    zetaMu_intervalIntegral_ge_width_div_twenty
      hA100 hAB.le
  have hwidth :
      (B-A)/20
        =
      quarticNegativeWindowRadius t * U.delta / 20 := by
    dsimp [A,B]
    rw [quarticNegativeWindow_width U t]
  rw [hwidth] at hmu
  dsimp [A,B] at hN hmu ⊢
  linarith

/--
Explicit negative quartic zero mass: -1/t main scale plus log(t)/t^2 counting
error.
-/
theorem exists_quarticNegativeWindow_zeroPair_explicit_upper
    (W : QuarticHighWitness)
    (U : QuarticBaseUniformNegativeWindow W) :
    ∃ C T0 : ℝ, 0 <= C ∧
      ∀ t : ℝ,
        max T0 100 <= t ->
        zetaWindowWeightedPair
            (quarticNegativeWindowA U t)
            (quarticNegativeWindowB U t)
            (quarticNegativeOrdinateTest W t)
          <=
        -(U.eta / (quarticNegativeWindowRadius t)^2)
          *
        (quarticNegativeWindowRadius t * U.delta / 20
          - C *
            (Real.log (quarticNegativeWindowA U t + 3)
              + Real.log (quarticNegativeWindowB U t + 4))) := by
  obtain ⟨C, T0, hC, hN⟩ :=
    exists_quarticNegativeWindow_Ncount_lower U
  refine ⟨C, T0, hC, ?_⟩
  intro t ht
  have ht100 : 100 <= t := (le_max_right T0 100).trans ht
  have htpos : 0 < t := by linarith
  have hpair := quarticNegativeWindow_zeroPair_le W U htpos
  have hcount := hN t ht
  let k : ℝ := U.eta / (quarticNegativeWindowRadius t)^2
  have hk : 0 <= k := by
    dsimp [k]
    positivity
  have hscaled :
      (-k) *
        (Ncount
          (quarticNegativeWindowA U t)
          (quarticNegativeWindowB U t) : ℝ)
        <=
      (-k) *
        (quarticNegativeWindowRadius t * U.delta / 20
          - C *
            (Real.log (quarticNegativeWindowA U t + 3)
              + Real.log (quarticNegativeWindowB U t + 4))) := by
    exact mul_le_mul_of_nonpos_left hcount (by linarith)
  dsimp [k] at hscaled
  exact hpair.trans hscaled

end Synthesis
