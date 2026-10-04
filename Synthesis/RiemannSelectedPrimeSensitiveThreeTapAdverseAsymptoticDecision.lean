import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAdverseMassCollapse

/-!
# Final asymptotic decision surface for the one-scale route

The half-height finite core is now controlled by one canonical normalized mass
M0.  This file factors its explicit log-over-t envelope as

  LogBudget = M0 * Q(t; C, Cmu),

where Q is completely explicit.  The remaining one-scale analytic inputs are
therefore exactly:

* an upper bound M0 <= M,
* an upper bound Far(t/2) <= F,
* a lower bound H <= LocalExact - Compensation,
* the scalar comparison 1/2 (M Q + F) < H.

No asymptotic hypothesis is asserted here.  This is the producer-facing
compiler that a genuine zeta-distribution estimate must feed.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators Interval

/-- Explicit finite-core coefficient after the R=t/2 and M1->M0 cuts. -/
def threeTapHalfHeightLogCoefficient
    (t C Cmu : ℝ) : ℝ :=
  (256/t) * (Cmu * (Real.log t + 1))
    + (256/t^2) * (C * (2*Real.log t + 1))
    + (2048/(5*t)) * (C * (2*Real.log t + 1))

theorem threeTapHalfHeightLogCoefficient_nonneg
    {t C Cmu : ℝ}
    (ht : 200 <= t)
    (hC : 0 <= C)
    (hCmu : 0 <= Cmu) :
    0 <= threeTapHalfHeightLogCoefficient t C Cmu := by
  have hlog : 0 <= Real.log t := Real.log_nonneg (by linarith)
  unfold threeTapHalfHeightLogCoefficient
  positivity

/-- Exact factorization of the explicit finite-core envelope. -/
theorem QuarticFourSignedPolePair.threeTapAdverseHalfHeightLogBudget_eq_M0_mul_coefficient
    {t eps C Cmu : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapAdverseHalfHeightLogBudget eps C Cmu
      =
    W.threeTapCanonicalM0 eps * threeTapHalfHeightLogCoefficient t C Cmu := by
  unfold QuarticFourSignedPolePair.threeTapAdverseHalfHeightLogBudget
    threeTapHalfHeightLogCoefficient
  ring

/-- A uniform upper bound on M0 immediately transports to the finite budget. -/
theorem QuarticFourSignedPolePair.threeTapAdverseHalfHeightLogBudget_le_of_M0_le
    {t eps C Cmu M : ℝ}
    (ht : 200 <= t)
    (hC : 0 <= C)
    (hCmu : 0 <= Cmu)
    (W : QuarticFourSignedPolePair t)
    (hM : W.threeTapCanonicalM0 eps <= M) :
    W.threeTapAdverseHalfHeightLogBudget eps C Cmu
      <= M * threeTapHalfHeightLogCoefficient t C Cmu := by
  rw [W.threeTapAdverseHalfHeightLogBudget_eq_M0_mul_coefficient]
  exact mul_le_mul_of_nonneg_right hM
    (threeTapHalfHeightLogCoefficient_nonneg ht hC hCmu)

/-- Coarsest half-height scalar after replacing the finite profile mass by an
external producer bound M. -/
def QuarticFourSignedPolePair.ThreeTapAdverseHalfHeightAsymptoticScalar
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps C Cmu M F H : ℝ) : ℝ :=
  (1/2 : ℝ) *
    (M * threeTapHalfHeightLogCoefficient t C Cmu + F) - H

/-- Universal asymptotic compiler.  Once a producer supplies M, F and H with
the stated same-object bounds, the displayed scalar inequality closes the
actual paid resonance cost. -/
theorem QuarticFourSignedPolePair.exists_threeTapHalfHeightAsymptoticPass_constants :
    ∃ C Cmu : ℝ, 0 <= C ∧ 0 <= Cmu ∧
      ∀ {t eps M F H : ℝ},
        200 <= t ->
        ∀ W : QuarticFourSignedPolePair t,
        W.threeTapCanonicalM0 eps <= M ->
        W.threeTapPairAdverseFarAfter eps (t/2) <= F ->
        H <= W.threeTapAdaptiveLocalExact eps
            - W.threeTapResonanceCompensation eps ->
        W.ThreeTapAdverseHalfHeightAsymptoticScalar eps C Cmu M F H < 0 ->
        W.threeTapResonancePaidCost eps < 0 := by
  obtain ⟨C,Cmu,hC,hCmu,hcut⟩ :=
    QuarticFourSignedPolePair.exists_threeTapAdverseCanonicalFinalCut_constants
  refine ⟨C,Cmu,hC,hCmu,?_⟩
  intro t eps M F H ht W hM hfar hH hscalar
  have hnear0 := W.threeTapAdverseNearExplicitBudget_le_scaleBudget
    (eps:=eps) (R:=t/2) (C:=C) (Cmu:=Cmu)
    ht (by linarith) hC hCmu (by linarith)
  have hclosed := W.threeTapAdverseHalfHeightScaleBudget_eq_closed
    (eps:=eps) (C:=C) (Cmu:=Cmu) (by linarith : 0 < t)
  have hcollapse := W.threeTapAdverseHalfHeightClosedBudget_le_logBudget
    ht hC hCmu (eps:=eps)
  have hmass := W.threeTapAdverseHalfHeightLogBudget_le_of_M0_le
    ht hC hCmu (eps:=eps) hM
  have hnear :
      W.threeTapAdverseNearExplicitBudget eps
          (threeTapCanonicalAlphaRadius t) (t/2) C Cmu
        <= M * threeTapHalfHeightLogCoefficient t C Cmu := by
    exact hnear0.trans ((le_of_eq hclosed).trans (hcollapse.trans hmass))
  have hbudget :
      (1/2 : ℝ) *
        (W.threeTapAdverseNearExplicitBudget eps
            (threeTapCanonicalAlphaRadius t) (t/2) C Cmu
          + W.threeTapPairAdverseFarAfter eps (t/2))
        < W.threeTapAdaptiveLocalExact eps
            - W.threeTapResonanceCompensation eps := by
    unfold QuarticFourSignedPolePair.ThreeTapAdverseHalfHeightAsymptoticScalar at hscalar
    have hsum := add_le_add hnear hfar
    have hhalf := mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ) <= 1/2)
    linarith
  apply hcut ht W (W.threeTapHalfHeightCutoff_compatible ht)
  exact hbudget

/-- Same asymptotic compiler directly to the near-line resonance PASS band. -/
theorem QuarticFourSignedPolePair.exists_threeTapHalfHeightAsymptoticPass_terminal_constants :
    ∃ C Cmu : ℝ, 0 <= C ∧ 0 <= Cmu ∧
      ∀ {t eps mult M F H : ℝ},
        200 <= t ->
        ∀ W : QuarticFourSignedPolePair t,
        Real.cos (t * Real.log 2) = 0 ->
        W.threeTapCanonicalM0 eps <= M ->
        W.threeTapPairAdverseFarAfter eps (t/2) <= F ->
        H <= W.threeTapAdaptiveLocalExact eps
            - W.threeTapResonanceCompensation eps ->
        W.ThreeTapAdverseHalfHeightAsymptoticScalar eps C Cmu M F H < 0 ->
        ∃ delta : ℝ, 0 < delta ∧
          ∀ a : ℝ, 0 < a -> a < delta ->
            0 < W.threeTapAdaptiveTerminalProfile eps mult a := by
  obtain ⟨C,Cmu,hC,hCmu,hpass⟩ :=
    QuarticFourSignedPolePair.exists_threeTapHalfHeightAsymptoticPass_constants
  refine ⟨C,Cmu,hC,hCmu,?_⟩
  intro t eps mult M F H ht W hphase hM hfar hH hscalar
  apply W.exists_threeTapResonantTerminalProfile_pos_right_of_paidCost_neg ht hphase
  exact hpass ht W hM hfar hH hscalar

end Synthesis
