import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAdverseAsymptoticDecision
import Synthesis.RiemannSelectedSignedFifthCorrelationCut

/-!
# Final scalar splits for the RH max-cut

This file does not add a zeta-distribution estimate.  It only rewrites the two
live analytic routes into producer-facing scalar obligations.

Route A: after the canonical R=t/2 cut and the M1 -> M0 collapse, it is enough
to find one same-object floor H such that

  M * Q(t;C,Cmu) <= H,
  Far(t/2) < H,
  H <= LocalExact - Compensation.

The first two inequalities imply

  1/2 * (M Q + Far) < H,

so the existing asymptotic compiler closes the paid resonance cost.

Route B: define the exact finite signed-fifth gap

  Credit - Debt + OuterBudget - 3 eps.

Nonnegativity of this gap is definitionally equivalent to the correlation
inequality already consumed by the signed-fifth interior target.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators Interval

/-- Split-budget Route-A compiler.  The genuinely analytic obligations are now
separate same-object estimates for the finite M0 log-over-t core, the actual
far adverse tail, and the available local compensation floor. -/
theorem QuarticFourSignedPolePair.exists_threeTapHalfHeightSplitPass_constants :
    ∃ C Cmu : ℝ, 0 <= C ∧ 0 <= Cmu ∧
      ∀ {t eps M H : ℝ},
        200 <= t ->
        ∀ W : QuarticFourSignedPolePair t,
        W.threeTapCanonicalM0 eps <= M ->
        M * threeTapHalfHeightLogCoefficient t C Cmu <= H ->
        W.threeTapPairAdverseFarAfter eps (t/2) < H ->
        H <= W.threeTapAdaptiveLocalExact eps
            - W.threeTapResonanceCompensation eps ->
        W.threeTapResonancePaidCost eps < 0 := by
  obtain ⟨C,Cmu,hC,hCmu,hpass⟩ :=
    QuarticFourSignedPolePair.exists_threeTapHalfHeightAsymptoticPass_constants
  refine ⟨C,Cmu,hC,hCmu,?_⟩
  intro t eps M H ht W hM hfinite hfar hH
  apply hpass ht W hM (le_rfl) hH
  unfold QuarticFourSignedPolePair.ThreeTapAdverseHalfHeightAsymptoticScalar
  linarith

/-- The same split scalar closes the near-line resonance PASS band directly. -/
theorem QuarticFourSignedPolePair.exists_threeTapHalfHeightSplitPass_terminal_constants :
    ∃ C Cmu : ℝ, 0 <= C ∧ 0 <= Cmu ∧
      ∀ {t eps mult M H : ℝ},
        200 <= t ->
        ∀ W : QuarticFourSignedPolePair t,
        Real.cos (t * Real.log 2) = 0 ->
        W.threeTapCanonicalM0 eps <= M ->
        M * threeTapHalfHeightLogCoefficient t C Cmu <= H ->
        W.threeTapPairAdverseFarAfter eps (t/2) < H ->
        H <= W.threeTapAdaptiveLocalExact eps
            - W.threeTapResonanceCompensation eps ->
        ∃ delta : ℝ, 0 < delta ∧
          ∀ a : ℝ, 0 < a -> a < delta ->
            0 < W.threeTapAdaptiveTerminalProfile eps mult a := by
  obtain ⟨C,Cmu,hC,hCmu,hpass⟩ :=
    QuarticFourSignedPolePair.exists_threeTapHalfHeightSplitPass_constants
  refine ⟨C,Cmu,hC,hCmu,?_⟩
  intro t eps mult M H ht W hphase hM hfinite hfar hH
  apply W.exists_threeTapResonantTerminalProfile_pos_right_of_paidCost_neg ht hphase
  exact hpass ht W hM hfinite hfar hH

/-- Exact signed-fifth credit-minus-debt scalar at a finite physical cutoff. -/
def QuarticFourSignedPolePair.signedFifthCorrelationGapAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV eps : ℝ) (n : ℕ) : ℝ :=
  W.signedFifthCorrelationCreditAt n
    - W.signedFifthCorrelationDebtAt n
    + W.outerVerticalAbsoluteBudget rho EV
    - 3*eps

/-- The Route-B scalar gap is exactly the existing credit/debt threshold
condition, with no loss from absolute-value replacement. -/
theorem QuarticFourSignedPolePair.signedFifthCorrelationGapAt_nonneg_iff
    {t EV eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (n : ℕ) :
    0 <= W.signedFifthCorrelationGapAt rho EV eps n
      ↔
    W.signedFifthCorrelationDebtAt n
        - W.outerVerticalAbsoluteBudget rho EV + 3*eps
      <= W.signedFifthCorrelationCreditAt n := by
  unfold QuarticFourSignedPolePair.signedFifthCorrelationGapAt
  constructor <;> intro h <;> linarith

/-- Eventual nonnegativity of the single Route-B gap is sufficient for the
already-owned signed-fifth interior target. -/
theorem QuarticFourSignedPolePair.signedFifthInteriorTarget_of_eventual_gap_nonneg
    {t EV eps : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (hlarge :
      ∀ᶠ n : ℕ in atTop,
        quarticSignedPoleCanonicalPhysicalHalfWidth t <= (n : ℝ))
    (hgap :
      ∀ᶠ n : ℕ in atTop,
        0 <= W.signedFifthCorrelationGapAt rho EV eps n) :
    W.SignedFifthInteriorTarget rho EV eps := by
  apply W.signedFifthInteriorTarget_of_eventual_credit_ge_debt_plus_threshold
    ht rho hlarge
  filter_upwards [hgap] with n hn
  exact (W.signedFifthCorrelationGapAt_nonneg_iff rho n).1 hn

end Synthesis
