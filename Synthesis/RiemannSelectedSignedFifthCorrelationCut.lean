import Synthesis.RiemannSelectedSignedFifthMaxCut
import Synthesis.RiemannQuarticFourthPrimitiveClassicalRemainder

/-!
# Signed-fifth correlation max-cut

The signed-fifth cap is a genuine correlation, not an absolute primitive norm:

  C5_W(q) * P4_t(q),

where the existing classical-remainder owner identifies `P4_t(q)` with a
cubic Cesaro integral of the literal two-sided RvM discrepancy.  This file
preserves that sign by splitting the correlation into nonnegative favorable
credit and nonnegative adverse debt.

No lower bound for the credit and no upper bound for the debt is invented.
The remaining Route-B theorem is exposed as a direct credit-versus-debt
comparison against the already-owned terminal threshold.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real

/-- Exact signed correlation integrand before the outer q integration. -/
def QuarticFourSignedPolePair.signedFifthCorrelationIntegrand
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (q : ℝ) : ℝ :=
  compactCosineD5
      (quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t) q
    * anchoredPrimitive4
        W.quarticScaleSymmetricWindowDiscrepancy
        quarticSignedPoleCanonicalLocalRadius q

/-- Positive correlation credit. -/
def QuarticFourSignedPolePair.signedFifthCorrelationCreditIntegrand
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (q : ℝ) : ℝ :=
  (W.signedFifthCorrelationIntegrand q
    + |W.signedFifthCorrelationIntegrand q|) / 2

/-- Magnitude of the negative correlation debt. -/
def QuarticFourSignedPolePair.signedFifthCorrelationDebtIntegrand
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (q : ℝ) : ℝ :=
  (|W.signedFifthCorrelationIntegrand q|
    - W.signedFifthCorrelationIntegrand q) / 2

theorem QuarticFourSignedPolePair.signedFifthCorrelationCreditIntegrand_nonneg
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (q : ℝ) :
    0 <= W.signedFifthCorrelationCreditIntegrand q := by
  unfold QuarticFourSignedPolePair.signedFifthCorrelationCreditIntegrand
  by_cases h : 0 <= W.signedFifthCorrelationIntegrand q
  · rw [abs_of_nonneg h]
    linarith
  · have h' : W.signedFifthCorrelationIntegrand q <= 0 := le_of_not_ge h
    rw [abs_of_nonpos h']
    ring

theorem QuarticFourSignedPolePair.signedFifthCorrelationDebtIntegrand_nonneg
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (q : ℝ) :
    0 <= W.signedFifthCorrelationDebtIntegrand q := by
  unfold QuarticFourSignedPolePair.signedFifthCorrelationDebtIntegrand
  exact div_nonneg (sub_nonneg.mpr (le_abs_self _)) (by norm_num)

theorem QuarticFourSignedPolePair.signedFifthCorrelationIntegrand_eq_credit_sub_debt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (q : ℝ) :
    W.signedFifthCorrelationIntegrand q
      = W.signedFifthCorrelationCreditIntegrand q
        - W.signedFifthCorrelationDebtIntegrand q := by
  unfold QuarticFourSignedPolePair.signedFifthCorrelationCreditIntegrand
    QuarticFourSignedPolePair.signedFifthCorrelationDebtIntegrand
  ring

/-- The primitive factor in the correlation is exactly the two-sided literal
RvM Cesaro primitive, including the q>16 negative-ordinate crossing. -/
theorem QuarticFourSignedPolePair.signedFifthCorrelationIntegrand_eq_twoSidedRemainder
    {t q : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hq : quarticSignedPoleCanonicalLocalRadius <= q) :
    W.signedFifthCorrelationIntegrand q
      =
    compactCosineD5
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t) q
      *
    (∫ s in
      ((t/16)*quarticSignedPoleCanonicalLocalRadius)..((t/16)*q),
      (((t/16)*q-s)^3/6) * zetaMuFullSymmetricRemainder t s) := by
  unfold QuarticFourSignedPolePair.signedFifthCorrelationIntegrand
  rw [W.anchoredFourth_eq_physicalFourthPrimitive ht hq,
      W.physicalFourthPrimitive_eq_fullSymmetricRemainder ht hq]

/-- Favorable correlation means the fifth kernel and the actual two-sided
fourth primitive have matching sign. -/
def QuarticFourSignedPolePair.SignedFifthCorrelationFavorable
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (q : ℝ) : Prop :=
  0 <= W.signedFifthCorrelationIntegrand q

/-- On the favorable q-set the debt vanishes identically. -/
theorem QuarticFourSignedPolePair.signedFifthCorrelationDebtIntegrand_eq_zero_of_favorable
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    {q : ℝ}
    (h : W.SignedFifthCorrelationFavorable q) :
    W.signedFifthCorrelationDebtIntegrand q = 0 := by
  unfold QuarticFourSignedPolePair.SignedFifthCorrelationFavorable at h
  unfold QuarticFourSignedPolePair.signedFifthCorrelationDebtIntegrand
  rw [abs_of_nonneg h]
  ring

/-- On an adverse q the positive credit vanishes, so only the signed debt is
paid. -/
theorem QuarticFourSignedPolePair.signedFifthCorrelationCreditIntegrand_eq_zero_of_adverse
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    {q : ℝ}
    (h : W.signedFifthCorrelationIntegrand q <= 0) :
    W.signedFifthCorrelationCreditIntegrand q = 0 := by
  unfold QuarticFourSignedPolePair.signedFifthCorrelationCreditIntegrand
  rw [abs_of_nonpos h]
  ring

def QuarticFourSignedPolePair.signedFifthCorrelationCreditAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (n : ℕ) : ℝ :=
  ∫ q in quarticSignedPoleCanonicalLocalRadius..((n : ℝ)/(t/16)),
    W.signedFifthCorrelationCreditIntegrand q

def QuarticFourSignedPolePair.signedFifthCorrelationDebtAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (n : ℕ) : ℝ :=
  ∫ q in quarticSignedPoleCanonicalLocalRadius..((n : ℝ)/(t/16)),
    W.signedFifthCorrelationDebtIntegrand q

/-- Exact finite cap decomposition.  The hypotheses are the same physical
cutoff hypotheses already required by the signed fifth-cap owner. -/
theorem QuarticFourSignedPolePair.signedFifthPhysicalCapInteriorAt_eq_credit_sub_debt
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hn : quarticSignedPoleCanonicalPhysicalHalfWidth t <= (n : ℝ)) :
    W.signedFifthPhysicalCapInteriorAt n
      = W.signedFifthCorrelationCreditAt n
        - W.signedFifthCorrelationDebtAt n := by
  have hr : 0 < t/16 := by positivity
  have hQ :
      quarticSignedPoleCanonicalLocalRadius <= (n : ℝ)/(t/16) := by
    rw [le_div_iff₀ hr]
    exact hn
  have hA :
      IntervalIntegrable
        W.quarticScaleSymmetricWindowDiscrepancy volume
        quarticSignedPoleCanonicalLocalRadius ((n : ℝ)/(t/16)) :=
    W.quarticScaleSymmetricWindowDiscrepancy_intervalIntegrable hQ
  obtain ⟨_,_,_,hP4ac⟩ := anchoredPrimitive_ladder_ac hA
  let P : ℝ → ℝ :=
    quarticFourSignedPoleCombinedProfile W.R W.muHalf W.muTwo t
  have hC5 : Continuous (compactCosineD5 P) :=
    compactCosineD5_continuous
      (quarticFourSignedPoleCombinedProfile_continuous W.Rpos)
      (quarticFourSignedPoleCombinedProfile_compact W.Rpos)
  have hbase :
      IntervalIntegrable W.signedFifthCorrelationIntegrand volume
        quarticSignedPoleCanonicalLocalRadius ((n : ℝ)/(t/16)) := by
    unfold QuarticFourSignedPolePair.signedFifthCorrelationIntegrand
    exact (hC5.continuousOn.mul hP4ac.continuousOn).intervalIntegrable
  have hcredit :
      IntervalIntegrable W.signedFifthCorrelationCreditIntegrand volume
        quarticSignedPoleCanonicalLocalRadius ((n : ℝ)/(t/16)) := by
    unfold QuarticFourSignedPolePair.signedFifthCorrelationCreditIntegrand
    exact (hbase.add hbase.abs).const_mul (1/2 : ℝ)
  have hdebt :
      IntervalIntegrable W.signedFifthCorrelationDebtIntegrand volume
        quarticSignedPoleCanonicalLocalRadius ((n : ℝ)/(t/16)) := by
    unfold QuarticFourSignedPolePair.signedFifthCorrelationDebtIntegrand
    exact (hbase.abs.sub hbase).const_mul (1/2 : ℝ)
  unfold QuarticFourSignedPolePair.signedFifthPhysicalCapInteriorAt
    QuarticFourSignedPolePair.signedFifthCorrelationCreditAt
    QuarticFourSignedPolePair.signedFifthCorrelationDebtAt
    QuarticFourSignedPolePair.signedFifthCorrelationIntegrand
  rw [← intervalIntegral.integral_sub hcredit hdebt]
  apply intervalIntegral.integral_congr
  intro q hq
  exact W.signedFifthCorrelationIntegrand_eq_credit_sub_debt q

theorem QuarticFourSignedPolePair.signedFifthCorrelationCreditAt_nonneg
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hQ : quarticSignedPoleCanonicalLocalRadius <= (n : ℝ)/(t/16)) :
    0 <= W.signedFifthCorrelationCreditAt n := by
  unfold QuarticFourSignedPolePair.signedFifthCorrelationCreditAt
  exact intervalIntegral.integral_nonneg hQ fun q hq =>
    W.signedFifthCorrelationCreditIntegrand_nonneg q

theorem QuarticFourSignedPolePair.signedFifthCorrelationDebtAt_nonneg
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hQ : quarticSignedPoleCanonicalLocalRadius <= (n : ℝ)/(t/16)) :
    0 <= W.signedFifthCorrelationDebtAt n := by
  unfold QuarticFourSignedPolePair.signedFifthCorrelationDebtAt
  exact intervalIntegral.integral_nonneg hQ fun q hq =>
    W.signedFifthCorrelationDebtIntegrand_nonneg q

/-- Finite producer-facing Route-B condition in explicit correlation
coordinates. -/
theorem QuarticFourSignedPolePair.signedFifthCapInterior_lower_of_credit_debt
    {t EV eps : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (n : ℕ)
    (hn : quarticSignedPoleCanonicalPhysicalHalfWidth t <= (n : ℝ))
    (hcorrelation :
      W.signedFifthCorrelationDebtAt n
        - W.outerVerticalAbsoluteBudget rho EV + 3*eps
        <= W.signedFifthCorrelationCreditAt n) :
    -W.outerVerticalAbsoluteBudget rho EV + 3*eps
      <= W.signedFifthPhysicalCapInteriorAt n := by
  rw [W.signedFifthPhysicalCapInteriorAt_eq_credit_sub_debt ht n hn]
  linarith

/-- The exact Route-B scalar from the max-cut roadmap.

`gap >= 0` is definitionally the same analytic statement as

  Credit_n - Debt_n + OuterBudget - 3 eps >= 0.

Naming this scalar avoids further representation work: the only unpaid Route-B
input is now eventual nonnegativity of this exact quantity. -/
def QuarticFourSignedPolePair.signedFifthCorrelationGapAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV eps : ℝ) (n : ℕ) : ℝ :=
  W.signedFifthCorrelationCreditAt n
    - W.signedFifthCorrelationDebtAt n
    + W.outerVerticalAbsoluteBudget rho EV
    - 3*eps

theorem QuarticFourSignedPolePair.signedFifthCorrelationGapAt_nonneg_iff
    {t EV eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (n : ℕ) :
    0 <= W.signedFifthCorrelationGapAt rho EV eps n
      ↔
    W.signedFifthCorrelationDebtAt n
        - W.outerVerticalAbsoluteBudget rho EV + 3*eps
      <= W.signedFifthCorrelationCreditAt n := by
  unfold QuarticFourSignedPolePair.signedFifthCorrelationGapAt
  constructor <;> intro h <;> linarith

/-- Eventual `G_n >= 0` is exactly sufficient for the existing signed-fifth
interior target.  This is the terminal Route-B producer interface; no new
credit/debt wrapper is required beyond this point. -/
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
  filter_upwards [hlarge,hgap] with n hn hg
  exact W.signedFifthCapInterior_lower_of_credit_debt
    ht rho n hn
    ((W.signedFifthCorrelationGapAt_nonneg_iff rho n).mp hg)

/-- Eventual correlation inequality is exactly sufficient for the existing
signed-fifth interior target. -/
theorem QuarticFourSignedPolePair.signedFifthInteriorTarget_of_eventual_credit_ge_debt_plus_threshold
    {t EV eps : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (hlarge :
      ∀ᶠ n : ℕ in atTop,
        quarticSignedPoleCanonicalPhysicalHalfWidth t <= (n : ℝ))
    (hcorr :
      ∀ᶠ n : ℕ in atTop,
        W.signedFifthCorrelationDebtAt n
          - W.outerVerticalAbsoluteBudget rho EV + 3*eps
          <= W.signedFifthCorrelationCreditAt n) :
    W.SignedFifthInteriorTarget rho EV eps := by
  filter_upwards [hlarge,hcorr] with n hn hc
  exact W.signedFifthCapInterior_lower_of_credit_debt
    ht rho n hn hc

end Synthesis