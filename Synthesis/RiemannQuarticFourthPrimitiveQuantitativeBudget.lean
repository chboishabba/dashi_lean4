import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleFourierTerminal

/-!
# Quantitative fourth-primitive RH budget

The fourfold integration-by-parts identity is an identity, not an r^-4 bound.
This owner calculates the exact terminal budget that any unconditional primitive
estimate must satisfy, with the physical horizontal and literal-local
corrections retained on the SAME witness.

Let r=t/16, eta=the canonical radius, and

  I_n = normalizedOuterPairedAbelAt n
      = integral_[eta,n/r] C'_W(q) r^4 D(t-rq,t+rq) dq.

The finite terminal scalar is -I_n/2 + H6 - L6.  Thus an ABSOLUTE
bound |I_n| <= E_n + B*K entails the desired terminal cut only when

  E_n + B*K < 2 * (r^6 * terminalMargin - H6 + L6).

No estimate for B is assumed/proved by these arithmetic identities.  The
original signed condition can be weaker and remains the preferred alternative
if this absolute margin is negative or too small.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real

namespace Synthesis

def QuarticFourSignedPolePair.outerVerticalAbsoluteBudget
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV : ℝ) : ℝ :=
  2 * (
    (t/16)^6 * W.postSixthTerminalResidualMargin rho EV
      - W.quarticScaleHorizontalRemainder
      + W.quarticScaleCanonicalLocalCorrection
  )

theorem QuarticFourSignedPolePair.outerVerticalAbsoluteBudget_eq
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV : ℝ) :
    W.outerVerticalAbsoluteBudget rho EV
      =
    2 * (t/16)^6 * W.postSixthTerminalResidualMargin rho EV
      - 2 * W.quarticScaleHorizontalRemainder
      + 2 * W.quarticScaleCanonicalLocalCorrection := by
  unfold QuarticFourSignedPolePair.outerVerticalAbsoluteBudget
  ring

theorem QuarticFourSignedPolePair.outerTerminal_lt_of_absoluteAbel_budget
    {t EV E n : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (k : ℕ)
    (hAbel : |W.normalizedOuterPairedAbelAt k| <= E)
    (hBudget : E < W.outerVerticalAbsoluteBudget rho EV) :
    W.quarticScaleOuterTerminalAt k
      < (t/16)^6 * W.postSixthTerminalResidualMargin rho EV := by
  unfold QuarticFourSignedPolePair.quarticScaleOuterTerminalAt
    QuarticFourSignedPolePair.quarticScaleOuterPairedHorizontalAt
    QuarticFourSignedPolePair.outerVerticalAbsoluteBudget at *
  have hlower := (abs_le.mp hAbel).1
  linarith

theorem QuarticFourSignedPolePair.absolutePrimitiveCost_strictBudget
    {t BP K boundary : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV : ℝ)
    (hBudget :
      boundary + BP*K < W.outerVerticalAbsoluteBudget rho EV) :
    (1/2 : ℝ) * (boundary + BP*K)
      + W.quarticScaleHorizontalRemainder
      - W.quarticScaleCanonicalLocalCorrection
      < (t/16)^6 * W.postSixthTerminalResidualMargin rho EV := by
  unfold QuarticFourSignedPolePair.outerVerticalAbsoluteBudget at hBudget
  linarith

/-- The maximal admissible *product* is well-defined without division by
an L1 mass that might vanish. The strict inequality is the actual condition,
not a standalone B4 estimate. -/
def QuarticFourSignedPolePair.absolutePrimitiveAdmissibleProduct
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV : ℝ)
    (BP K : ℝ) : Prop :=
  BP*K < W.outerVerticalAbsoluteBudget rho EV

theorem QuarticFourSignedPolePair.absolutePrimitiveAdmissibleProduct_iff
    {t BP K : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV : ℝ) :
    W.absolutePrimitiveAdmissibleProduct rho EV BP K
      ↔
    (1/2 : ℝ) * BP*K
      + W.quarticScaleHorizontalRemainder
      - W.quarticScaleCanonicalLocalCorrection
        < (t/16)^6 * W.postSixthTerminalResidualMargin rho EV := by
  unfold QuarticFourSignedPolePair.absolutePrimitiveAdmissibleProduct
    QuarticFourSignedPolePair.outerVerticalAbsoluteBudget
  constructor <;> intro h <;> linarith

/-- When the fifth-derivative mass is strictly positive, the admissible
coefficient is exactly the budget divided by that SAME kernel norm. -/
theorem QuarticFourSignedPolePair.absolutePrimitiveCoefficient_lt_iff
    {t BP K : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV : ℝ)
    (hK : 0 < K) :
    W.absolutePrimitiveAdmissibleProduct rho EV BP K
      ↔ BP < W.outerVerticalAbsoluteBudget rho EV / K := by
  unfold QuarticFourSignedPolePair.absolutePrimitiveAdmissibleProduct
  exact (lt_div_iff₀ hK).symm

/-- A bound that is already too large at the scalar budget cannot be rescued
by simply recasting it as a polynomial-growth primitive interface. -/
theorem QuarticFourSignedPolePair.absoluteBudget_failfast
    {t BP K : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV : ℝ)
    (hTooLarge : W.outerVerticalAbsoluteBudget rho EV <= BP*K) :
    ¬ W.absolutePrimitiveAdmissibleProduct rho EV BP K := by
  unfold QuarticFourSignedPolePair.absolutePrimitiveAdmissibleProduct
  exact not_lt.mpr hTooLarge


/-!
## Polynomial-growth primitive versus weighted fifth-kernel norm

This is the useful non-uniform interface.  The analytic assumption is a
bound on the ACTUAL anchored/physical fourth primitive.  The fifth-derivative
integrability is recorded separately as a weighted kernel envelope.

It is important that the coefficient BP remains height-dependent in any
future RvM estimate: no quartic-scale saving is inferred from the growth
degree alone.
-/

def QuarticFourSignedPolePair.OuterFourthPrimitivePolynomialBound
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) (BP : ℝ) : Prop :=
  ∀ q : ℝ, quarticSignedPoleCanonicalLocalRadius <= q ->
    |anchoredPrimitive4
      W.quarticScaleSymmetricWindowDiscrepancy
      quarticSignedPoleCanonicalLocalRadius q|
      <= BP * (1 + q^5)

def QuarticFourSignedPolePair.FifthDerivativeWeightedOuterEnvelope
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) (K : ℝ) : Prop :=
  ∀ Q : ℝ, quarticSignedPoleCanonicalLocalRadius <= Q ->
    (∫ q in quarticSignedPoleCanonicalLocalRadius..Q,
      (1 + q^5)
        * |compactCosineD5
           (quarticFourSignedPoleCombinedProfile
             W.R W.muHalf W.muTwo t) q|)
      <= K

theorem QuarticFourSignedPolePair.weightedFifthInterior_abs_le_primitiveCost
    {t BP K Q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hQ : quarticSignedPoleCanonicalLocalRadius <= Q)
    (hBP : 0 <= BP)
    (hPrimitive : W.OuterFourthPrimitivePolynomialBound BP)
    (hWeighted : W.FifthDerivativeWeightedOuterEnvelope K) :
    |
      ∫ q in quarticSignedPoleCanonicalLocalRadius..Q,
        compactCosineD5
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t) q
          *
        anchoredPrimitive4
          W.quarticScaleSymmetricWindowDiscrepancy
          quarticSignedPoleCanonicalLocalRadius q
    | <= BP*K := by
  let P : ℝ -> ℝ :=
    quarticFourSignedPoleCombinedProfile W.R W.muHalf W.muTwo t
  let A : ℝ -> ℝ := W.quarticScaleSymmetricWindowDiscrepancy
  let P4 : ℝ -> ℝ :=
    anchoredPrimitive4 A quarticSignedPoleCanonicalLocalRadius
  have hPcont : Continuous P :=
    quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P :=
    quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have hC5cont : Continuous (compactCosineD5 P) :=
    compactCosineD5_continuous hPcont hPc
  have hAint :
      IntervalIntegrable A volume
        quarticSignedPoleCanonicalLocalRadius Q :=
    W.quarticScaleSymmetricWindowDiscrepancy_intervalIntegrable hQ
  obtain ⟨_,_,_,hP4ac⟩ := anchoredPrimitive_ladder_ac hAint
  have hP4cont :
      ContinuousOn P4 (Set.uIcc quarticSignedPoleCanonicalLocalRadius Q) :=
    hP4ac.continuousOn
  have hproduct :
      IntervalIntegrable
        (fun q => compactCosineD5 P q * P4 q)
        volume quarticSignedPoleCanonicalLocalRadius Q :=
    (hC5cont.continuousOn.mul hP4cont).intervalIntegrable
  have hweight :
      IntervalIntegrable
        (fun q => (1+q^5)*|compactCosineD5 P q|)
        volume quarticSignedPoleCanonicalLocalRadius Q := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hmajor :
      IntervalIntegrable
        (fun q => BP*((1+q^5)*|compactCosineD5 P q|))
        volume quarticSignedPoleCanonicalLocalRadius Q :=
    hweight.const_mul BP
  have hraw :
      |
        ∫ q in quarticSignedPoleCanonicalLocalRadius..Q,
          compactCosineD5 P q * P4 q
      | <=
      BP *
        (∫ q in quarticSignedPoleCanonicalLocalRadius..Q,
          (1+q^5)*|compactCosineD5 P q|) := by
    calc
      |
        ∫ q in quarticSignedPoleCanonicalLocalRadius..Q,
          compactCosineD5 P q * P4 q
      |
        <= ∫ q in quarticSignedPoleCanonicalLocalRadius..Q,
          |compactCosineD5 P q * P4 q| :=
          intervalIntegral.abs_integral_le_integral_abs hQ
      _ <= ∫ q in quarticSignedPoleCanonicalLocalRadius..Q,
          BP*((1+q^5)*|compactCosineD5 P q|) := by
        apply intervalIntegral.integral_mono_on
          hQ hproduct.abs hmajor
        intro q hq
        rw [abs_mul]
        have hqEta :
            quarticSignedPoleCanonicalLocalRadius <= q := hq.1
        have hbound := hPrimitive q hqEta
        have hbase : 0 <= (1+q^5) := by
          have heta : 0 < quarticSignedPoleCanonicalLocalRadius :=
            quarticSignedPoleCanonicalLocalRadius_pos
          have hq0 : 0 <= q := heta.le.trans hqEta
          positivity
        calc
          |compactCosineD5 P q| * |P4 q|
            <= |compactCosineD5 P q| * (BP*(1+q^5)) :=
              mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
          _ = BP*((1+q^5)*|compactCosineD5 P q|) := by ring
      _ =
          BP *
          (∫ q in quarticSignedPoleCanonicalLocalRadius..Q,
            (1+q^5)*|compactCosineD5 P q|) := by
            rw [intervalIntegral.integral_const_mul]
  have hbound := hWeighted Q hQ
  exact hraw.trans (mul_le_mul_of_nonneg_left hbound hBP)

theorem QuarticFourSignedPolePair.weightedOuterAbel_abs_le_boundary_add_cost
    {t BP K : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hBP : 0 <= BP)
    (hPrimitive : W.OuterFourthPrimitivePolynomialBound BP)
    (hWeighted : W.FifthDerivativeWeightedOuterEnvelope K)
    (n : ℕ)
    (hn : quarticSignedPoleCanonicalPhysicalHalfWidth t <= (n : ℝ))
    (hA :
      IntervalIntegrable
        W.quarticScaleSymmetricWindowDiscrepancy volume
        quarticSignedPoleCanonicalLocalRadius ((n : ℝ)/(t/16))) :
    |W.normalizedOuterPairedAbelAt n|
      <=
      |fourfoldIBPUpperBoundary
        W.normalizedOrdinateCosineD1
        (compactCosineD2
          (quarticFourSignedPoleCombinedProfile W.R W.muHalf W.muTwo t))
        (compactCosineD3
          (quarticFourSignedPoleCombinedProfile W.R W.muHalf W.muTwo t))
        (compactCosineD4
          (quarticFourSignedPoleCombinedProfile W.R W.muHalf W.muTwo t))
        (anchoredPrimitive1 W.quarticScaleSymmetricWindowDiscrepancy
          quarticSignedPoleCanonicalLocalRadius)
        (anchoredPrimitive2 W.quarticScaleSymmetricWindowDiscrepancy
          quarticSignedPoleCanonicalLocalRadius)
        (anchoredPrimitive3 W.quarticScaleSymmetricWindowDiscrepancy
          quarticSignedPoleCanonicalLocalRadius)
        (anchoredPrimitive4 W.quarticScaleSymmetricWindowDiscrepancy
          quarticSignedPoleCanonicalLocalRadius)
        ((n : ℝ)/(t/16))|
      + BP*K := by
  rw [W.normalizedOuterPairedAbelAt_eq_upperBoundary_add_fifthInterior
    ht n hn hA]
  have hQ : quarticSignedPoleCanonicalLocalRadius <= (n : ℝ)/(t/16) := by
    rw [le_div_iff₀ (by positivity : 0 < t/16)]
    exact hn
  have hinner := W.weightedFifthInterior_abs_le_primitiveCost
    hQ hBP hPrimitive hWeighted
  exact (abs_add _ _).trans (add_le_add_left hinner _)


/-!
## Absolute RvM comparison: fourfold smoothing does not produce r^-4

The following exact scalar bound is intentionally unconditional with respect
to any *given* pointwise envelope E for a finite interval.  It proves that
four primitives transfer the r^4 coefficient into the physical primitive's
size: the affine identity alone is not an analytic saving.
-/

theorem cubicCesaro_abs_le_of_discrepancy_envelope
    {a Q E : ℝ}
    {A : ℝ -> ℝ}
    (haQ : a <= Q)
    (hE : 0 <= E)
    (hAI : IntervalIntegrable
      (fun q : ℝ => ((Q-q)^3 / 6) * A q) volume a Q)
    (hAbound : ∀ q ∈ Set.Icc a Q, |A q| <= E) :
    |∫ q in a..Q, ((Q-q)^3 / 6) * A q|
      <= E * (Q-a)^4 / 24 := by
  let w : ℝ -> ℝ := fun q => (Q-q)^3 / 6
  have hwcont : Continuous w := by
    dsimp [w]
    fun_prop
  have hwint : IntervalIntegrable w volume a Q :=
    hwcont.intervalIntegrable a Q
  have hmajor :
      IntervalIntegrable (fun q => E*w q) volume a Q :=
    hwint.const_mul E
  have hweight :
      (∫ q in a..Q, w q) = (Q-a)^4 / 24 := by
    let F : ℝ -> ℝ := fun q => -(Q-q)^4 / 24
    have hderiv :
        ∀ q ∈ Set.uIcc a Q, HasDerivAt F (w q) q := by
      intro q hq
      have hraw :
          HasDerivAt F
            (-(4*(Q-q)^3*(-1))/24) q := by
        dsimp [F]
        fun_prop
      convert hraw using 1 <;> dsimp [w] <;> ring
    have hint :
        IntervalIntegrable w volume a Q := hwint
    have hFTC :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    dsimp [F,w] at hFTC ⊢
    rw [hFTC]
    ring
  have hineq :
      (∫ q in a..Q, |w q * A q|)
        <= (∫ q in a..Q, E*w q) := by
    apply intervalIntegral.integral_mono_on
      haQ hAI.abs hmajor
    intro q hq
    have hqQ : q <= Q := hq.2
    have hwpos : 0 <= w q := by
      dsimp [w]
      have hdiff : 0 <= Q-q := by linarith
      positivity
    rw [abs_mul,abs_of_nonneg hwpos]
    have hbound := hAbound q hq
    calc
      w q * |A q| <= w q * E :=
        mul_le_mul_of_nonneg_left hbound hwpos
      _ = E*w q := by ring
  calc
    |∫ q in a..Q, ((Q-q)^3/6)*A q|
      <= ∫ q in a..Q, |w q * A q| := by
        dsimp [w]
        exact intervalIntegral.abs_integral_le_integral_abs haQ
    _ <= ∫ q in a..Q, E*w q := hineq
    _ = E*(Q-a)^4/24 := by
      rw [intervalIntegral.integral_const_mul, hweight]
      ring

theorem QuarticFourSignedPolePair.fourthPrimitive_abs_le_from_absoluteRvM
    {t Q E : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hQ : quarticSignedPoleCanonicalLocalRadius <= Q)
    (hE : 0 <= E)
    (hD : ∀ q ∈
      Set.Icc quarticSignedPoleCanonicalLocalRadius Q,
      |zetaMuCumulativeDiscrepancy
        (t-(t/16)*q) (t+(t/16)*q)| <= E) :
    |W.outerSymmetricDiscrepancyFourthPhysicalPrimitive Q|
      <=
    (t/16)^4 * E
      * (Q-quarticSignedPoleCanonicalLocalRadius)^4 / 24 := by
  have hA :
      IntervalIntegrable
        W.quarticScaleSymmetricWindowDiscrepancy volume
        quarticSignedPoleCanonicalLocalRadius Q :=
    W.quarticScaleSymmetricWindowDiscrepancy_intervalIntegrable hQ
  have hprod :
      IntervalIntegrable
        (fun q : ℝ =>
          ((Q-q)^3/6)
          * W.quarticScaleSymmetricWindowDiscrepancy q)
        volume quarticSignedPoleCanonicalLocalRadius Q := by
    have hw : Continuous (fun q : ℝ => (Q-q)^3/6) := by
      fun_prop
    exact hA.mul_continuousOn hw.continuousOn
  have hr4 : 0 <= (t/16)^4 := by positivity
  have hbound :
      ∀ q ∈ Set.Icc quarticSignedPoleCanonicalLocalRadius Q,
        |W.quarticScaleSymmetricWindowDiscrepancy q|
          <= (t/16)^4 * E := by
    intro q hq
    unfold QuarticFourSignedPolePair.quarticScaleSymmetricWindowDiscrepancy
    rw [abs_mul, abs_of_nonneg hr4]
    exact mul_le_mul_of_nonneg_left (hD q hq) hr4
  have hraw :=
    cubicCesaro_abs_le_of_discrepancy_envelope
      hQ (mul_nonneg hr4 hE) hprod hbound
  rw [← W.outerSymmetricDiscrepancyFourthPrimitive_eq_physical ht]
  unfold QuarticFourSignedPolePair.outerSymmetricDiscrepancyFourthPrimitive
  exact hraw


/-!
## One-sided alternative, on the literal outer terminal carrier

A crucial sign that should not be hidden by absolute values:

  T_n = -I_n/2 + H6 - L6,
  T_n < r^6 M  <->  -budget < I_n.

Thus the exact analytic target for the selected witness is a LOWER bound
on the signed outer Abel integral, not an upper bound on its absolute value.
When budget <= 0, the absolute route has no nonnegative cost that fits,
but the signed route remains logically available.
-/

theorem QuarticFourSignedPolePair.outerTerminal_lt_iff_signedAbel_gt_negBudget
    {t EV : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (n : ℕ) :
    W.quarticScaleOuterTerminalAt n
      < (t/16)^6 * W.postSixthTerminalResidualMargin rho EV
    ↔
    - W.outerVerticalAbsoluteBudget rho EV
      < W.normalizedOuterPairedAbelAt n := by
  unfold QuarticFourSignedPolePair.quarticScaleOuterTerminalAt
    QuarticFourSignedPolePair.quarticScaleOuterPairedHorizontalAt
    QuarticFourSignedPolePair.outerVerticalAbsoluteBudget
  constructor <;> intro h <;> linarith

theorem QuarticFourSignedPolePair.nonpos_budget_blocks_nonnegative_absolute_cost
    {t EV BP K : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (hBudget : W.outerVerticalAbsoluteBudget rho EV <= 0)
    (hBP : 0 <= BP)
    (hK : 0 <= K) :
    ¬ W.absolutePrimitiveAdmissibleProduct rho EV BP K := by
  apply W.absoluteBudget_failfast
  exact hBudget.trans (mul_nonneg hBP hK)

theorem QuarticFourSignedPolePair.positive_budget_iff_heightDefect_exceeds_cost
    {t EV : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    0 < W.outerVerticalAbsoluteBudget rho EV
    ↔
    W.quarticScaleHorizontalRemainder
      - W.quarticScaleCanonicalLocalCorrection
      <
    (t/16)^6 * W.postSixthTerminalResidualMargin rho EV := by
  unfold QuarticFourSignedPolePair.outerVerticalAbsoluteBudget
  constructor <;> intro h <;> linarith

theorem QuarticFourSignedPolePair.nonpos_budget_iff_heightDefect_below_cost
    {t EV : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.outerVerticalAbsoluteBudget rho EV <= 0
    ↔
    (t/16)^6 * W.postSixthTerminalResidualMargin rho EV
      <=
    W.quarticScaleHorizontalRemainder
      - W.quarticScaleCanonicalLocalCorrection := by
  unfold QuarticFourSignedPolePair.outerVerticalAbsoluteBudget
  constructor <;> intro h <;> linarith

theorem QuarticFourSignedPolePair.outerTerminal_eventually_iff_signedAbel_eventually
    {t EV eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    (∀ᶠ n : ℕ in atTop,
      W.quarticScaleOuterTerminalAt n
        <= (t/16)^6 * W.postSixthTerminalResidualMargin rho EV - eps)
    ↔
    (∀ᶠ n : ℕ in atTop,
      - W.outerVerticalAbsoluteBudget rho EV + 2*eps
        <= W.normalizedOuterPairedAbelAt n) := by
  apply Filter.eventually_congr
  filter_upwards with n
  unfold QuarticFourSignedPolePair.quarticScaleOuterTerminalAt
    QuarticFourSignedPolePair.quarticScaleOuterPairedHorizontalAt
    QuarticFourSignedPolePair.outerVerticalAbsoluteBudget
  constructor <;> intro h <;> linarith

theorem QuarticFourSignedPolePair.signedAbelPositiveSlack_iff_terminalCut
    {t EV : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.QuarticScaleOuterTerminalEventuallyBelowMargin rho EV
      ↔
    ∃ eps : ℝ, 0 < eps ∧
      ∀ᶠ n : ℕ in atTop,
        - W.outerVerticalAbsoluteBudget rho EV + 2*eps
          <= W.normalizedOuterPairedAbelAt n := by
  unfold QuarticFourSignedPolePair.QuarticScaleOuterTerminalEventuallyBelowMargin
  constructor
  · rintro ⟨eps,heps,hev⟩
    exact ⟨eps,heps,
      (W.outerTerminal_eventually_iff_signedAbel_eventually rho).1 hev⟩
  · rintro ⟨eps,heps,hev⟩
    exact ⟨eps,heps,
      (W.outerTerminal_eventually_iff_signedAbel_eventually rho).2 hev⟩


/-!
## Automatic weighted C5 norm from the existing Schwartz rapid decay

The integrable-power theorem in Mathlib's Schwartz-space library gives
integrability of |q|^5 |C5(q)| from the m=0 and
m=5+volume.integrablePower rapid-decay estimates. This produces a concrete
weighted norm, not a new analytic assumption.
-/

theorem compactCosineD5_weighted_abs_integrable
    {P : ℝ -> ℝ}
    (hPc : HasCompactSupport P)
    (hPs : ContDiff ℝ (⊤ : ℕ∞) P) :
    Integrable (fun q : ℝ =>
      (1 + |q|^5) * |compactCosineD5 P q|) := by
  have hcont : Continuous (compactCosineD5 P) :=
    compactCosineD5_continuous hPs.continuous hPc
  obtain ⟨C0,hC0,hdec0⟩ :=
    compactCosineD5_rapid_decay hPc hPs 0
  obtain ⟨Cw,hCw,hdecw⟩ :=
    compactCosineD5_rapid_decay hPc hPs
      (5 + (volume : Measure ℝ).integrablePower)
  have hw :
      Integrable (fun q : ℝ =>
        ‖q‖^5 * ‖compactCosineD5 P q‖) := by
    apply SchwartzMap.integrable_of_le_of_pow_mul_le
      (C₁:=C0) (C₂:=Cw)
    · intro q
      simpa [Real.norm_eq_abs] using hdec0 q
    · intro q
      simpa [Real.norm_eq_abs] using hdecw q
    · exact hcont.aestronglyMeasurable
  have hC5 :
      Integrable (fun q : ℝ => |compactCosineD5 P q|) :=
    (compactCosineD5_integrable (hPs.of_le (by simp)) hPc).abs
  have hw' :
      Integrable (fun q : ℝ => |q|^5 * |compactCosineD5 P q|) := by
    simpa [Real.norm_eq_abs] using hw
  have hsum := hC5.add hw'
  simpa [add_mul] using hsum

def QuarticFourSignedPolePair.fifthDerivativeWeightedGlobalL1Mass
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) : ℝ :=
  ∫ q : ℝ, (1 + |q|^5) *
    |compactCosineD5
      (quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t) q|

theorem QuarticFourSignedPolePair.fifthDerivativeWeightedGlobalL1Mass_nonneg
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 <= W.fifthDerivativeWeightedGlobalL1Mass := by
  unfold QuarticFourSignedPolePair.fifthDerivativeWeightedGlobalL1Mass
  apply integral_nonneg
  intro q
  positivity

theorem QuarticFourSignedPolePair.fifthDerivativeWeightedOuterEnvelope_global
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.FifthDerivativeWeightedOuterEnvelope
      W.fifthDerivativeWeightedGlobalL1Mass := by
  intro Q hQ
  let P : ℝ -> ℝ :=
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t
  have hPs : ContDiff ℝ (⊤ : ℕ∞) P :=
    quarticFourSignedPoleCombinedProfile_contDiff_n W.Rpos ⊤
  have hPc : HasCompactSupport P :=
    quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have hweighted :
      Integrable (fun q : ℝ =>
        (1+|q|^5)*|compactCosineD5 P q|) :=
    compactCosineD5_weighted_abs_integrable hPc hPs
  have hpos : 0 < quarticSignedPoleCanonicalLocalRadius :=
    quarticSignedPoleCanonicalLocalRadius_pos
  have hpoint :
      (∫ q in quarticSignedPoleCanonicalLocalRadius..Q,
        (1+q^5)*|compactCosineD5 P q|)
      =
      ∫ q in quarticSignedPoleCanonicalLocalRadius..Q,
        (1+|q|^5)*|compactCosineD5 P q| := by
    apply intervalIntegral.integral_congr
    intro q hq
    rw [Set.uIcc_of_le hQ] at hq
    rw [abs_of_nonneg (hpos.le.trans hq.1)]
  rw [hpoint, intervalIntegral.integral_of_le hQ]
  unfold QuarticFourSignedPolePair.fifthDerivativeWeightedGlobalL1Mass
  apply setIntegral_mono_set
  · exact hweighted.integrableOn
  · filter_upwards with q
    exact mul_nonneg
      (by positivity : 0 <= 1+|q|^5)
      (abs_nonneg _)
  · exact Filter.Eventually.of_forall fun q hq => Set.mem_univ q

theorem QuarticFourSignedPolePair.weightedFifthInterior_abs_le_physicalGrowth_mul_global
    {t BP Q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hQ : quarticSignedPoleCanonicalLocalRadius <= Q)
    (hBP : 0 <= BP)
    (hPrimitive : W.OuterFourthPrimitivePolynomialBound BP) :
    |
      ∫ q in quarticSignedPoleCanonicalLocalRadius..Q,
        compactCosineD5
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t) q
        * anchoredPrimitive4
          W.quarticScaleSymmetricWindowDiscrepancy
          quarticSignedPoleCanonicalLocalRadius q
    |
    <= BP * W.fifthDerivativeWeightedGlobalL1Mass := by
  exact W.weightedFifthInterior_abs_le_primitiveCost
    hQ hBP hPrimitive W.fifthDerivativeWeightedOuterEnvelope_global


/-!
## Budget sign on the actual off-critical target

The quantitative target theorem proves that combinedZeroHeightDefect rho > 0
for a selected off-line rho, but budget positivity needs *more*:
the quartic target must beat the entire local+horizontal overhead.

Expose this exact equation so future analytic work cannot infer an absolute
margin solely from target-pair positivity.
-/

def QuarticFourSignedPolePair.absoluteFourthPrimitiveOverhead
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) (EV : ℝ) : ℝ :=
  (t/16)^6 * W.postSixthTerminalLocalM6Budget EV
    + 2*W.quarticScaleHorizontalRemainder
    - 2*W.quarticScaleCanonicalLocalCorrection

theorem QuarticFourSignedPolePair.absoluteBudget_eq_targetHeight_minus_overhead
    {t EV : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.outerVerticalAbsoluteBudget rho EV
      =
    4*(t/16)^6 * W.combinedZeroHeightDefect rho
      - W.absoluteFourthPrimitiveOverhead EV := by
  unfold QuarticFourSignedPolePair.outerVerticalAbsoluteBudget
    QuarticFourSignedPolePair.absoluteFourthPrimitiveOverhead
    QuarticFourSignedPolePair.postSixthTerminalResidualMargin
  ring

theorem QuarticFourSignedPolePair.absoluteBudget_pos_iff_overhead_lt_targetHeight
    {t EV : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    0 < W.outerVerticalAbsoluteBudget rho EV
      ↔
    W.absoluteFourthPrimitiveOverhead EV
      < 4*(t/16)^6 * W.combinedZeroHeightDefect rho := by
  rw [W.absoluteBudget_eq_targetHeight_minus_overhead]
  constructor <;> intro h <;> linarith

theorem QuarticFourSignedPolePair.offline_targetHeight_pos_but_absolute_requires_overhead
    {t EV : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hhigh : 8/t < W.quantitativeTargetRadius)
    (rho : Zeros)
    (hoff : heightOf rho ≠ 0) :
    0 < W.combinedZeroHeightDefect rho
    ∧
    (0 < W.outerVerticalAbsoluteBudget rho EV
      ↔ W.absoluteFourthPrimitiveOverhead EV
          < 4*(t/16)^6 * W.combinedZeroHeightDefect rho) := by
  exact ⟨W.combinedZeroHeightDefect_pos_quantitative
      ht hhigh rho hoff,
    W.absoluteBudget_pos_iff_overhead_lt_targetHeight rho⟩


/-!
## Direct signed C5 cap pairing cut

The absolute P4 route can fail while the one-sided integral succeeds.
Keep the exact two surviving pieces of fourfold IBP as separate functions,
without replacing either with a norm.
-/

def QuarticFourSignedPolePair.signedFifthPhysicalCapInteriorAt
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) (n : ℕ) : ℝ :=
  ∫ q in quarticSignedPoleCanonicalLocalRadius..((n : ℝ)/(t/16)),
    compactCosineD5
      (quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t) q
      * anchoredPrimitive4
        W.quarticScaleSymmetricWindowDiscrepancy
        quarticSignedPoleCanonicalLocalRadius q

def QuarticFourSignedPolePair.signedFifthCapUpperBoundaryAt
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) (n : ℕ) : ℝ :=
  fourfoldIBPUpperBoundary
    W.normalizedOrdinateCosineD1
    (compactCosineD2
      (quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t))
    (compactCosineD3
      (quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t))
    (compactCosineD4
      (quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t))
    (anchoredPrimitive1
      W.quarticScaleSymmetricWindowDiscrepancy
      quarticSignedPoleCanonicalLocalRadius)
    (anchoredPrimitive2
      W.quarticScaleSymmetricWindowDiscrepancy
      quarticSignedPoleCanonicalLocalRadius)
    (anchoredPrimitive3
      W.quarticScaleSymmetricWindowDiscrepancy
      quarticSignedPoleCanonicalLocalRadius)
    (anchoredPrimitive4
      W.quarticScaleSymmetricWindowDiscrepancy
      quarticSignedPoleCanonicalLocalRadius)
    ((n : ℝ)/(t/16))

theorem QuarticFourSignedPolePair.signedOuterAbel_eq_boundary_add_fifthCap
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hn : quarticSignedPoleCanonicalPhysicalHalfWidth t <= (n : ℝ)) :
    W.normalizedOuterPairedAbelAt n
      =
    W.signedFifthCapUpperBoundaryAt n
      + W.signedFifthPhysicalCapInteriorAt n := by
  have hQ : quarticSignedPoleCanonicalLocalRadius
      <= (n : ℝ)/(t/16) := by
    rw [le_div_iff₀ (by positivity : 0 < t/16)]
    exact hn
  have hA :
      IntervalIntegrable
        W.quarticScaleSymmetricWindowDiscrepancy volume
        quarticSignedPoleCanonicalLocalRadius ((n : ℝ)/(t/16)) :=
    W.quarticScaleSymmetricWindowDiscrepancy_intervalIntegrable hQ
  exact W.normalizedOuterPairedAbelAt_eq_upperBoundary_add_fifthInterior
    ht n hn hA

theorem QuarticFourSignedPolePair.signedFifthCapLowerBound_closes_finiteTerminal
    {t EV eps : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (n : ℕ)
    (hn : quarticSignedPoleCanonicalPhysicalHalfWidth t <= (n : ℝ))
    (heps : 0 < eps)
    (hboundary :
      |W.signedFifthCapUpperBoundaryAt n| <= eps)
    (hsigned :
      -W.outerVerticalAbsoluteBudget rho EV + 2*eps
        <= W.signedFifthPhysicalCapInteriorAt n) :
    W.quarticScaleOuterTerminalAt n
      <
    (t/16)^6 * W.postSixthTerminalResidualMargin rho EV := by
  have hsum :=
    W.signedOuterAbel_eq_boundary_add_fifthCap ht n hn
  have hbd := (abs_le.mp hboundary).1
  have htarget :
      -W.outerVerticalAbsoluteBudget rho EV
        < W.normalizedOuterPairedAbelAt n := by
    rw [hsum]
    linarith
  exact (W.outerTerminal_lt_iff_signedAbel_gt_negBudget rho n).2 htarget

/-- The signed cap route does not require the absolute budget to be positive:
the fifth-kernel correlation can in principle provide the needed lower
bound even when the absolute sufficient criterion has no headroom. -/
theorem QuarticFourSignedPolePair.signedFifthCapCriterion_no_budget_sign
    {t EV eps : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (n : ℕ)
    (hn : quarticSignedPoleCanonicalPhysicalHalfWidth t <= (n : ℝ))
    (heps : 0 < eps)
    (hboundary : |W.signedFifthCapUpperBoundaryAt n| <= eps)
    (hsigned :
      -W.outerVerticalAbsoluteBudget rho EV + 2*eps
        <= W.signedFifthPhysicalCapInteriorAt n) :
    W.PostSixthCanonicalSignedHighCut rho EV := by
  exact W.signedFifthCapLowerBound_closes_finiteTerminal
    ht rho n hn heps hboundary hsigned

end Synthesis
