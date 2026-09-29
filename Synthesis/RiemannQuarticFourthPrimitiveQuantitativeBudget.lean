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

end Synthesis
