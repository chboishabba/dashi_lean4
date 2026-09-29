import Synthesis.RiemannQuarticFourthPrimitiveQuantitativeBudget
import Synthesis.RiemannZetaMuExactAbel

/-!
# Positive-ordinate classical RvM remainder for the quartic cap

On 0 <= A <= B the exact literal discrepancy satisfies

  D(A,B) = S0(B) - S0(A),

where S0(T) := Ncount(0,T) - integral_0^T mu.

The positive-endpoint hypothesis is essential.  The fourth physical cap
eventually crosses t-s=0 when s>t; this lemma does not silently treat negative
endpoints as classical positive-ordinate S(T).

The proof is unconditional and uses the actual Zeta23 window and mu.
-/

noncomputable section

open MeasureTheory Set
open scoped Real

namespace Synthesis

def zetaMuPositiveOrdinateRemainder (T : ℝ) : ℝ :=
  zetaMuCumulativeDiscrepancy 0 T

theorem zetaMuWindowDiscrepancy_eq_positiveRemainder_sub
    {A B : ℝ}
    (hA : 0 <= A)
    (hAB : A <= B) :
    zetaMuCumulativeDiscrepancy A B
      =
    zetaMuPositiveOrdinateRemainder B
      - zetaMuPositiveOrdinateRemainder A := by
  have hcount :=
    Zeta23.Ncount_add
      (a := (0 : ℝ)) (b := A) (c := B) hA hAB
  have hint : ∀ a b : ℝ,
      IntervalIntegrable Zeta23.mu volume a b :=
    fun a b => Zeta23.gammaFacts.smooth.continuous.intervalIntegrable a b
  have hmu :=
    intervalIntegral.integral_add_adjacent_intervals
      (hint 0 A) (hint A B)
  unfold zetaMuPositiveOrdinateRemainder
    zetaMuCumulativeDiscrepancy zetaMuPrimitive
  have hcountR :
      (Ncount 0 B : ℝ)
        =
      (Ncount 0 A : ℝ) + (Ncount A B : ℝ) := by
    exact_mod_cast hcount
  rw [hcountR,hmu]
  ring

/-- The physical cap uses the difference of TWO classical counting
remainders, not just one S(t) term.  This distinction matters for every
attempt to import estimates on integrated S_n. -/
theorem QuarticFourSignedPolePair.physicalFourthPrimitive_eq_positiveRemainderDifference
    {t Q : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hQ : quarticSignedPoleCanonicalLocalRadius <= Q)
    (hwithin : (t/16)*Q <= t) :
    W.outerSymmetricDiscrepancyFourthPhysicalPrimitive Q
      =
    ∫ s in
      ((t/16)*quarticSignedPoleCanonicalLocalRadius)..((t/16)*Q),
      (((t/16)*Q-s)^3/6)
        * (zetaMuPositiveOrdinateRemainder (t+s)
            - zetaMuPositiveOrdinateRemainder (t-s)) := by
  let r : ℝ := t/16
  have hr : 0 < r := by dsimp [r]; positivity
  have hle : r*quarticSignedPoleCanonicalLocalRadius <= r*Q :=
    mul_le_mul_of_nonneg_left hQ hr.le
  unfold QuarticFourSignedPolePair.outerSymmetricDiscrepancyFourthPhysicalPrimitive
  dsimp [r]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le hle] at hs
  have hs0 : 0 <= s := by
    have heta := quarticSignedPoleCanonicalLocalRadius_pos
    nlinarith [hs.1]
  have hsmax : s <= t := le_trans hs.2 hwithin
  rw [zetaMuWindowDiscrepancy_eq_positiveRemainder_sub
    (by linarith : 0 <= t-s)
    (by linarith : t-s <= t+s)]
  rfl

end Synthesis
