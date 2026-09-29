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

open MeasureTheory Complex Set
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


/-- At good positive heights the exact difference of classical counting
remainders is the zeta-only half-contour, with the Gamma density already
cancelled.  No RH input is used. -/
theorem zetaMuPositiveOrdinateRemainder_sub_eq_zetaHalfContour
    {A B : ℝ}
    (hA : 1 <= A)
    (hAB : A < B)
    (hgA : Zeta23.RvM.GoodHeight A)
    (hgB : Zeta23.RvM.GoodHeight B) :
    zetaMuPositiveOrdinateRemainder B
      - zetaMuPositiveOrdinateRemainder A
      =
    (1/Real.pi) *
      (Zeta23.RvM.halfContour
        (logDeriv riemannZeta) A B).im := by
  have hwindow :=
    zetaMuWindowDiscrepancy_eq_zetaHalfContour
      hA hAB hgA hgB
  have hdelta :=
    zetaMuWindowDiscrepancy_eq_positiveRemainder_sub
      (by linarith : 0 <= A) hAB.le
  rw [zetaMuCumulativeDiscrepancy_endpoint] at hdelta
  exact hdelta.symm.trans hwindow


/-- Exact additivity of the *same* atomic counting discrepancy and the mu
integral at an arbitrary intermediate ordinate. -/
theorem zetaMuCumulativeDiscrepancy_add
    {A B C : ℝ}
    (hAB : A <= B)
    (hBC : B <= C) :
    zetaMuCumulativeDiscrepancy A C
      =
    zetaMuCumulativeDiscrepancy A B
      + zetaMuCumulativeDiscrepancy B C := by
  have hn :=
    Zeta23.Ncount_add (a:=A) (b:=B) (c:=C) hAB hBC
  have hnR :
      (Ncount A C : ℝ)
        = (Ncount A B : ℝ) + (Ncount B C : ℝ) := by
    exact_mod_cast hn
  have hmu : ∀ a b : ℝ,
      IntervalIntegrable Zeta23.mu volume a b :=
    fun a b => Zeta23.gammaFacts.smooth.continuous.intervalIntegrable a b
  have hi :=
    intervalIntegral.integral_add_adjacent_intervals
      (hmu A B) (hmu B C)
  unfold zetaMuCumulativeDiscrepancy zetaMuPrimitive
  rw [hnR,hi]
  ring

/-- A two-sided remainder which is defined even when the symmetric window
crosses ordinate zero.  The negative-side term is not discarded. -/
def zetaMuFullSymmetricRemainder (t s : ℝ) : ℝ :=
  if s <= t then
    zetaMuPositiveOrdinateRemainder (t+s)
      - zetaMuPositiveOrdinateRemainder (t-s)
  else
    zetaMuCumulativeDiscrepancy (t-s) 0
      + zetaMuPositiveOrdinateRemainder (t+s)

theorem zetaMuSymmetricDiscrepancy_eq_fullRemainder
    {t s : ℝ}
    (ht : 0 <= t)
    (hs : 0 <= s) :
    zetaMuCumulativeDiscrepancy (t-s) (t+s)
      =
    zetaMuFullSymmetricRemainder t s := by
  unfold zetaMuFullSymmetricRemainder
  split_ifs with hst
  · exact zetaMuWindowDiscrepancy_eq_positiveRemainder_sub
      (by linarith) (by linarith)
  · have hleft : t-s <= 0 := by linarith
    have hright : 0 <= t+s := by linarith
    rw [zetaMuCumulativeDiscrepancy_add hleft hright]
    rfl

/-- Full positive-and-negative-ordinate version.  No cutoff condition
r*Q <= t is required; the negative window is retained literally. -/
theorem QuarticFourSignedPolePair.physicalFourthPrimitive_eq_fullSymmetricRemainder
    {t Q : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hQ : quarticSignedPoleCanonicalLocalRadius <= Q) :
    W.outerSymmetricDiscrepancyFourthPhysicalPrimitive Q
      =
    ∫ s in
      ((t/16)*quarticSignedPoleCanonicalLocalRadius)..((t/16)*Q),
      (((t/16)*Q-s)^3/6) * zetaMuFullSymmetricRemainder t s := by
  let r : ℝ := t/16
  have hr : 0 < r := by dsimp [r]; positivity
  have hle : r*quarticSignedPoleCanonicalLocalRadius <= r*Q :=
    mul_le_mul_of_nonneg_left hQ hr.le
  unfold QuarticFourSignedPolePair.outerSymmetricDiscrepancyFourthPhysicalPrimitive
  dsimp [r]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le hle] at hs
  have hs0 : 0 <= s :=
    (mul_nonneg hr.le quarticSignedPoleCanonicalLocalRadius_pos.le).trans hs.1
  rw [zetaMuSymmetricDiscrepancy_eq_fullRemainder ht.le hs0]


/-- The actual signed fifth-kernel pairing, with no anonymous fourth
primitive: its inner integrand is the literal full-range RvM remainder,
including negative ordinates when q>16. -/
theorem QuarticFourSignedPolePair.signedFifthCapInterior_eq_twoSidedRemainder
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hn : quarticSignedPoleCanonicalPhysicalHalfWidth t <= (n : ℝ)) :
    W.signedFifthPhysicalCapInteriorAt n
      =
    ∫ q in quarticSignedPoleCanonicalLocalRadius..((n : ℝ)/(t/16)),
      compactCosineD5
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t) q
      *
      (∫ s in
        ((t/16)*quarticSignedPoleCanonicalLocalRadius)..((t/16)*q),
        (((t/16)*q-s)^3/6) *
          zetaMuFullSymmetricRemainder t s) := by
  have hr : 0 < t/16 := by positivity
  have hQ :
      quarticSignedPoleCanonicalLocalRadius <= (n : ℝ)/(t/16) := by
    rw [le_div_iff₀ hr]
    exact hn
  unfold QuarticFourSignedPolePair.signedFifthPhysicalCapInteriorAt
  apply intervalIntegral.integral_congr
  intro q hq
  rw [Set.uIcc_of_le hQ] at hq
  rw [W.anchoredFourth_eq_physicalFourthPrimitive ht hq.1,
    W.physicalFourthPrimitive_eq_fullSymmetricRemainder ht hq.1]

end Synthesis
