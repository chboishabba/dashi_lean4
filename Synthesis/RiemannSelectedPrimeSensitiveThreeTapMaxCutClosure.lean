import Synthesis.RiemannSelectedPrimeSensitiveThreeTapMaxCutDecision
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapJ2SignRegion

/-!
# Exhaustive one-scale three-tap resonance max-cut

At resonance there are now only five source-visible cases:

1. paid cost < 0: immediate near-line PASS;
2. paid cost > 0: immediate near-line FAIL;
3. paid cost = 0 and atomic J2 exceeds the smooth-transfer envelope: FAIL;
4. paid cost = 0 and atomic J2 is below minus the envelope: PASS;
5. paid cost = 0 and the atomic J2 lies inside the transfer envelope.

The fifth case is the exact unresolved strip.  It does not assert J2=0; it says
only that the present atomic approximation is not sharp enough to certify its
sign.  A genuine J4 branch is justified only after the smooth J2 itself is
proved zero by the already-owned exceptional-locus theorem.
-/

noncomputable section
namespace Synthesis

open scoped Real

/-- Boundary FAIL compiler using only the atomic polynomial and the exact
smooth-transfer error envelope. -/
theorem QuarticFourSignedPolePair.exists_threeTapResonantTerminalProfile_neg_right_of_paidCost_zero_atomic_gt_errorEnvelope
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (hmult : 0 < mult)
    (hcost : W.threeTapResonancePaidCost eps = 0)
    (hmargin :
      W.threeTapJ2PolynomialErrorEnvelope eps
        < W.threeTapAtomicJ2Polynomial eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta →
        W.threeTapAdaptiveTerminalProfile eps mult a < 0 := by
  have hJ : 0 < W.threeTapNormalizedJ2Polynomial eps :=
    W.threeTapNormalizedJ2Polynomial_pos_of_atomic_gt_errorEnvelope hmargin
  exact
    W.exists_threeTapResonantTerminalProfile_neg_right_of_paidCost_zero_J2_pos
      ht hphase hmult hcost hJ

/-- Boundary PASS compiler under the symmetric strict negative atomic margin. -/
theorem QuarticFourSignedPolePair.exists_threeTapResonantTerminalProfile_pos_right_of_paidCost_zero_atomic_lt_neg_errorEnvelope
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (hmult : 0 < mult)
    (hcost : W.threeTapResonancePaidCost eps = 0)
    (hmargin :
      W.threeTapAtomicJ2Polynomial eps
        < - W.threeTapJ2PolynomialErrorEnvelope eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta →
        0 < W.threeTapAdaptiveTerminalProfile eps mult a := by
  have hJ : W.threeTapNormalizedJ2Polynomial eps < 0 :=
    W.threeTapNormalizedJ2Polynomial_neg_of_atomic_lt_neg_errorEnvelope hmargin
  exact
    W.exists_threeTapResonantTerminalProfile_pos_right_of_paidCost_zero_J2_neg
      ht hphase hmult hcost hJ

/-- The finite atomic max-cut partition.  Every resonance datum lies in exactly
one sign-resolved cost branch, one strict atomic-margin branch on the balanced
cost locus, or the explicit atomic uncertainty strip. -/
theorem QuarticFourSignedPolePair.threeTap_resonance_atomic_maxCut
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    (W.threeTapResonancePaidCost eps < 0)
    ∨
    (0 < W.threeTapResonancePaidCost eps)
    ∨
    (W.threeTapResonancePaidCost eps = 0
      ∧ W.threeTapJ2PolynomialErrorEnvelope eps
          < W.threeTapAtomicJ2Polynomial eps)
    ∨
    (W.threeTapResonancePaidCost eps = 0
      ∧ W.threeTapAtomicJ2Polynomial eps
          < - W.threeTapJ2PolynomialErrorEnvelope eps)
    ∨
    (W.threeTapResonancePaidCost eps = 0
      ∧ |W.threeTapAtomicJ2Polynomial eps|
          <= W.threeTapJ2PolynomialErrorEnvelope eps) := by
  rcases lt_trichotomy (W.threeTapResonancePaidCost eps) 0 with
      hcostNeg | hcostZero | hcostPos
  · exact Or.inl hcostNeg
  · have hE : 0 <= W.threeTapJ2PolynomialErrorEnvelope eps :=
      W.threeTapJ2PolynomialErrorEnvelope_nonneg
    by_cases hpos :
        W.threeTapJ2PolynomialErrorEnvelope eps
          < W.threeTapAtomicJ2Polynomial eps
    · exact Or.inr <| Or.inr <| Or.inl ⟨hcostZero, hpos⟩
    · by_cases hneg :
          W.threeTapAtomicJ2Polynomial eps
            < - W.threeTapJ2PolynomialErrorEnvelope eps
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨hcostZero, hneg⟩
      · have hupper :
            W.threeTapAtomicJ2Polynomial eps
              <= W.threeTapJ2PolynomialErrorEnvelope eps := by
          exact le_of_not_gt hpos
        have hlower :
            - W.threeTapJ2PolynomialErrorEnvelope eps
              <= W.threeTapAtomicJ2Polynomial eps := by
          exact le_of_not_gt hneg
        have habs :
            |W.threeTapAtomicJ2Polynomial eps|
              <= W.threeTapJ2PolynomialErrorEnvelope eps := by
          rw [abs_le]
          exact ⟨hlower, hupper⟩
        exact Or.inr <| Or.inr <| Or.inr <| Or.inr
          ⟨hcostZero, habs⟩
  · exact Or.inr <| Or.inl hcostPos

/-- If the atomic uncertainty strip is escaped on the balanced paid-cost locus,
then the one-scale near-line behavior is already decided. -/
theorem QuarticFourSignedPolePair.threeTap_resonance_balanced_atomic_resolved
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (hmult : 0 < mult)
    (hcost : W.threeTapResonancePaidCost eps = 0)
    (houtside :
      W.threeTapJ2PolynomialErrorEnvelope eps
        < W.threeTapAtomicJ2Polynomial eps
      ∨
      W.threeTapAtomicJ2Polynomial eps
        < - W.threeTapJ2PolynomialErrorEnvelope eps) :
    (
      ∃ delta : ℝ, 0 < delta ∧
        ∀ a : ℝ, 0 < a → a < delta →
          W.threeTapAdaptiveTerminalProfile eps mult a < 0
    )
    ∨
    (
      ∃ delta : ℝ, 0 < delta ∧
        ∀ a : ℝ, 0 < a → a < delta →
          0 < W.threeTapAdaptiveTerminalProfile eps mult a
    ) := by
  rcases houtside with hpos | hneg
  · exact Or.inl
      (W.exists_threeTapResonantTerminalProfile_neg_right_of_paidCost_zero_atomic_gt_errorEnvelope
        ht hphase hmult hcost hpos)
  · exact Or.inr
      (W.exists_threeTapResonantTerminalProfile_pos_right_of_paidCost_zero_atomic_lt_neg_errorEnvelope
        ht hphase hmult hcost hneg)

end Synthesis
