import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAdverseNearEnvelope

/-!
# Strict adverse near carrier -> literal half-open Zeta window

`nearOffFinset t R` is the strict symmetric off-ordinate carrier

  |Im rho - t| < R,

whereas the exact RvM producer uses the literal Zeta23 window

  t-R < Im rho <= t+R.

For the adverse physical test every summand is nonnegative.  Therefore the
strict off-ordinate finite envelope is bounded by the broader literal half-open
weighted zero pairing.  Same-ordinate and right-endpoint atoms are retained on
the producer side as nonnegative extra mass; no generic-position assumption is
made.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators
open Zeta23Bridge.OffOrdinateCutoffCarrier

/-- The finite ordinate envelope on `nearOffFinset` is bounded by the literal
Zeta23 half-open weighted window. -/
theorem QuarticFourSignedPolePair.threeTapPairAdverseNearEnvelopeAt_le_windowPair
    {t eps A R : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapPairAdverseNearEnvelopeAt eps A R
      <=
    zetaWindowWeightedPair (t-R) (t+R)
      (W.threeTapAdversePhysicalOrdinateTest eps A) := by
  classical
  let F : Finset ((SameOrd t)ᶜ : Set Zeros) := nearOffFinset t R
  let H : Finset ℂ := F.image fun sigma => ((sigma : Zeros) : ℂ)
  let G : Finset ℂ :=
    (zetaZeroConfig.finite_window (t-R) (t+R)).toFinset
  let f : ℂ → ℝ := fun z =>
    (zetaZeroConfig.mult z : ℝ)
      * W.threeTapAdversePhysicalOrdinateTest eps A z.im
  have hsubset : H ⊆ G := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨sigma, hsigma, rfl⟩
    have hnear : |((sigma : Zeros) : ℂ).im - t| < R :=
      (mem_nearOffFinset_iff t R sigma).1 hsigma
    rw [abs_lt] at hnear
    have hwin :
        ((sigma : Zeros) : ℂ) ∈
          zetaZeroConfig.window (t-R) (t+R) := by
      exact ⟨(sigma : Zeros).2, by linarith, by linarith⟩
    simpa [G] using hwin
  have hnearRewrite :
      W.threeTapPairAdverseNearEnvelopeAt eps A R
        = ∑ z ∈ H, f z := by
    unfold QuarticFourSignedPolePair.threeTapPairAdverseNearEnvelopeAt
    dsimp [F,H,f]
    rw [Finset.sum_image]
    · rfl
    · intro a ha b hb hab
      exact Subtype.ext hab
  have hwindowRewrite :
      zetaWindowWeightedPair (t-R) (t+R)
        (W.threeTapAdversePhysicalOrdinateTest eps A)
        = ∑ z ∈ G, f z := by
    unfold zetaWindowWeightedPair
    rw [finsum_mem_eq_finite_toFinset_sum _
      (zetaZeroConfig.finite_window (t-R) (t+R))]
    rfl
  rw [hnearRewrite, hwindowRewrite]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun z hzG hzH =>
      mul_nonneg (by positivity)
        (W.threeTapAdversePhysicalOrdinateTest_nonneg ht))

/-- Full same-object finite adverse core -> literal RvM weighted pair. -/
theorem QuarticFourSignedPolePair.threeTapPairAdverseNearAt_le_windowPair
    {t eps A R : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hA : 0 <= A)
    (hstrip : W.ThreeTapAlphaStripBound A) :
    W.threeTapPairAdverseNearAt eps R
      <=
    zetaWindowWeightedPair (t-R) (t+R)
      (W.threeTapAdversePhysicalOrdinateTest eps A) := by
  exact
    (W.threeTapPairAdverseNearAt_le_envelope ht hA hstrip).trans
      (W.threeTapPairAdverseNearEnvelopeAt_le_windowPair
        (by linarith : 0 < t))

/-- The finite adverse transformed source is now literally bounded by the
smooth-density term plus the exact AC discrepancy Abel remainder. -/
theorem QuarticFourSignedPolePair.threeTapPairAdverseNearAt_le_mu_add_discrepancyAbel
    {t eps A R : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hA : 0 <= A)
    (hR : 0 <= R)
    (hstrip : W.ThreeTapAlphaStripBound A) :
    W.threeTapPairAdverseNearAt eps R
      <=
    (∫ x in (t-R)..(t+R),
      W.threeTapAdversePhysicalOrdinateTest eps A x * Zeta23.mu x)
      +
    W.threeTapAdversePhysicalOrdinateTest eps A (t+R)
      * zetaMuCumulativeDiscrepancy (t-R) (t+R)
      -
    ∫ x in (t-R)..(t+R),
      deriv (W.threeTapAdversePhysicalOrdinateTest eps A) x
        * zetaMuCumulativeDiscrepancy (t-R) x := by
  have hnear := W.threeTapPairAdverseNearAt_le_windowPair ht hA hstrip
  rw [W.threeTapAdverseWindowPair_eq_mu_add_discrepancyAbel
    (by linarith : 0 < t) hR] at hnear
  exact hnear

end Synthesis
