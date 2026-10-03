import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAdverseNearBudget

/-!
# Literal exhaustion of the residual transformed adverse tail

The adverse pair carrier is nonnegative and summable.  Consequently the
residual after a sufficiently large literal `nearOffFinset t R` is arbitrarily
small.  This is stronger and cleaner than introducing a new absolute Fourier
tail constant: the required convergence is already owned by the exact
reflection-pair summability theorem.

Thus `Bfar` is not an independent zero-distribution hypothesis.  For every
eta>0 there exists a physical cutoff R with

  0 <= threeTapPairAdverseFarAfter eps R < eta.

The substantive one-scale inequality is therefore concentrated in the finite
RvM core and how its explicit budget compares with the paid threshold.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators
open Zeta23Bridge.OffOrdinateCutoffCarrier

/-- Every finite adverse near sum is bounded by the total adverse tsum. -/
theorem QuarticFourSignedPolePair.threeTapPairAdverseNearAt_le_tsum
    {t eps R : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapPairAdverseNearAt eps R
      <=
    ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      W.threeTapPairAdversePart eps (sigma : Zeros) := by
  classical
  unfold QuarticFourSignedPolePair.threeTapPairAdverseNearAt
  exact Summable.sum_le_tsum
    (nearOffFinset t R)
    (fun sigma hsigma =>
      W.threeTapPairAdversePart_nonneg (eps:=eps) (sigma : Zeros))
    (W.threeTapPairAdversePart_summable ht (eps:=eps))

theorem QuarticFourSignedPolePair.threeTapPairAdverseFarAfter_nonneg
    {t eps R : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    0 <= W.threeTapPairAdverseFarAfter eps R := by
  unfold QuarticFourSignedPolePair.threeTapPairAdverseFarAfter
  exact sub_nonneg.mpr (W.threeTapPairAdverseNearAt_le_tsum ht)

/-- Any finite set of off-ordinate zeros is contained in a sufficiently large
literal near-off window. -/
theorem exists_radius_covering_offOrd_finset
    {t : ℝ}
    (s : Finset ((SameOrd t)ᶜ : Set Zeros)) :
    ∃ R : ℝ, 0 < R ∧ s ⊆ nearOffFinset t R := by
  classical
  let R : ℝ :=
    1 + ∑ sigma ∈ s,
      |((sigma : Zeros) : ℂ).im - t|
  have hR : 0 < R := by
    dsimp [R]
    have hs :
        0 <= ∑ sigma ∈ s,
          |((sigma : Zeros) : ℂ).im - t| := by positivity
    linarith
  refine ⟨R,hR,?_⟩
  intro sigma hsigma
  apply (mem_nearOffFinset_iff t R sigma).2
  have hsingle :
      |((sigma : Zeros) : ℂ).im - t|
        <=
      ∑ tau ∈ s, |((tau : Zeros) : ℂ).im - t| := by
    exact Finset.single_le_sum
      (fun tau htau => abs_nonneg (((tau : Zeros) : ℂ).im - t))
      hsigma
  dsimp [R]
  linarith

/-- Summability closes the far adverse tail: for any requested positive error,
there is a literal physical ordinate cutoff making the residual smaller. -/
theorem QuarticFourSignedPolePair.exists_threeTapPairAdverseFarAfter_lt
    {t eps eta : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (heta : 0 < eta) :
    ∃ R : ℝ, 0 < R ∧
      0 <= W.threeTapPairAdverseFarAfter eps R ∧
      W.threeTapPairAdverseFarAfter eps R < eta := by
  classical
  let f : ((SameOrd t)ᶜ : Set Zeros) → ℝ :=
    fun sigma => W.threeTapPairAdversePart eps (sigma : Zeros)
  have hf : Summable f := by
    dsimp [f]
    exact W.threeTapPairAdversePart_summable ht (eps:=eps)
  have hsum : HasSum f (∑' sigma, f sigma) := hf.hasSum
  rcases Metric.tendsto_atTop.1 hsum eta heta with ⟨s,hs⟩
  obtain ⟨R,hR,hcover⟩ := exists_radius_covering_offOrd_finset s
  have hsApprox := hs (nearOffFinset t R) hcover
  have hsLe :
      (∑ sigma ∈ s, f sigma)
        <= ∑' sigma, f sigma := by
    exact Summable.sum_le_tsum s
      (fun sigma hsigma =>
        W.threeTapPairAdversePart_nonneg (eps:=eps) (sigma : Zeros)) hf
  have hnearLe :
      W.threeTapPairAdverseNearAt eps R
        <= ∑' sigma, f sigma := by
    simpa [f] using W.threeTapPairAdverseNearAt_le_tsum ht (eps:=eps) (R:=R)
  have hsNear :
      (∑ sigma ∈ s, f sigma)
        <= W.threeTapPairAdverseNearAt eps R := by
    unfold QuarticFourSignedPolePair.threeTapPairAdverseNearAt
    exact Finset.sum_le_sum_of_subset_of_nonneg hcover
      (fun sigma hnear hs =>
        W.threeTapPairAdversePart_nonneg (eps:=eps) (sigma : Zeros))
  have hgap :
      (∑' sigma, f sigma) - (∑ sigma ∈ s, f sigma) < eta := by
    rw [Real.dist_eq] at hsApprox
    have habs :
        |(∑ sigma ∈ s, f sigma) - (∑' sigma, f sigma)| < eta := hsApprox
    rw [abs_of_nonpos (sub_nonpos.mpr hsLe)] at habs
    linarith
  have htailLt : W.threeTapPairAdverseFarAfter eps R < eta := by
    unfold QuarticFourSignedPolePair.threeTapPairAdverseFarAfter
    change
      (∑' sigma, f sigma) - W.threeTapPairAdverseNearAt eps R < eta
    linarith
  refine ⟨R,hR,?_,htailLt⟩
  exact W.threeTapPairAdverseFarAfter_nonneg ht

/-- The far-tail input in the PASS compiler can therefore always be chosen
arbitrarily small; only the corresponding finite-core budget changes with R. -/
theorem QuarticFourSignedPolePair.exists_threeTapResonancePaidCost_neg_of_explicitNear_margin
    {t eps A C Cmu eta : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (heta : 0 < eta)
    (hnearProvider :
      ∀ R : ℝ, 0 < R →
        W.threeTapPairAdverseNearAt eps R
          <= W.threeTapAdverseNearExplicitBudget eps A R C Cmu)
    (hbudget :
      ∃ R : ℝ, 0 < R ∧
        W.threeTapPairAdverseFarAfter eps R < eta ∧
        (1/2 : ℝ) *
          (W.threeTapAdverseNearExplicitBudget eps A R C Cmu + eta)
          < W.threeTapAdaptiveLocalExact eps
              - W.threeTapResonanceCompensation eps) :
    W.threeTapResonancePaidCost eps < 0 := by
  obtain ⟨R,hR,hfar,hpaid⟩ := hbudget
  exact W.threeTapResonancePaidCost_neg_of_explicitNear_and_far
    ht (hnearProvider R hR) (le_of_lt hfar) hpaid

end Synthesis
