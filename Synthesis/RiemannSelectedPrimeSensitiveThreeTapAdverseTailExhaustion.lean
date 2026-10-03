import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAdverseNearBudget

/-!
# Literal exhaustion of the residual transformed adverse tail

The adverse pair carrier is nonnegative and summable.  Consequently the
residual after a sufficiently large literal `nearOffFinset t R` is arbitrarily
small.  This records the exact convergence supplied by reflection-pair
summability; no new Fourier tail estimate is required for unrestricted R.

For every eta>0 there exists a physical cutoff R with

  0 <= threeTapPairAdverseFarAfter eps R < eta.

Important firewall: the current unconditional arbitrary-endpoint RvM theorem
used for the finite-core budget requires `5 <= t-R`.  Summability by itself does
NOT guarantee that an eta-small cutoff can be chosen before this left-endpoint
threshold is crossed.  The usable one-scale cut therefore still requires one
RvM-compatible cutoff where the explicit finite-core budget plus the actual
residual tail beats the paid threshold.
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

/-- Unrestricted literal tail exhaustion.  No claim is made that the returned
R also satisfies the positive-left-endpoint condition used by the finite RvM
producer. -/
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
  have htail0 := W.threeTapPairAdverseFarAfter_nonneg ht (eps:=eps) (R:=R)
  refine ⟨R,hR,htail0,?_⟩
  linarith

/-- A cutoff is compatible with the currently-owned positive-height arbitrary-
endpoint RvM producer exactly when it is positive and leaves the left endpoint
at or above 5. -/
def QuarticFourSignedPolePair.ThreeTapRvMCompatibleCutoff
    {t : ℝ} (W : QuarticFourSignedPolePair t) (R : ℝ) : Prop :=
  0 < R ∧ 5 <= t-R

end Synthesis
