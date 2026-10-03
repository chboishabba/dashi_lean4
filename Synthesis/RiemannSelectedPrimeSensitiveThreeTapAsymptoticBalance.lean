import Synthesis.RiemannSelectedPrimeSensitiveThreeTapInverseSquareShells
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapCompensationFloor

/-!
# Final Route-A asymptotic balance surface

After the M0 and q^-2 cuts, the one-scale PASS has only four scalar inputs:

  finite(t,eps) + Ccurv * inverseSquareTail(t,t/2)
    < G - S/2,

where
* finite is the explicit witness-independent half-height budget,
* Ccurv is a uniform bound for the actual oscillatory curvature,
* G is the magnitude of the negative translated gamma+pole channel,
* S bounds the already-paid nonnegative local slack.

This file contains exact compilation of those inputs to the existing paid-cost
sign theorem.  On the inverse-square side it also isolates the one remaining
carrier cut: once the literal complementary zero tsum is bounded by a constant
times the already-proved dyadic numerical majorant, all infinite-series algebra
compiles automatically to the desired `O(log t/t)` tail bound.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators

/-- The complete adverse upper budget after the q^-2 reduction. -/
def threeTapRouteAAdverseBudget
    (t eps C Cmu Ccurv tail : ℝ) : ℝ :=
  threeTapUniformFiniteHalfHeightBudget t eps C Cmu
    + Ccurv * tail

/-- Abstract inverse-square RvM producer surface.  This is deliberately stated
on the exact literal tail object rather than on a surrogate density. -/
def ThreeTapInverseSquareTailBound
    (Ctail : ℝ) : Prop :=
  0 <= Ctail ∧
  ∀ t : ℝ, 200 <= t ->
    threeTapInverseSquareZeroTailAfter t (t/2)
      <= Ctail * ((2*Real.log t + 1)/t)

/-- Exact remaining shell-partition surface.  All zero-count input and the
numerical dyadic series are already paid elsewhere; this predicate asks only
for the literal complementary zero carrier to be dominated by that series. -/
def ThreeTapInverseSquareShellPartitionBound
    (Ashell : ℝ) : Prop :=
  0 <= Ashell ∧
  ∀ t : ℝ, 200 <= t ->
    threeTapInverseSquareZeroTailAfter t (t/2)
      <= Ashell * (∑' k : ℕ, threeTapDyadicLogMajorant t k)

/-- Once the exact carrier-to-shell inequality is supplied, the already-paid
closed form of the dyadic series gives the Route-A log-over-t tail with no
further zero analysis.  The harmless factor four absorbs the `+4` in the
closed-form shell sum into the normalized `(2 log t + 1)/t` scale. -/
theorem ThreeTapInverseSquareShellPartitionBound.toTailBound
    {Ashell : ℝ}
    (h : ThreeTapInverseSquareShellPartitionBound Ashell) :
    ThreeTapInverseSquareTailBound (4 * Ashell) := by
  refine ⟨mul_nonneg (by norm_num) h.1, ?_⟩
  intro t ht
  have ht0 : t ≠ 0 := by linarith
  have htpos : 0 < t := by linarith
  have hlog : 0 <= Real.log t :=
    Real.log_nonneg (by linarith : 1 <= t)
  have hraw := h.2 t ht
  rw [tsum_threeTapDyadicLogMajorant ht0] at hraw
  have hnum :
      2 * Real.log t + 4 <= 4 * (2 * Real.log t + 1) := by
    linarith
  have hfrac :
      (2 * Real.log t + 4) / t
        <= 4 * ((2 * Real.log t + 1) / t) := by
    have hdiv := div_le_div_of_nonneg_right hnum htpos.le
    convert hdiv using 1 <;> ring
  calc
    threeTapInverseSquareZeroTailAfter t (t/2)
        <= Ashell * ((2 * Real.log t + 4) / t) := hraw
    _ <= Ashell * (4 * ((2 * Real.log t + 1) / t)) :=
      mul_le_mul_of_nonneg_left hfrac h.1
    _ = (4 * Ashell) * ((2 * Real.log t + 1) / t) := by ring

/-- Existential form used by the regression target once the literal shell
partition producer is paid. -/
theorem exists_threeTapInverseSquareTailBound_of_shellPartition
    (h : ∃ Ashell : ℝ, ThreeTapInverseSquareShellPartitionBound Ashell) :
    ∃ Ctail : ℝ, ThreeTapInverseSquareTailBound Ctail := by
  obtain ⟨Ashell, hAshell⟩ := h
  exact ⟨4 * Ashell, hAshell.toTailBound⟩

/-- If the exact inverse-square tail and compact-alpha curvature are controlled,
the actual adverse residual at the compatible half-height cutoff inherits their
product bound. -/
theorem QuarticFourSignedPolePair.threeTapHalfHeightFar_le_curvature_tail
    {t eps Ccurv : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hcurv : W.ThreeTapUniformCurvatureBound eps Ccurv)
    (hinv : Summable
      (fun sigma : {sigma : ((SameOrd t)ᶜ : Set Zeros) //
          sigma ∉ nearOffFinset t (t/2)} =>
        ((Zeta23.zetaZeroConfig).mult
            ((sigma : ((SameOrd t)ᶜ : Set Zeros)) : Zeros) : ℝ)
          / ((((sigma : ((SameOrd t)ᶜ : Set Zeros)) : Zeros) : ℂ).im - t)^2)) :
    W.threeTapPairAdverseFarAfter eps (t/2)
      <= Ccurv * threeTapInverseSquareZeroTailAfter t (t/2) := by
  exact W.threeTapPairAdverseFarAfter_le_curvature_mul_inverseSquareTail
    ht (by linarith : 0 < t/2) hcurv hinv

/-- The clean final one-scale PASS compiler.  Strictness is placed on the full
adverse budget, so no artificial factor-of-two split threshold is needed. -/
theorem QuarticFourSignedPolePair.exists_threeTapRouteAAsymptoticBalancePass_constants :
    ∃ C Cmu : ℝ, 0 <= C ∧ 0 <= Cmu ∧
      ∀ {t eps Ccurv G S : ℝ},
        200 <= t ->
        ∀ W : QuarticFourSignedPolePair t,
        W.ThreeTapUniformCurvatureBound eps Ccurv ->
        Summable
          (fun sigma : {sigma : ((SameOrd t)ᶜ : Set Zeros) //
              sigma ∉ nearOffFinset t (t/2)} =>
            ((Zeta23.zetaZeroConfig).mult
                ((sigma : ((SameOrd t)ᶜ : Set Zeros)) : Zeros) : ℝ)
              / ((((sigma : ((SameOrd t)ᶜ : Set Zeros)) : Zeros) : ℂ).im - t)^2) ->
        W.threeTapGammaPoleCombination eps <= -G ->
        W.threeTapAdaptiveLocalSlack eps <= S ->
        threeTapRouteAAdverseBudget t eps C Cmu Ccurv
            (threeTapInverseSquareZeroTailAfter t (t/2))
          < G - (1/2 : ℝ)*S ->
        W.threeTapResonancePaidCost eps < 0 := by
  obtain ⟨C,Cmu,hC,hCmu,hpass⟩ :=
    QuarticFourSignedPolePair.exists_threeTapGammaPoleSlackPass_constants
  refine ⟨C,Cmu,hC,hCmu,?_⟩
  intro t eps Ccurv G S ht W hcurv hinv hgp hslack hbalance
  let F := threeTapUniformFiniteHalfHeightBudget t eps C Cmu
  let T := Ccurv * threeTapInverseSquareZeroTailAfter t (t/2)
  let H := F + T
  have hfarLe : W.threeTapPairAdverseFarAfter eps (t/2) <= T := by
    dsimp [T]
    exact W.threeTapHalfHeightFar_le_curvature_tail ht hcurv hinv
  have hfinite : F <= H := by
    dsimp [H,T]
    have hC0 := hcurv.1
    have htail0 := threeTapInverseSquareZeroTailAfter_nonneg t (t/2)
    positivity
  have hfar : W.threeTapPairAdverseFarAfter eps (t/2) < H := by
    have hF0 : 0 <= F := by
      dsimp [F, threeTapUniformFiniteHalfHeightBudget]
      exact mul_nonneg (threeTapUniformM0Bound_nonneg eps)
        (threeTapHalfHeightLogCoefficient_nonneg ht hC hCmu)
    dsimp [H]
    linarith
  have hH : H <= G - (1/2 : ℝ)*S := by
    dsimp [H,F,T,threeTapRouteAAdverseBudget] at hbalance ⊢
    exact hbalance.le
  exact hpass ht W hfinite hfar hgp hslack hH

/-- Once the inverse-square RvM tail has the expected log-over-t scale, the
whole adverse side has the same scale with an explicit coefficient. -/
theorem threeTapRouteAAdverseBudget_le_logOverT
    {t eps C Cmu Ccurv Ctail tail : ℝ}
    (ht : 200 <= t)
    (hC : 0 <= C)
    (hCmu : 0 <= Cmu)
    (hcurv : 0 <= Ccurv)
    (htail0 : 0 <= tail)
    (htail : tail <= Ctail * ((2*Real.log t + 1)/t)) :
    threeTapRouteAAdverseBudget t eps C Cmu Ccurv tail
      <=
    (threeTapUniformM0Bound eps * (256*Cmu + (3328/5)*C)
      + Ccurv*Ctail)
      * ((2*Real.log t + 1)/t) := by
  have hfinite := threeTapUniformFiniteHalfHeightBudget_le_logOverT
    ht hC hCmu (eps:=eps)
  have hscale : 0 <= (2*Real.log t + 1)/t := by
    have ht0 : 0 < t := by linarith
    have hlog : 0 <= Real.log t := Real.log_nonneg (by linarith : 1 <= t)
    positivity
  have htailScaled :
      Ccurv * tail
        <= Ccurv * (Ctail * ((2*Real.log t + 1)/t)) :=
    mul_le_mul_of_nonneg_left htail hcurv
  unfold threeTapRouteAAdverseBudget
  calc
    threeTapUniformFiniteHalfHeightBudget t eps C Cmu + Ccurv*tail
      <= threeTapUniformM0Bound eps
          * ((256*Cmu + (3328/5)*C) * ((2*Real.log t + 1)/t))
        + Ccurv * (Ctail * ((2*Real.log t + 1)/t)) :=
          add_le_add hfinite htailScaled
    _ = (threeTapUniformM0Bound eps * (256*Cmu + (3328/5)*C)
          + Ccurv*Ctail) * ((2*Real.log t + 1)/t) := by ring

end Synthesis
