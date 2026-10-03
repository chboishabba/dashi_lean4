import Synthesis.RiemannSelectedPrimeSensitiveThreeTapCurvatureMaxCut
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAdverseTailExhaustion
import Synthesis.RiemannZeta23RvMArbitraryEndpointCountBound

/-!
# Actual adverse far tail -> inverse-square zero tail

For a finite literal near window s = nearOffFinset(t,R), summability gives the
exact decomposition

  tsum adverse = sum_s adverse + tsum_{sigma notin s} adverse.

Hence the repository's subtraction-defined `threeTapPairAdverseFarAfter` is
exactly the complementary subtype tsum.  Combining this identity with the
uniform-curvature per-pair majorant reduces the full far contribution to one
classical positive zero-count tail:

  FarAfter <= C_curv * sum_{sigma notin near}
    mult(sigma)/(gamma_sigma-t)^2.

The imported arbitrary-endpoint count theorem now pays the positive-height RvM
counting input on the same literal `Ncount` carrier.  The remaining analytic cut
is the two-sided dyadic-shell summation, including the negative-ordinate side;
that side must be paid on the literal all-real local zero-count carrier rather
than by silently assuming positive ordinates.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators
open Zeta23Bridge.OffOrdinateCutoffCarrier

/-- Positive inverse-square zero-count tail on the exact complement of the
literal finite near window. -/
def threeTapInverseSquareZeroTailAfter
    (t R : ℝ) : ℝ :=
  ∑' sigma : {sigma : ((SameOrd t)ᶜ : Set Zeros) //
      sigma ∉ nearOffFinset t R},
    ((Zeta23.zetaZeroConfig).mult ((sigma : ((SameOrd t)ᶜ : Set Zeros)) : Zeros) : ℝ)
      / ((((sigma : ((SameOrd t)ᶜ : Set Zeros)) : Zeros) : ℂ).im - t)^2

theorem threeTapInverseSquareZeroTailAfter_nonneg
    (t R : ℝ) :
    0 <= threeTapInverseSquareZeroTailAfter t R := by
  unfold threeTapInverseSquareZeroTailAfter
  exact tsum_nonneg fun sigma => by positivity

/-- The subtraction-defined residual adverse tail is exactly the complementary
subtype tsum. -/
theorem QuarticFourSignedPolePair.threeTapPairAdverseFarAfter_eq_compl_tsum
    {t eps R : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapPairAdverseFarAfter eps R
      =
    ∑' sigma : {sigma : ((SameOrd t)ᶜ : Set Zeros) //
        sigma ∉ nearOffFinset t R},
      W.threeTapPairAdversePart eps
        ((sigma : ((SameOrd t)ᶜ : Set Zeros)) : Zeros) := by
  classical
  let f : ((SameOrd t)ᶜ : Set Zeros) -> ℝ :=
    fun sigma => W.threeTapPairAdversePart eps (sigma : Zeros)
  have hf : Summable f := by
    dsimp [f]
    exact W.threeTapPairAdversePart_summable ht (eps:=eps)
  have hsplit := sum_add_tsum_subtype_compl hf (nearOffFinset t R)
  unfold QuarticFourSignedPolePair.threeTapPairAdverseFarAfter
    QuarticFourSignedPolePair.threeTapPairAdverseNearAt
  change (∑' sigma, f sigma) - ∑ sigma ∈ nearOffFinset t R, f sigma = _
  change (∑' sigma, f sigma) - (nearOffFinset t R).sum f = _
  change _ = ∑' sigma : {sigma : ((SameOrd t)ᶜ : Set Zeros) //
      sigma ∉ nearOffFinset t R}, f (sigma : ((SameOrd t)ᶜ : Set Zeros))
  linarith

/-- The inverse-square complementary carrier is the only remaining zero-count
object once uniform curvature is paid. -/
theorem QuarticFourSignedPolePair.threeTapPairAdverseFarAfter_le_curvature_mul_inverseSquareTail
    {t eps R C : ℝ}
    (ht : 200 <= t)
    (hR : 0 <= R)
    (W : QuarticFourSignedPolePair t)
    (hcurv : W.ThreeTapUniformCurvatureBound eps C)
    (hinv : Summable
      (fun sigma : {sigma : ((SameOrd t)ᶜ : Set Zeros) //
          sigma ∉ nearOffFinset t R} =>
        ((Zeta23.zetaZeroConfig).mult
            ((sigma : ((SameOrd t)ᶜ : Set Zeros)) : Zeros) : ℝ)
          / ((((sigma : ((SameOrd t)ᶜ : Set Zeros)) : Zeros) : ℂ).im - t)^2)) :
    W.threeTapPairAdverseFarAfter eps R
      <= C * threeTapInverseSquareZeroTailAfter t R := by
  classical
  rw [W.threeTapPairAdverseFarAfter_eq_compl_tsum ht]
  let f : {sigma : ((SameOrd t)ᶜ : Set Zeros) //
      sigma ∉ nearOffFinset t R} -> ℝ :=
    fun sigma => W.threeTapPairAdversePart eps
      ((sigma : ((SameOrd t)ᶜ : Set Zeros)) : Zeros)
  let g : {sigma : ((SameOrd t)ᶜ : Set Zeros) //
      sigma ∉ nearOffFinset t R} -> ℝ :=
    fun sigma =>
      ((Zeta23.zetaZeroConfig).mult
          ((sigma : ((SameOrd t)ᶜ : Set Zeros)) : Zeros) : ℝ)
        / ((((sigma : ((SameOrd t)ᶜ : Set Zeros)) : Zeros) : ℂ).im - t)^2
  have hf : Summable f := by
    dsimp [f]
    exact (W.threeTapPairAdversePart_summable ht (eps:=eps)).subtype _
  have hg : Summable g := by simpa [g] using hinv
  have hpoint : ∀ sigma, f sigma <= C * g sigma := by
    intro sigma
    have hnot := sigma.property
    have hmemnot :
        ¬ |((((sigma : ((SameOrd t)ᶜ : Set Zeros)) : Zeros) : ℂ).im - t)| <= R := by
      intro hle
      exact hnot ((mem_nearOffFinset_iff t R
        (sigma : ((SameOrd t)ᶜ : Set Zeros))).2 hle)
    have hdist :
        R < |((((sigma : ((SameOrd t)ᶜ : Set Zeros)) : Zeros) : ℂ).im - t)| :=
      lt_of_not_ge hmemnot
    have hord :
        ((((sigma : ((SameOrd t)ᶜ : Set Zeros)) : Zeros) : ℂ).im - t) ≠ 0 := by
      intro hz
      rw [hz, abs_zero] at hdist
      linarith
    have hpair := W.threeTapPairAdversePart_le_uniformInverseSquare
      ht hcurv ((sigma : ((SameOrd t)ᶜ : Set Zeros)) : Zeros) hord
    dsimp [f,g]
    convert hpair using 1 <;> ring
  have hCg : Summable (fun sigma => C * g sigma) := hg.mul_left C
  have hsum := tsum_le_tsum hpoint hf hCg
  have hfactor :
      (∑' sigma, C * g sigma) = C * ∑' sigma, g sigma := by
    exact hg.tsum_mul_left C
  rw [hfactor] at hsum
  simpa [threeTapInverseSquareZeroTailAfter, g] using hsum

end Synthesis
