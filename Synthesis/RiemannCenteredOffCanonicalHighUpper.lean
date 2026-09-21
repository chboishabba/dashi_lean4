import Synthesis.RiemannCenteredOffExplicitFarOnly
import Synthesis.RiemannCanonicalSignedWindowCutoff

/-!
# Explicit high-ordinate centered Off upper

For |t| >= 18 and the canonical support radius

    Lambda <= 9*pi/(4|t|),

choose J=floor(|t|/9).  This cutoff lies inside the centered-pair cosine window,
so the finite near core is nonpositive.  Combining the explicit centered
curvature with the explicit far-shell bound gives a fully quantitative upper.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone

def centeredOffHighEnvelope (A : ℝ) (g : ℝ → ℝ)
    (Lambda r t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * centeredPairCurvatureCoeff g Lambda r *
    (324 * A * Real.log (|t| + 4) / |t|
      + 72 * A * Real.sqrt (18 / |t|))

theorem exists_centeredOff_canonicalHigh_upper
    {g : ℝ → ℝ} {Lambda t r : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hnn : ∀ u, 0 <= g u)
    (hsupp : ∀ u, g u ≠ 0 → |u| <= Lambda)
    (hLambda : 0 <= Lambda)
    (ht : 18 <= |t|)
    (hcanonical : Lambda <= 9 * Real.pi / (4 * |t|)) :
    ∃ A : ℝ, 1 <= A ∧
      evenConeFunctional
          (offOrdVec (sampleFam (gammaCenteredTaper g r) t 0) t)
        <= centeredOffHighEnvelope A g Lambda r t := by
  obtain ⟨A, hA, hoff⟩ :=
    exists_centeredOff_explicit_farOnly_upper
      hgs hgc heven hnn hsupp hLambda
      (t := t) (r := r)
  refine ⟨A, hA, ?_⟩

  let J := canonicalSignedWindowCutoff t
  have hJ : 1 <= J := canonicalSignedWindowCutoff_one_le ht
  have hJwindow :
      (J : ℝ) * Lambda <= Real.pi / 2 :=
    canonicalSignedWindowCutoff_mul_support_le ht hLambda hcanonical

  have hbase := hoff J hJ hJwindow
  have hfar :=
    farShellBound_canonicalSignedWindowCutoff_le
      (A := A) (t := t) (le_trans (by norm_num) hA) ht
  have hC0 : 0 <= centeredPairCurvatureCoeff g Lambda r :=
    centeredPairCurvatureCoeff_nonneg g hLambda r
  have hscale :
      (1 / 2 : ℝ) * centeredPairCurvatureCoeff g Lambda r
        * Zeta23Bridge.FarShellCutoffTailBound.farShellBound A |t| J
      <=
      (1 / 2 : ℝ) * centeredPairCurvatureCoeff g Lambda r
        * (324 * A * Real.log (|t| + 4) / |t|
          + 72 * A * Real.sqrt (18 / |t|)) := by
    exact mul_le_mul_of_nonneg_left hfar
      (mul_nonneg (by norm_num) hC0)

  unfold centeredOffHighEnvelope
  exact le_trans hbase hscale

end Synthesis
