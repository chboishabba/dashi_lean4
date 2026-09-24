import Synthesis.RiemannCenteredPairCurvature
import Synthesis.RiemannCenteredNearPairSign
import Synthesis.RiemannFinalEvenConeNearFarSplit

/-!
# Explicit far-only upper for the centered final Off channel

The centered finite near core is nonpositive inside J*Lambda <= pi/2, and the
centered reflection-pair curvature has an explicit coefficient.  Therefore the
only positive contribution to the final centered Off channel is the explicit
far-shell remainder, with no existential curvature constant.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.ReflectionPairCurvatureBound
open Zeta23Bridge.FarShellCutoffTailBound

theorem exists_centeredOff_explicit_farOnly_upper
    {g : ℝ → ℝ} {Lambda t r : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hnn : ∀ u, 0 <= g u)
    (hsupp : ∀ u, g u ≠ 0 → |u| <= Lambda)
    (hLambda : 0 <= Lambda) :
    ∃ A : ℝ, 1 <= A ∧
      ∀ J : ℕ, 1 <= J ->
        (J : ℝ) * Lambda <= Real.pi / 2 ->
        evenConeFunctional
            (offOrdVec (sampleFam (gammaCenteredTaper g r) t 0) t)
          <=
          (1 / 2 : ℝ) *
            (centeredPairCurvatureCoeff g Lambda r
              * farShellBound A |t| J) := by
  obtain ⟨A, hA1, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  refine ⟨A, hA1, ?_⟩
  intro J hJ hJwindow

  have hh2 := gammaCenteredTaper_contDiff hgs r
  have hhc := gammaCenteredTaper_hasCompactSupport hgc r
  have hhe := gammaCenteredTaper_even heven r
  have hC0 : 0 <= centeredPairCurvatureCoeff g Lambda r :=
    centeredPairCurvatureCoeff_nonneg g hLambda r
  have hC : ∀ rho : Zeros,
      pairWeightCurvature (gammaCenteredTaper g r) (heightOf rho)
        <= centeredPairCurvatureCoeff g Lambda r := by
    intro rho
    exact pairWeightCurvature_gammaCenteredTaper_le
      hgs hsupp hLambda (abs_heightOf_le rho)

  have hsplit :=
    abs_finalOffOrd_sub_finiteNear_le
      hh2 hhc hhe t 0 hA1 hC0 hloc hC J hJ

  have hnear :=
    centeredFiniteNearCore_nonpos
      hgs hgc heven hnn hsupp hLambda J hJwindow
      (t := t) (r := r)

  have hdir :
      evenConeFunctional
          (offOrdVec (sampleFam (gammaCenteredTaper g r) t 0) t)
        - (1 / 2 : ℝ) *
            ∑ sigma ∈ finalNearOffFinset t J,
              finalPairTerm (gammaCenteredTaper g r) t 0 sigma
      <=
      |evenConeFunctional
          (offOrdVec (sampleFam (gammaCenteredTaper g r) t 0) t)
        - (1 / 2 : ℝ) *
            ∑ sigma ∈ finalNearOffFinset t J,
              finalPairTerm (gammaCenteredTaper g r) t 0 sigma| :=
    le_abs_self _

  have hnearhalf :
      (1 / 2 : ℝ) *
          ∑ sigma ∈ finalNearOffFinset t J,
            finalPairTerm (gammaCenteredTaper g r) t 0 sigma
        <= 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) hnear

  linarith

end Synthesis
