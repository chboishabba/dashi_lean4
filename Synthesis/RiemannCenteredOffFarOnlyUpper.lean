import Synthesis.RiemannCenteredNearPairSign
import Synthesis.RiemannFinalEvenConeNearFarSplit

/-!
# Centered final Off response: only the far remainder can be positive

For h_r = g(cos(r u)-1), the finite near reflection-pair core is nonpositive
whenever J*Lambda <= pi/2.

Combining that sign theorem with the final-carrier near/far decomposition gives

  Off_{h_r}(t,0) <= 1/2 * C * farShellBound A |t| J

for every cutoff J that stays inside the cosine window.

Thus no positive near-core budget is needed on this route; all positive Off risk
is pushed into the explicit far remainder.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.FarShellCutoffTailBound

theorem exists_centeredOff_farOnly_upper
    {g : ℝ → ℝ} {Lambda t r : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hnn : ∀ u, 0 <= g u)
    (hsupp : ∀ u, g u ≠ 0 → |u| <= Lambda)
    (hLambda : 0 <= Lambda) :
    ∃ A C : ℝ, 1 <= A ∧ 0 <= C ∧
      ∀ J : ℕ, 1 <= J ->
        (J : ℝ) * Lambda <= Real.pi / 2 ->
        evenConeFunctional
            (offOrdVec (sampleFam (gammaCenteredTaper g r) t 0) t)
          <= (1 / 2 : ℝ) * (C * farShellBound A |t| J) := by
  have hh2 := gammaCenteredTaper_contDiff hgs r
  have hhc := gammaCenteredTaper_hasCompactSupport hgc r
  have hhe := gammaCenteredTaper_even heven r
  obtain ⟨A, C, hA, hC, hsplit, -⟩ :=
    exists_finalEvenCone_near_far_split hh2 hhc hhe t 0
  refine ⟨A, C, hA, hC, ?_⟩
  intro J hJ hJwindow
  have hnear :=
    centeredFiniteNearCore_nonpos
      hgs hgc heven hnn hsupp hLambda J hJwindow
      (t := t) (r := r)
  have hbound := hsplit J hJ
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
  have hhalf : 0 <= (1 / 2 : ℝ) := by norm_num
  have hnearhalf :
      (1 / 2 : ℝ) *
          ∑ sigma ∈ finalNearOffFinset t J,
            finalPairTerm (gammaCenteredTaper g r) t 0 sigma
        <= 0 :=
    mul_nonpos_of_nonneg_of_nonpos hhalf hnear
  linarith

end Synthesis
