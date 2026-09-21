import Synthesis.RiemannProjectiveQuarticSmoothInhabitant
import Synthesis.RiemannProjectiveQuarticThreeWindow

/-!
# Rescaling the smooth quartic-escape detector to the physical sample radius

For a normalized profile G and r>0 define

  G_r(u) = G(r u).

Then:
  evenResp(G_r,0,c r) = r^{-1} evenResp(G,0,c),
  SqResp(G_r,c r)     = r^{-3} SqResp(G,c),
  FourthResp(G_r,c r) = r^{-5} FourthResp(G,c).

Hence the projective moments scale exactly by

  J2(G_r,r) = r^{-4} J2(G,1),
  J4(G_r,r) = r^{-6} J4(G,1).

So the smooth quartic-escape witness at normalized radius one transports
without loss of sign or cancellation to the physical radius r=t/16.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance

def projectiveRescaleProfile
    (G : ℝ → ℝ) (r : ℝ) : ℝ → ℝ :=
  fun u => G (r*u)

theorem projectiveRescaleProfile_continuous
    {G : ℝ → ℝ} (hG : Continuous G) (r : ℝ) :
    Continuous (projectiveRescaleProfile G r) := by
  unfold projectiveRescaleProfile
  fun_prop

theorem projectiveRescaleProfile_contDiff
    {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G) (r : ℝ) :
    ContDiff ℝ 2 (projectiveRescaleProfile G r) := by
  unfold projectiveRescaleProfile
  fun_prop

theorem projectiveRescaleProfile_compact
    {G : ℝ → ℝ} (hG : HasCompactSupport G)
    {r : ℝ} (hr : r ≠ 0) :
    HasCompactSupport (projectiveRescaleProfile G r) := by
  have hhomeo : Homeomorph ℝ ℝ :=
    Homeomorph.mulLeft₀ r hr
  simpa [projectiveRescaleProfile, hhomeo] using
    hG.comp_homeomorph hhomeo

theorem projectiveRescaleProfile_even
    {G : ℝ → ℝ} (hG : ∀ u, G (-u) = G u)
    (r u : ℝ) :
    projectiveRescaleProfile G r (-u)
      = projectiveRescaleProfile G r u := by
  unfold projectiveRescaleProfile
  have h : r * (-u) = -(r*u) := by ring
  rw [h, hG]

private theorem integral_rescale_mul
    {F : ℝ → ℝ} {r : ℝ} (hr : 0 < r) :
    (∫ u : ℝ, F (r*u))
      = (1/r) * ∫ x : ℝ, F x := by
  have h := Measure.integral_comp_mul_left F r
  have habs : |r⁻¹| = 1/r := by
    rw [abs_of_pos (inv_pos.mpr hr)]
    rfl
  simpa [habs, smul_eq_mul] using h

theorem evenResp_projectiveRescale
    {G : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (c : ℝ) :
    evenResp (projectiveRescaleProfile G r) 0 (c*r)
      = (1/r) * evenResp G 0 c := by
  unfold evenResp projectiveRescaleProfile
  simp only [zero_mul, Real.cosh_zero, one_mul]
  let F : ℝ → ℝ := fun x => G x * Real.cos (c*x)
  have hpoint :
      (fun u : ℝ => G (r*u) * Real.cos ((c*r)*u))
        = fun u => F (r*u) := by
    funext u
    dsimp [F]
    congr 2
    ring
  rw [hpoint, integral_rescale_mul hr]
  rfl

theorem projectiveSqEvenResp_rescale
    {G : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (c : ℝ) :
    projectiveSqEvenResp (projectiveRescaleProfile G r) (c*r)
      = (1/r^3) * projectiveSqEvenResp G c := by
  unfold projectiveSqEvenResp projectiveRescaleProfile
  have hr0 : r ≠ 0 := ne_of_gt hr
  let F : ℝ → ℝ := fun x => G x * x^2 * Real.cos (c*x)
  have hpoint :
      (fun u : ℝ => G (r*u) * u^2 * Real.cos ((c*r)*u))
        =
      fun u => (1/r^2) * F (r*u) := by
    funext u
    dsimp [F]
    field_simp [hr0]
    ring
  rw [hpoint, integral_const_mul, integral_rescale_mul hr]
  field_simp [hr0]
  ring

theorem projectiveFourthEvenResp_rescale
    {G : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (c : ℝ) :
    projectiveFourthEvenResp (projectiveRescaleProfile G r) (c*r)
      = (1/r^5) * projectiveFourthEvenResp G c := by
  unfold projectiveFourthEvenResp projectiveRescaleProfile
  have hr0 : r ≠ 0 := ne_of_gt hr
  let F : ℝ → ℝ := fun x => G x * x^4 * Real.cos (c*x)
  have hpoint :
      (fun u : ℝ => G (r*u) * u^4 * Real.cos ((c*r)*u))
        =
      fun u => (1/r^4) * F (r*u) := by
    funext u
    dsimp [F]
    field_simp [hr0]
    ring
  rw [hpoint, integral_const_mul, integral_rescale_mul hr]
  field_simp [hr0]
  ring

theorem projectiveBracketSecondMoment_rescale
    {G : ℝ → ℝ}
    (hG : Continuous G) (hGc : HasCompactSupport G)
    {r : ℝ} (hr : 0 < r) :
    projectiveBracketSecondMoment
        (projectiveRescaleProfile G r) r
      =
    (1/r^4) * projectiveBracketSecondMoment G 1 := by
  rw [projectiveBracketSecondMoment_eq_response_det
      (projectiveRescaleProfile_continuous hG r)
      (projectiveRescaleProfile_compact hGc hr.ne') r,
    projectiveBracketSecondMoment_eq_response_det hG hGc 1]
  rw [show r = (1:ℝ)*r by ring,
      show 2*r = (2:ℝ)*r by ring,
      evenResp_projectiveRescale hr 1,
      evenResp_projectiveRescale hr 2,
      projectiveSqEvenResp_rescale hr 1,
      projectiveSqEvenResp_rescale hr 2]
  field_simp [hr.ne']
  ring

theorem projectiveBracketFourthMoment_rescale
    {G : ℝ → ℝ}
    (hG : Continuous G) (hGc : HasCompactSupport G)
    {r : ℝ} (hr : 0 < r) :
    projectiveBracketFourthMoment
        (projectiveRescaleProfile G r) r
      =
    (1/r^6) * projectiveBracketFourthMoment G 1 := by
  rw [projectiveBracketFourthMoment_eq_response_det
      (projectiveRescaleProfile_continuous hG r)
      (projectiveRescaleProfile_compact hGc hr.ne') r,
    projectiveBracketFourthMoment_eq_response_det hG hGc 1]
  rw [show r = (1:ℝ)*r by ring,
      show 2*r = (2:ℝ)*r by ring,
      evenResp_projectiveRescale hr 1,
      evenResp_projectiveRescale hr 2,
      projectiveFourthEvenResp_rescale hr 1,
      projectiveFourthEvenResp_rescale hr 2]
  field_simp [hr.ne']
  ring

/--
The constructed normalized inhabitant transports to every positive physical
sampling radius.
-/
theorem exists_quartic_escape_at_radius
    {r : ℝ} (hr : 0 < r) :
    ∃ G : ℝ → ℝ,
      ContDiff ℝ 2 G
      ∧ HasCompactSupport G
      ∧ (∀ u, G (-u) = G u)
      ∧ projectiveBracketSecondMoment G r = 0
      ∧ projectiveBracketFourthMoment G r < 0 := by
  obtain ⟨R, lam, hR, hRone, hlam, hJ2, hJ4⟩ :=
    exists_smooth_quartic_escape_threeWindow
  let G0 := quarticThreeWindowProfile R lam
  let G := projectiveRescaleProfile G0 r
  have hG0c := quarticThreeWindowProfile_continuous (lam := lam) hR
  have hG0cd := quarticThreeWindowProfile_contDiff (lam := lam) hR
  have hG0k := quarticThreeWindowProfile_compact (lam := lam) hR
  have hG0e := quarticThreeWindowProfile_even R lam
  refine ⟨G, ?_, ?_, ?_, ?_, ?_⟩
  · exact projectiveRescaleProfile_contDiff hG0cd r
  · exact projectiveRescaleProfile_compact hG0k hr.ne'
  · intro u
    exact projectiveRescaleProfile_even hG0e r u
  · rw [show G = projectiveRescaleProfile G0 r by rfl,
        projectiveBracketSecondMoment_rescale hG0c hG0k hr,
        hJ2]
    ring
  · rw [show G = projectiveRescaleProfile G0 r by rfl,
        projectiveBracketFourthMoment_rescale hG0c hG0k hr]
    have hfac : 0 < 1/r^6 := by positivity
    exact mul_neg_of_pos_of_neg hfac hJ4

end Synthesis
