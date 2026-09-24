import Synthesis.RiemannProjectiveQuarticFourWindowSmoothFamily
import Synthesis.RiemannProjectiveQuarticPhysicalRescale
import Synthesis.RiemannProjectiveQuarticTargetLocalSign
import Synthesis.RiemannProjectiveQuarticPhysicalSupport
import Zeta23Bridge.LiteralWeilSameOrdinateEvenCone

/-!
# Four-window quartic witnesses on the actual high-zero consumer

The smooth four-window family leaves lambda free after exact J2 cancellation.
This file promotes those moment witnesses to the same high-ordinate geometry
used by the three-window quartic lane.

For a normalized profile G_{R,lambda,mu}, rescale by r=t/16:

  G_t(u) = G_{R,lambda,mu}((t/16)u).

The exact rescaling theorem transports the local positive height detector to the
whole critical strip once 8/t is inside its punctured target band.

The extra window is centred at pi, so the normalized support lies in
|v| < pi + R < pi+1.  For t>=200 the physical support is safely below log 2;
this intentionally conservative threshold is immaterial for the Clay high-zero
range.

Thus a four-window witness has:
* exact prime invisibility;
* nonnegative same-ordinate cluster;
* strictly positive off-line target;
* one genuine free design parameter lambda.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector

def quarticFourPhysicalDetector
    (R lam mu t : ℝ) : ℝ -> ℝ :=
  projectiveRescaleProfile
    (quarticFourWindowProfile R lam mu) (t/16)

theorem quarticFourWindowProfile_support_abs_lt
    {R lam mu u : ℝ} (hR : 0 < R)
    (hu : quarticFourWindowProfile R lam mu u ≠ 0) :
    |u| < Real.pi + R := by
  have hm : quarticWindowMass R ≠ 0 :=
    ne_of_gt (quarticWindowMass_pos hR)
  have hraw : quarticFourWindowRaw R lam mu u ≠ 0 := by
    intro hz
    apply hu
    unfold quarticFourWindowProfile
    rw [hz]
    ring
  by_contra hbad
  have hge : Real.pi + R <= |u| := le_of_not_gt hbad
  have h0 : quantitativeSymBump 0 R u = 0 := by
    by_contra h
    have hs := quantitativeSymBump_support_abs_lt hR h
    simp only [abs_zero, zero_add] at hs
    have hp : 0 < Real.pi := Real.pi_pos
    linarith
  have h1 : quantitativeSymBump (Real.pi/3) R u = 0 := by
    by_contra h
    have hs := quantitativeSymBump_support_abs_lt hR h
    rw [abs_of_pos (by positivity : 0 < Real.pi/3)] at hs
    have hp := Real.pi_pos
    linarith
  have h2 : quantitativeSymBump (Real.pi/2) R u = 0 := by
    by_contra h
    have hs := quantitativeSymBump_support_abs_lt hR h
    rw [abs_of_pos (by positivity : 0 < Real.pi/2)] at hs
    have hp := Real.pi_pos
    linarith
  have h3 : quantitativeSymBump Real.pi R u = 0 := by
    by_contra h
    have hs := quantitativeSymBump_support_abs_lt hR h
    rw [abs_of_pos Real.pi_pos] at hs
    linarith
  unfold quarticFourWindowRaw at hraw
  rw [h0,h1,h2,h3] at hraw
  simp at hraw

theorem quarticFourPhysicalDetector_contDiff
    {R lam mu t : ℝ} (hR : 0 < R) :
    ContDiff ℝ 2 (quarticFourPhysicalDetector R lam mu t) := by
  unfold quarticFourPhysicalDetector
  exact projectiveRescaleProfile_contDiff
    (quarticFourWindowProfile_contDiff (lam:=lam) (mu:=mu) hR) (t/16)

theorem quarticFourPhysicalDetector_compact
    {R lam mu t : ℝ} (hR : 0 < R) (ht : 0 < t) :
    HasCompactSupport (quarticFourPhysicalDetector R lam mu t) := by
  unfold quarticFourPhysicalDetector
  exact projectiveRescaleProfile_compact
    (quarticFourWindowProfile_compact (lam:=lam) (mu:=mu) hR)
    (by positivity : t/16 ≠ 0)

theorem quarticFourPhysicalDetector_even
    (R lam mu t u : ℝ) :
    quarticFourPhysicalDetector R lam mu t (-u)
      = quarticFourPhysicalDetector R lam mu t u := by
  unfold quarticFourPhysicalDetector
  exact projectiveRescaleProfile_even
    (quarticFourWindowProfile_even R lam mu) (t/16) u

theorem quarticFourPhysicalDetector_support_abs_lt
    {R lam mu t u : ℝ}
    (hR : 0 < R) (hRone : R < 1)
    (ht : 0 < t)
    (hu : quarticFourPhysicalDetector R lam mu t u ≠ 0) :
    |u| < 16 * (Real.pi + 1) / t := by
  have hr : 0 < t/16 := by positivity
  have hs := quarticFourWindowProfile_support_abs_lt hR hu
  unfold quarticFourPhysicalDetector projectiveRescaleProfile at hu
  have hs' := quarticFourWindowProfile_support_abs_lt hR hu
  have habs : |(t/16)*u| = (t/16)*|u| := by
    rw [abs_mul, abs_of_pos hr]
  rw [habs] at hs'
  rw [lt_div_iff₀ ht]
  nlinarith

theorem quarticFourPhysicalDetector_short_of_twoHundred
    {R lam mu t : ℝ}
    (hR : 0 < R) (hRone : R < 1)
    (ht : 200 <= t) :
    ∀ u, quarticFourPhysicalDetector R lam mu t u ≠ 0 ->
      |u| < Real.log 2 := by
  intro u hu
  have htpos : 0 < t := by linarith
  have hs :=
    quarticFourPhysicalDetector_support_abs_lt
      hR hRone htpos hu
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hbound :
      16 * (Real.pi + 1) / t < (2/5 : ℝ) := by
    rw [div_lt_iff₀ htpos]
    nlinarith
  have hlog : (2/5 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  exact hs.trans (hbound.trans hlog)

structure QuarticFourHighWitness where
  R : ℝ
  lam : ℝ
  mu : ℝ
  eps : ℝ
  Rpos : 0 < R
  RltOne : R < 1
  lamMem : lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ)
  muAbs : |mu| < 1/10
  epsPos : 0 < eps
  J2zero :
    projectiveBracketSecondMoment
      (quarticFourWindowProfile R lam mu) 1 = 0
  J4neg :
    projectiveBracketFourthMoment
      (quarticFourWindowProfile R lam mu) 1 < 0
  targetBand :
    ∀ a : ℝ, 0 < |a| -> |a| < eps ->
      0 <
      heightDefect
        (quarticFourWindowProfile R lam mu) 1 a 0

/--
Every sufficiently small radius and every lambda in the free interval produces
an actual four-window high witness.
-/
theorem exists_quarticFourHighWitness_family :
    ∃ R0 : ℝ, 0 < R0 ∧
      ∀ R lam : ℝ,
        0 < R -> R < R0 ->
        lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) ->
        Nonempty QuarticFourHighWitness := by
  obtain ⟨Rraw,hRraw,hfam⟩ :=
    exists_uniform_smooth_quarticFourWindow_family
  let R0 : ℝ := min Rraw 1
  have hR0 : 0 < R0 := by
    dsimp [R0]
    exact lt_min hRraw (by norm_num)
  refine ⟨R0,hR0,?_⟩
  intro R lam hR hRR hlam
  have hRraw' : R < Rraw :=
    hRR.trans_le (by
      dsimp [R0]
      exact min_le_left _ _)
  have hRone : R < 1 :=
    hRR.trans_le (by
      dsimp [R0]
      exact min_le_right _ _)
  obtain ⟨S⟩ := hfam R lam hR hRraw' hlam
  have hc :=
    quarticFourWindowProfile_continuous
      (lam:=lam) (mu:=S.mu) hR
  have hk :=
    quarticFourWindowProfile_compact
      (lam:=lam) (mu:=S.mu) hR
  obtain ⟨eps,heps,hband⟩ :=
    exists_heightDefect_pos_punctured_of_quartic_escape
      hc hk S.J2zero S.J4neg
  exact ⟨{
    R := R
    lam := lam
    mu := S.mu
    eps := eps
    Rpos := hR
    RltOne := hRone
    lamMem := hlam
    muAbs := S.muAbs
    epsPos := heps
    J2zero := S.J2zero
    J4neg := S.J4neg
    targetBand := hband
  }⟩

theorem QuarticFourHighWitness.normalized_height_lt
    (W : QuarticFourHighWitness)
    {t : ℝ} (ht : 0 < t)
    (hhigh : 8/t < W.eps)
    (rho : Zeros) :
    |heightOf rho / (t/16)| < W.eps := by
  have hstrip := zetaZero_height_abs_le_half rho
  have hr : 0 < t/16 := by positivity
  rw [abs_div, abs_of_pos hr]
  have hscale : |heightOf rho| / (t/16) <= 8/t := by
    rw [div_le_div_iff₀ hr ht]
    nlinarith
  exact hscale.trans_lt hhigh

theorem QuarticFourHighWitness.zeroHeightDefect_nonneg
    (W : QuarticFourHighWitness)
    {t : ℝ} (ht : 0 < t)
    (hhigh : 8/t < W.eps)
    (rho : Zeros) :
    0 <=
      zeroHeightDefect
        (quarticFourPhysicalDetector W.R W.lam W.mu t)
        (t/16) rho := by
  unfold zeroHeightDefect
  by_cases ha : heightOf rho = 0
  · rw [ha, heightDefect_self]
  · have hr : 0 < t/16 := by positivity
    have hnorm0 : 0 < |heightOf rho / (t/16)| := by
      rw [abs_pos]
      exact div_ne_zero ha hr.ne'
    have hnormlt := W.normalized_height_lt ht hhigh rho
    have hpos :=
      W.targetBand (heightOf rho/(t/16)) hnorm0 hnormlt
    rw [heightDefect_projectiveRescale_zero hr (heightOf rho)]
    have hfac : 0 < 1/(t/16)^2 := by positivity
    have hm : 0 < ((zetaZeroConfig).mult (rho : ℂ) : ℝ) := by positivity
    unfold quarticFourPhysicalDetector
    exact mul_nonneg hm.le (mul_pos hfac hpos).le

theorem QuarticFourHighWitness.zeroHeightDefect_pos_of_offLine
    (W : QuarticFourHighWitness)
    {t : ℝ} (ht : 0 < t)
    (hhigh : 8/t < W.eps)
    (rho : Zeros)
    (hoff : heightOf rho ≠ 0) :
    0 <
      zeroHeightDefect
        (quarticFourPhysicalDetector W.R W.lam W.mu t)
        (t/16) rho := by
  unfold zeroHeightDefect
  have hr : 0 < t/16 := by positivity
  have hnorm0 : 0 < |heightOf rho/(t/16)| := by
    rw [abs_pos]
    exact div_ne_zero hoff hr.ne'
  have hnormlt := W.normalized_height_lt ht hhigh rho
  have hpos :=
    W.targetBand (heightOf rho/(t/16)) hnorm0 hnormlt
  rw [heightDefect_projectiveRescale_zero hr (heightOf rho)]
  have hfac : 0 < 1/(t/16)^2 := by positivity
  have hm : 0 < ((zetaZeroConfig).mult (rho : ℂ) : ℝ) := by positivity
  unfold quarticFourPhysicalDetector
  exact mul_pos hm (mul_pos hfac hpos)

end Synthesis
