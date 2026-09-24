import Synthesis.RiemannProjectiveQuarticPhysicalSupport
import Synthesis.RiemannProjectiveQuarticSmoothInhabitant
import Zeta23Bridge.LiteralWeilSameOrdinateEvenCone

/-!
# High-ordinate same-fibre positivity for the signed quartic detector

Leaving GateData loses the old global nonnegative-taper argument, but the
quartic detector has a different high-ordinate mechanism.

Every zeta zero lies in the closed strip 0 <= Re rho <= 1, so its signed height

  a_rho = Re rho - 1/2

satisfies |a_rho| <= 1/2.

For the physical sample radius r=t/16, exact rescaling gives

  D_{G_r,r}(a,0) = r^{-2} D_{G,1}(a/r,0).

The fixed normalized quartic witness has a punctured positive target band
|alpha|<eps_Q.  Hence whenever 8/t<eps_Q, every same-ordinate zero lies in
that band after normalization:
  |a_rho/r| <= 8/t < eps_Q.

Thus all same-ordinate defects are nonnegative, and every off-line one is
strictly positive.  This recovers the cluster sign needed by the reflection-pair
argument without requiring the signed taper to inhabit GateData.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector

def quarticPhysicalDetector
    (R lam t : ℝ) : ℝ → ℝ :=
  projectiveRescaleProfile
    (quarticThreeWindowProfile R lam) (t/16)

theorem zetaZero_height_abs_le_half
    (rho : Zeros) :
    |heightOf rho| ≤ 1/2 := by
  have hs :=
    (zetaZeroConfig).strip (rho : ℂ) rho.property
  unfold heightOf
  rw [abs_le]
  constructor <;> linarith [hs.1, hs.2]

theorem quarticPhysicalDetector_contDiff
    {R lam t : ℝ} (hR : 0 < R) :
    ContDiff ℝ 2 (quarticPhysicalDetector R lam t) := by
  unfold quarticPhysicalDetector
  exact projectiveRescaleProfile_contDiff
    (quarticThreeWindowProfile_contDiff (lam := lam) hR) (t/16)

theorem quarticPhysicalDetector_compact
    {R lam t : ℝ} (hR : 0 < R) (ht : 0 < t) :
    HasCompactSupport (quarticPhysicalDetector R lam t) := by
  unfold quarticPhysicalDetector
  exact projectiveRescaleProfile_compact
    (quarticThreeWindowProfile_compact (lam := lam) hR)
    (by positivity : t/16 ≠ 0)

theorem quarticPhysicalDetector_even
    (R lam t u : ℝ) :
    quarticPhysicalDetector R lam t (-u)
      = quarticPhysicalDetector R lam t u := by
  unfold quarticPhysicalDetector
  exact projectiveRescaleProfile_even
    (quarticThreeWindowProfile_even R lam) (t/16) u

/--
A fixed normalized quartic witness together with its positive local height band.
-/
structure QuarticHighWitness where
  R : ℝ
  lam : ℝ
  eps : ℝ
  Rpos : 0 < R
  RltOne : R < 1
  lamMem : lam ∈ Set.Icc (1/2 : ℝ) (3/4 : ℝ)
  epsPos : 0 < eps
  J2zero :
    projectiveBracketSecondMoment
      (quarticThreeWindowProfile R lam) 1 = 0
  J4neg :
    projectiveBracketFourthMoment
      (quarticThreeWindowProfile R lam) 1 < 0
  targetBand :
    ∀ a : ℝ, 0 < |a| → |a| < eps →
      0 <
      heightDefect
        (quarticThreeWindowProfile R lam) 1 a 0

theorem exists_quarticHighWitness :
    ∃ W : QuarticHighWitness, True := by
  obtain ⟨R, lam, hR, hRone, hlam, hJ2, hJ4⟩ :=
    exists_smooth_quartic_escape_threeWindow
  have hc := quarticThreeWindowProfile_continuous (lam := lam) hR
  have hk := quarticThreeWindowProfile_compact (lam := lam) hR
  obtain ⟨eps, heps, hband⟩ :=
    exists_heightDefect_pos_punctured_of_quartic_escape
      hc hk hJ2 hJ4
  refine ⟨{
    R := R
    lam := lam
    eps := eps
    Rpos := hR
    RltOne := hRone
    lamMem := hlam
    epsPos := heps
    J2zero := hJ2
    J4neg := hJ4
    targetBand := hband
  }, trivial⟩

theorem QuarticHighWitness.normalized_height_lt
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t)
    (hhigh : 8/t < W.eps)
    (rho : Zeros) :
    |heightOf rho / (t/16)| < W.eps := by
  have hstrip := zetaZero_height_abs_le_half rho
  have hr : 0 < t/16 := by positivity
  rw [abs_div, abs_of_pos hr]
  have hscale :
      |heightOf rho| / (t/16) ≤ 8/t := by
    rw [div_le_div_iff₀ hr ht]
    nlinarith
  exact hscale.trans_lt hhigh

theorem QuarticHighWitness.zeroHeightDefect_nonneg
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t)
    (hhigh : 8/t < W.eps)
    (rho : Zeros) :
    0 ≤
      zeroHeightDefect
        (quarticPhysicalDetector W.R W.lam t)
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
      W.targetBand
        (heightOf rho / (t/16)) hnorm0 hnormlt
    rw [heightDefect_projectiveRescale_zero hr (heightOf rho)]
    have hfac : 0 < 1/(t/16)^2 := by positivity
    have hm : 0 < ((zetaZeroConfig).mult (rho : ℂ) : ℝ) := by
      positivity
    unfold quarticPhysicalDetector
    exact mul_nonneg hm.le (mul_pos hfac hpos).le

theorem QuarticHighWitness.zeroHeightDefect_pos_of_offLine
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t)
    (hhigh : 8/t < W.eps)
    (rho : Zeros)
    (hoff : heightOf rho ≠ 0) :
    0 <
      zeroHeightDefect
        (quarticPhysicalDetector W.R W.lam t)
        (t/16) rho := by
  unfold zeroHeightDefect
  have hr : 0 < t/16 := by positivity
  have hnorm0 : 0 < |heightOf rho / (t/16)| := by
    rw [abs_pos]
    exact div_ne_zero hoff hr.ne'
  have hnormlt := W.normalized_height_lt ht hhigh rho
  have hpos :=
    W.targetBand
      (heightOf rho / (t/16)) hnorm0 hnormlt
  rw [heightDefect_projectiveRescale_zero hr (heightOf rho)]
  have hfac : 0 < 1/(t/16)^2 := by positivity
  have hm : 0 < ((zetaZeroConfig).mult (rho : ℂ) : ℝ) := by
    positivity
  unfold quarticPhysicalDetector
  exact mul_pos hm (mul_pos hfac hpos)

end Synthesis
