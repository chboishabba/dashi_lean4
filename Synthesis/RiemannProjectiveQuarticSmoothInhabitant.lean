import Synthesis.RiemannProjectiveQuarticThreeWindowRobustness
import Synthesis.RiemannProjectiveQuarticBaseLocalSign
import Synthesis.RiemannProjectiveQuarticTargetLocalSign
import Mathlib.Topology.Order.IntermediateValue

/-!
# An actual smooth quartic-escape projective detector

The atomic three-radius family has:
* J2(1/2)>0,
* J2(3/4)<0,
* a uniform strictly negative J4 margin on [1/2,3/4].

Uniform localization transports those statements to every sufficiently narrow
smooth three-window profile.  Continuity in lambda and the intermediate value
theorem then produce an exact smooth coefficient lambda_R with

  J2(G_{R,lambda_R},1)=0,
  J4(G_{R,lambda_R},1)<0.

The existing fourth-order sign compilers immediately yield:
* a two-sided punctured negative q-base lobe;
* a two-sided punctured positive target-height defect.

This is the first literal C^2 compactly-supported inhabitant of the quartic
escape.  It intentionally leaves the old nonnegative GateData class.
-/

noncomputable section

open Set
open scoped Real

namespace Synthesis

def quarticJ2EndpointMargin : ℝ :=
  min
    (quarticAtomicJAt (1/2) 2)
    (- quarticAtomicJAt (3/4) 2)

def quarticJ4UniformMargin : ℝ :=
  11 * Real.pi^4 / 1728

theorem quarticJ2EndpointMargin_pos :
    0 < quarticJ2EndpointMargin := by
  unfold quarticJ2EndpointMargin
  exact lt_min
    quarticAtomicJAt_two_half_pos
    (neg_pos.mpr quarticAtomicJAt_two_three_quarters_neg)

theorem quarticJ4UniformMargin_pos :
    0 < quarticJ4UniformMargin := by
  unfold quarticJ4UniformMargin
  positivity

theorem quarticThreeWindowJ_continuous_lambda
    (R : ℝ) (k : ℕ) :
    Continuous (fun lam => quarticThreeWindowJ R lam k) := by
  unfold quarticThreeWindowJ quarticThreeWindowMomentResp
    quarticThreeWindowPairing
  fun_prop

/--
Existence of a literal smooth moment-cancelled quartic-escape profile.
-/
theorem exists_smooth_quartic_escape_threeWindow :
    ∃ R lam : ℝ,
      0 < R
      ∧ R < 1
      ∧ lam ∈ Set.Icc (1/2 : ℝ) (3/4 : ℝ)
      ∧ projectiveBracketSecondMoment
          (quarticThreeWindowProfile R lam) 1 = 0
      ∧ projectiveBracketFourthMoment
          (quarticThreeWindowProfile R lam) 1 < 0 := by
  let eps2 : ℝ := quarticJ2EndpointMargin / 2
  let eps4 : ℝ := quarticJ4UniformMargin / 2
  have heps2 : 0 < eps2 := by
    dsimp [eps2]
    linarith [quarticJ2EndpointMargin_pos]
  have heps4 : 0 < eps4 := by
    dsimp [eps4]
    linarith [quarticJ4UniformMargin_pos]

  obtain ⟨d2, hd2, hclose2⟩ :=
    exists_radius_quarticThreeWindowJ2_close_atomic heps2
  obtain ⟨d4, hd4, hclose4⟩ :=
    exists_radius_quarticThreeWindowJ4_close_atomic heps4

  let R : ℝ := min 1 (min d2 d4) / 2
  have hmin : 0 < min 1 (min d2 d4) := by
    exact lt_min (by norm_num) (lt_min hd2 hd4)
  have hR : 0 < R := by
    dsimp [R]
    linarith
  have hRone : R < 1 := by
    dsimp [R]
    have hm := min_le_left (1 : ℝ) (min d2 d4)
    linarith
  have hRrest : R < min d2 d4 := by
    dsimp [R]
    have hm := min_le_right (1 : ℝ) (min d2 d4)
    linarith
  have hRd2 : R < d2 :=
    hRrest.trans_le (min_le_left d2 d4)
  have hRd4 : R < d4 :=
    hRrest.trans_le (min_le_right d2 d4)

  have hhalfMem : (1/2 : ℝ) ∈ Set.Icc (1/2 : ℝ) (3/4 : ℝ) := by
    constructor <;> norm_num
  have hthreeMem : (3/4 : ℝ) ∈ Set.Icc (1/2 : ℝ) (3/4 : ℝ) := by
    constructor <;> norm_num

  have hhalfClose :=
    hclose2 R (1/2) hR hRd2 hhalfMem
  have hthreeClose :=
    hclose2 R (3/4) hR hRd2 hthreeMem

  have hmarginHalf :
      quarticJ2EndpointMargin
        ≤ quarticAtomicJAt (1/2) 2 := by
    unfold quarticJ2EndpointMargin
    exact min_le_left _ _
  have hmarginThree :
      quarticJ2EndpointMargin
        ≤ - quarticAtomicJAt (3/4) 2 := by
    unfold quarticJ2EndpointMargin
    exact min_le_right _ _

  have hhalfPos : 0 < quarticThreeWindowJ R (1/2) 2 := by
    have hlo := (abs_le.mp hhalfClose).1
    dsimp [eps2] at hlo
    linarith [quarticJ2EndpointMargin_pos]
  have hthreeNeg : quarticThreeWindowJ R (3/4) 2 < 0 := by
    have hhi := (abs_le.mp hthreeClose).2
    dsimp [eps2] at hhi
    linarith [quarticJ2EndpointMargin_pos]

  have hcont :
      ContinuousOn
        (fun lam => quarticThreeWindowJ R lam 2)
        (Set.Icc (1/2 : ℝ) (3/4 : ℝ)) :=
    (quarticThreeWindowJ_continuous_lambda R 2).continuousOn
  have hab : (1/2 : ℝ) ≤ 3/4 := by norm_num
  have hzero :
      (0 : ℝ) ∈
        Set.Icc
          (quarticThreeWindowJ R (3/4) 2)
          (quarticThreeWindowJ R (1/2) 2) :=
    ⟨hthreeNeg.le, hhalfPos.le⟩
  have himage :=
    intermediate_value_Icc' hab hcont hzero
  rcases himage with ⟨lam, hlam, hlamzero⟩

  have h4close := hclose4 R lam hR hRd4 hlam
  have hatom4 :
      quarticAtomicJAt lam 4 ≤ - quarticJ4UniformMargin := by
    unfold quarticJ4UniformMargin
    exact quarticAtomicJAt_four_uniform_margin hlam.1
  have hsmooth4 : quarticThreeWindowJ R lam 4 < 0 := by
    have hhi := (abs_le.mp h4close).2
    dsimp [eps4] at hhi
    linarith [quarticJ4UniformMargin_pos]

  refine ⟨R, lam, hR, hRone, hlam, ?_, ?_⟩
  · rw [projectiveBracketSecondMoment_threeWindow_one hR]
    exact hlamzero.symm
  · rw [projectiveBracketFourthMoment_threeWindow_one hR]
    exact hsmooth4

/--
The inhabitant already exposes the two local observables needed by the quartic
route.
-/
theorem exists_smooth_quartic_escape_with_local_signs :
    ∃ R lam : ℝ,
      0 < R
      ∧ R < 1
      ∧ lam ∈ Set.Icc (1/2 : ℝ) (3/4 : ℝ)
      ∧ (∃ eps : ℝ, 0 < eps ∧
          ∀ q : ℝ, 0 < |q| → |q| < eps →
            genericProjectiveBaseKernel
              (quarticThreeWindowProfile R lam) 1 q < 0)
      ∧ (∃ eps : ℝ, 0 < eps ∧
          ∀ a : ℝ, 0 < |a| → |a| < eps →
            0 <
            Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.heightDefect
              (quarticThreeWindowProfile R lam) 1 a 0) := by
  obtain ⟨R, lam, hR, hRone, hlam, hJ2, hJ4⟩ :=
    exists_smooth_quartic_escape_threeWindow
  have hc := quarticThreeWindowProfile_continuous (lam := lam) hR
  have hk := quarticThreeWindowProfile_compact (lam := lam) hR
  have hbase :=
    exists_genericProjectiveBaseKernel_neg_punctured_of_quartic_escape
      hc hk hJ2 hJ4
  have htarget :=
    exists_heightDefect_pos_punctured_of_quartic_escape
      hc hk hJ2 hJ4
  exact ⟨R, lam, hR, hRone, hlam, hbase, htarget⟩

end Synthesis
