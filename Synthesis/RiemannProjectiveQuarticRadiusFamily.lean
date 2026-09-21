import Synthesis.RiemannProjectiveQuarticSmoothInhabitant

/-!
# A free-radius family of smooth quartic-escape detectors

The existing inhabitant theorem selected one convenient small window radius R.
The robustness inputs are stronger: the J2 endpoint signs and the uniform J4
negative margin hold for every sufficiently small positive R.

Therefore there is a fixed R0>0 such that every

  0 < R < R0

admits some lambda_R in [1/2,3/4] with

  J2(R,lambda_R)=0,
  J4(R,lambda_R)<0.

This retains one genuine design parameter after imposing the quartic moment
cancellation.  It is the natural parameter to use when studying the remaining
signed N-mu projective pairing.
-/

noncomputable section

open Set
open scoped Real

namespace Synthesis

theorem exists_radius_family_smooth_quartic_escape :
    ∃ R0 : ℝ, 0 < R0 ∧
      ∀ R : ℝ, 0 < R -> R < R0 ->
        ∃ lam : ℝ,
          lam ∈ Set.Icc (1/2 : ℝ) (3/4 : ℝ)
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

  obtain ⟨d2,hd2,hclose2⟩ :=
    exists_radius_quarticThreeWindowJ2_close_atomic heps2
  obtain ⟨d4,hd4,hclose4⟩ :=
    exists_radius_quarticThreeWindowJ4_close_atomic heps4

  let R0 : ℝ := min 1 (min d2 d4)
  have hR0 : 0 < R0 := by
    dsimp [R0]
    exact lt_min (by norm_num) (lt_min hd2 hd4)
  refine ⟨R0,hR0,?_⟩
  intro R hR hRR0

  have hRone : R < 1 :=
    hRR0.trans_le (min_le_left 1 (min d2 d4))
  have hRest : R < min d2 d4 :=
    hRR0.trans_le (min_le_right 1 (min d2 d4))
  have hRd2 : R < d2 :=
    hRest.trans_le (min_le_left d2 d4)
  have hRd4 : R < d4 :=
    hRest.trans_le (min_le_right d2 d4)

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
        <= quarticAtomicJAt (1/2) 2 := by
    unfold quarticJ2EndpointMargin
    exact min_le_left _ _
  have hmarginThree :
      quarticJ2EndpointMargin
        <= -quarticAtomicJAt (3/4) 2 := by
    unfold quarticJ2EndpointMargin
    exact min_le_right _ _

  have hhalfPos :
      0 < quarticThreeWindowJ R (1/2) 2 := by
    have hlo := (abs_le.mp hhalfClose).1
    dsimp [eps2] at hlo
    linarith [quarticJ2EndpointMargin_pos]
  have hthreeNeg :
      quarticThreeWindowJ R (3/4) 2 < 0 := by
    have hhi := (abs_le.mp hthreeClose).2
    dsimp [eps2] at hhi
    linarith [quarticJ2EndpointMargin_pos]

  have hcont :
      ContinuousOn
        (fun lam => quarticThreeWindowJ R lam 2)
        (Set.Icc (1/2 : ℝ) (3/4 : ℝ)) :=
    (quarticThreeWindowJ_continuous_lambda R 2).continuousOn
  have hab : (1/2 : ℝ) <= 3/4 := by norm_num
  have hzero :
      (0:ℝ) ∈
        Set.Icc
          (quarticThreeWindowJ R (3/4) 2)
          (quarticThreeWindowJ R (1/2) 2) :=
    ⟨hthreeNeg.le,hhalfPos.le⟩
  obtain ⟨lam,hlam,hlamzero⟩ :=
    intermediate_value_Icc' hab hcont hzero

  have h4close := hclose4 R lam hR hRd4 hlam
  have hatom4 :
      quarticAtomicJAt lam 4 <= -quarticJ4UniformMargin := by
    unfold quarticJ4UniformMargin
    exact quarticAtomicJAt_four_uniform_margin hlam.1
  have hsmooth4 :
      quarticThreeWindowJ R lam 4 < 0 := by
    have hhi := (abs_le.mp h4close).2
    dsimp [eps4] at hhi
    linarith [quarticJ4UniformMargin_pos]

  refine ⟨lam,hlam,?_,?_⟩
  · rw [projectiveBracketSecondMoment_threeWindow_one hR]
    exact hlamzero.symm
  · rw [projectiveBracketFourthMoment_threeWindow_one hR]
    exact hsmooth4

structure QuarticRadiusEscapeWitness (R : ℝ) where
  lam : ℝ
  lamMem : lam ∈ Set.Icc (1/2 : ℝ) (3/4 : ℝ)
  J2zero :
    projectiveBracketSecondMoment
      (quarticThreeWindowProfile R lam) 1 = 0
  J4neg :
    projectiveBracketFourthMoment
      (quarticThreeWindowProfile R lam) 1 < 0

theorem exists_quarticRadiusEscapeWitness_family :
    ∃ R0 : ℝ, 0 < R0 ∧
      ∀ R : ℝ, 0 < R -> R < R0 ->
        Nonempty (QuarticRadiusEscapeWitness R) := by
  obtain ⟨R0,hR0,hfam⟩ :=
    exists_radius_family_smooth_quartic_escape
  refine ⟨R0,hR0,?_⟩
  intro R hR hRR
  obtain ⟨lam,hlam,hJ2,hJ4⟩ := hfam R hR hRR
  exact ⟨{
    lam := lam
    lamMem := hlam
    J2zero := hJ2
    J4neg := hJ4
  }⟩

end Synthesis
