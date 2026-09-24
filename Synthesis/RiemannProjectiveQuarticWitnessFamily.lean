import Synthesis.RiemannProjectiveQuarticHighCluster
import Synthesis.RiemannProjectiveQuarticThreeWindowRobustness
import Mathlib.Topology.Order.IntermediateValue

/-!
# A genuine one-parameter family of smooth quartic high witnesses

The existing inhabitant theorem chooses one sufficiently small window radius R.
The robustness estimates are uniform, so in fact every sufficiently small
positive R admits a coefficient lambda_R in [1/2,3/4] with

  J2(R,lambda_R)=0,
  J4(R,lambda_R)<0.

Consequently every sufficiently small R carries a QuarticHighWitness.  This is
the parameter freedom needed by the multi-detector orthogonalization lane:
three witnesses may be selected at distinct radii and their complete base/pole
channel ratios compared.

No claim about those ratios is made here.
-/

noncomputable section

open Set
open scoped Real

namespace Synthesis

/--
Uniform small-radius family of exact smooth quartic-escape profiles.
-/
theorem exists_quarticWitness_radius_threshold :
    ∃ d : ℝ, 0 < d ∧
      ∀ R : ℝ, 0 < R → R < d →
        ∃ W : QuarticHighWitness, W.R = R := by
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

  let d : ℝ := min 1 (min d2 d4)
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (by norm_num) (lt_min hd2 hd4)

  refine ⟨d, hd, ?_⟩
  intro R hR hRd
  have hRone : R < 1 := by
    have hle : d <= 1 := by
      dsimp [d]
      exact min_le_left _ _
    exact hRd.trans_le hle
  have hRmin : R < min d2 d4 := by
    have hle : d <= min d2 d4 := by
      dsimp [d]
      exact min_le_right _ _
    exact hRd.trans_le hle
  have hRd2 : R < d2 := hRmin.trans_le (min_le_left _ _)
  have hRd4 : R < d4 := hRmin.trans_le (min_le_right _ _)

  have hhalfMem : (1/2 : ℝ) ∈ Set.Icc (1/2 : ℝ) (3/4 : ℝ) := by
    constructor <;> norm_num
  have hthreeMem : (3/4 : ℝ) ∈ Set.Icc (1/2 : ℝ) (3/4 : ℝ) := by
    constructor <;> norm_num

  have hhalfClose :=
    hclose2 R (1/2) hR hRd2 hhalfMem
  have hthreeClose :=
    hclose2 R (3/4) hR hRd2 hthreeMem

  have hmarginHalf :
      quarticJ2EndpointMargin <= quarticAtomicJAt (1/2) 2 := by
    unfold quarticJ2EndpointMargin
    exact min_le_left _ _
  have hmarginThree :
      quarticJ2EndpointMargin <= - quarticAtomicJAt (3/4) 2 := by
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
  have hab : (1/2 : ℝ) <= 3/4 := by norm_num
  have hzero :
      (0 : ℝ) ∈
        Set.Icc
          (quarticThreeWindowJ R (3/4) 2)
          (quarticThreeWindowJ R (1/2) 2) :=
    ⟨hthreeNeg.le, hhalfPos.le⟩
  obtain ⟨lam, hlam, hlamzero⟩ :=
    intermediate_value_Icc' hab hcont hzero

  have h4close := hclose4 R lam hR hRd4 hlam
  have hatom4 :
      quarticAtomicJAt lam 4 <= - quarticJ4UniformMargin := by
    unfold quarticJ4UniformMargin
    exact quarticAtomicJAt_four_uniform_margin hlam.1
  have hsmooth4 : quarticThreeWindowJ R lam 4 < 0 := by
    have hhi := (abs_le.mp h4close).2
    dsimp [eps4] at hhi
    linarith [quarticJ4UniformMargin_pos]

  have hJ2 :
      projectiveBracketSecondMoment
        (quarticThreeWindowProfile R lam) 1 = 0 := by
    rw [projectiveBracketSecondMoment_threeWindow_one hR]
    exact hlamzero.symm
  have hJ4 :
      projectiveBracketFourthMoment
        (quarticThreeWindowProfile R lam) 1 < 0 := by
    rw [projectiveBracketFourthMoment_threeWindow_one hR]
    exact hsmooth4

  have hc := quarticThreeWindowProfile_continuous (lam := lam) hR
  have hk := quarticThreeWindowProfile_compact (lam := lam) hR
  obtain ⟨eps, heps, hband⟩ :=
    exists_heightDefect_pos_punctured_of_quartic_escape
      hc hk hJ2 hJ4

  let W : QuarticHighWitness := {
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
  }
  exact ⟨W, rfl⟩

/--
There are quartic witnesses at three distinct radii.  This is the minimal
existence input for the three-channel base/pole orthogonalization problem.
-/
theorem exists_three_quarticHighWitness_distinct_radii :
    ∃ W1 W2 W3 : QuarticHighWitness,
      W1.R ≠ W2.R ∧ W1.R ≠ W3.R ∧ W2.R ≠ W3.R := by
  obtain ⟨d, hd, hfamily⟩ := exists_quarticWitness_radius_threshold
  let R1 := d/4
  let R2 := d/3
  let R3 := d/2
  have hR1 : 0 < R1 := by dsimp [R1]; positivity
  have hR2 : 0 < R2 := by dsimp [R2]; positivity
  have hR3 : 0 < R3 := by dsimp [R3]; positivity
  have hR1d : R1 < d := by dsimp [R1]; linarith
  have hR2d : R2 < d := by dsimp [R2]; linarith
  have hR3d : R3 < d := by dsimp [R3]; linarith
  obtain ⟨W1, hW1⟩ := hfamily R1 hR1 hR1d
  obtain ⟨W2, hW2⟩ := hfamily R2 hR2 hR2d
  obtain ⟨W3, hW3⟩ := hfamily R3 hR3 hR3d
  refine ⟨W1,W2,W3,?_,?_,?_⟩
  · intro h
    have := congrArg QuarticHighWitness.R h
    rw [hW1,hW2] at this
    dsimp [R1,R2] at this
    nlinarith
  · intro h
    have := congrArg QuarticHighWitness.R h
    rw [hW1,hW3] at this
    dsimp [R1,R3] at this
    nlinarith
  · intro h
    have := congrArg QuarticHighWitness.R h
    rw [hW2,hW3] at this
    dsimp [R2,R3] at this
    nlinarith

end Synthesis
