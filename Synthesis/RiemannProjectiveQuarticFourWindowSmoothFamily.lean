import Synthesis.RiemannProjectiveQuarticFourWindowRobustness
import Synthesis.RiemannProjectiveQuarticFourWindowAtomicCorridor
import Mathlib.Topology.Order.IntermediateValue

/-!
# Smooth one-parameter four-window quartic-escape family

Uniform moment robustness plus the atomic corridor gives a genuine smooth
one-parameter family.

There exists R0>0 such that for every 0<R<R0 and every

  lambda in [1/2,2/3]

there is a coefficient mu near the atomic null value mu0(lambda) satisfying

  J2(G_{R,lambda,mu},1)=0,
  J4(G_{R,lambda,mu},1)<0.

Moreover

  |mu-mu0(lambda)| <= 1/10000,
  |mu| < 1/10.

Thus lambda survives as a free design parameter after exact smooth quartic
moment cancellation.  This is the parameter space on which the remaining
signed N-mu functional can be optimized or annihilated.
-/

noncomputable section

open Set
open scoped Real

namespace Synthesis

theorem quarticFourWindowJ_continuous_mu
    (R lam : ℝ) (k : ℕ) :
    Continuous (fun mu => quarticFourWindowJ R lam mu k) := by
  unfold quarticFourWindowJ quarticFourWindowMomentResp
    quarticFourWindowPairing normalizedSymBumpPairing
  fun_prop

structure SmoothQuarticFourWindowWitness
    (R lam : ℝ) where
  mu : ℝ
  muNear :
    |mu-quarticFourAtomicMu lam|
      <= quarticFourAtomicMuRadius
  muAbs : |mu| < 1/10
  J2zero :
    projectiveBracketSecondMoment
      (quarticFourWindowProfile R lam mu) 1 = 0
  J4neg :
    projectiveBracketFourthMoment
      (quarticFourWindowProfile R lam mu) 1 < 0

theorem exists_uniform_smooth_quarticFourWindow_family :
    ∃ R0 : ℝ, 0 < R0 ∧
      ∀ R lam : ℝ,
        0 < R -> R < R0 ->
        lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) ->
        Nonempty (SmoothQuarticFourWindowWitness R lam) := by
  let eps2 : ℝ := quarticFourAtomicJ2CorridorMargin / 2
  let eps4 : ℝ := quarticFourAtomicJ4CorridorMargin / 2
  have heps2 : 0 < eps2 := by
    dsimp [eps2]
    linarith [quarticFourAtomicJ2CorridorMargin_pos]
  have heps4 : 0 < eps4 := by
    dsimp [eps4]
    linarith [quarticFourAtomicJ4CorridorMargin_pos]

  obtain ⟨d2,hd2,hclose2⟩ :=
    exists_radius_quarticFourWindowJ2_close_atomic heps2
  obtain ⟨d4,hd4,hclose4⟩ :=
    exists_radius_quarticFourWindowJ4_close_atomic heps4

  let R0 : ℝ := min 1 (min d2 d4)
  have hR0 : 0 < R0 := by
    dsimp [R0]
    exact lt_min (by norm_num) (lt_min hd2 hd4)
  refine ⟨R0,hR0,?_⟩
  intro R lam hR hRR hlam

  have hRd2 :
      R < d2 := by
    have hrest :
        R < min d2 d4 :=
      hRR.trans_le (min_le_right 1 (min d2 d4))
    exact hrest.trans_le (min_le_left d2 d4)
  have hRd4 :
      R < d4 := by
    have hrest :
        R < min d2 d4 :=
      hRR.trans_le (min_le_right 1 (min d2 d4))
    exact hrest.trans_le (min_le_right d2 d4)

  let mu0 : ℝ := quarticFourAtomicMu lam
  let d : ℝ := quarticFourAtomicMuRadius
  let muMinus : ℝ := mu0-d
  let muPlus : ℝ := mu0+d

  have hdpos : 0 < d := by
    dsimp [d]
    exact quarticFourAtomicMuRadius_pos
  have hmump : muMinus < muPlus := by
    dsimp [muMinus,muPlus]
    linarith

  have hminusNear :
      |muMinus-quarticFourAtomicMu lam|
        <= quarticFourAtomicMuRadius := by
    dsimp [muMinus,mu0,d]
    rw [abs_neg]
    exact le_rfl
  have hplusNear :
      |muPlus-quarticFourAtomicMu lam|
        <= quarticFourAtomicMuRadius := by
    dsimp [muPlus,mu0,d]
    simp

  have hminusAbs : |muMinus| < 1/10 :=
    quarticFourAtomicMu_corridor_abs_lt_tenth
      hlam.1 hlam.2 hminusNear
  have hplusAbs : |muPlus| < 1/10 :=
    quarticFourAtomicMu_corridor_abs_lt_tenth
      hlam.1 hlam.2 hplusNear

  have hcloseMinus :=
    hclose2 R lam muMinus hR hRd2 hlam hminusAbs.le
  have hclosePlus :=
    hclose2 R lam muPlus hR hRd2 hlam hplusAbs.le

  have hatMinus :=
    quarticFourAtomicJ2_sub_radius_le_neg_margin
      hlam.1 hlam.2
  have hatPlus :=
    quarticFourAtomicJ2_add_radius_ge_margin
      hlam.1 hlam.2

  have hsmoothMinus :
      quarticFourWindowJ R lam muMinus 2 < 0 := by
    have hhi := (abs_le.mp hcloseMinus).2
    dsimp [eps2] at hhi
    dsimp [muMinus,mu0,d] at hatMinus
    linarith [quarticFourAtomicJ2CorridorMargin_pos]

  have hsmoothPlus :
      0 < quarticFourWindowJ R lam muPlus 2 := by
    have hlo := (abs_le.mp hclosePlus).1
    dsimp [eps2] at hlo
    dsimp [muPlus,mu0,d] at hatPlus
    linarith [quarticFourAtomicJ2CorridorMargin_pos]

  have hcont :
      ContinuousOn
        (fun mu => quarticFourWindowJ R lam mu 2)
        (Set.Icc muMinus muPlus) :=
    (quarticFourWindowJ_continuous_mu R lam 2).continuousOn
  have hzero :
      (0:ℝ) ∈
        Set.Icc
          (quarticFourWindowJ R lam muMinus 2)
          (quarticFourWindowJ R lam muPlus 2) :=
    ⟨hsmoothMinus.le,hsmoothPlus.le⟩
  obtain ⟨mu,hmuMem,hmuZero⟩ :=
    intermediate_value_Icc' hmump.le hcont hzero

  have hmuNear :
      |mu-quarticFourAtomicMu lam|
        <= quarticFourAtomicMuRadius := by
    rw [abs_le]
    dsimp [muMinus,muPlus,mu0,d] at hmuMem ⊢
    constructor <;> linarith [hmuMem.1,hmuMem.2]

  have hmuAbs :
      |mu| < 1/10 :=
    quarticFourAtomicMu_corridor_abs_lt_tenth
      hlam.1 hlam.2 hmuNear

  have hcloseJ4 :=
    hclose4 R lam mu hR hRd4 hlam hmuAbs.le
  have hatJ4 :=
    quarticFourAtomicJ4_le_neg_corridorMargin
      hlam.1 hlam.2 hmuNear
  have hsmoothJ4 :
      quarticFourWindowJ R lam mu 4 < 0 := by
    have hhi := (abs_le.mp hcloseJ4).2
    dsimp [eps4] at hhi
    linarith [quarticFourAtomicJ4CorridorMargin_pos]

  refine ⟨{
    mu := mu
    muNear := hmuNear
    muAbs := hmuAbs
    J2zero := ?_
    J4neg := ?_
  }⟩
  · rw [projectiveBracketSecondMoment_fourWindow_one hR]
    exact hmuZero.symm
  · rw [projectiveBracketFourthMoment_fourWindow_one hR]
    exact hsmoothJ4

end Synthesis
