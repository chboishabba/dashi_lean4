import Synthesis.RiemannProjectiveQuarticFourWindowLocalization
import Synthesis.RiemannProjectiveQuarticThreeWindowRobustness

/-!
# Uniform determinant robustness for the four-window quartic family

The four scalar responses entering each projective determinant converge
uniformly to their atomic counterparts on

  lambda in [1/2,2/3], |mu| <= 1/10.

The generic determinant perturbation bound therefore gives uniform convergence

  J_k^smooth(R,lambda,mu) -> J_k^atomic(lambda,mu)

for k=2 and k=4.

This is the last analytic localization layer needed before solving the smooth
J2 equation in mu while leaving lambda free.
-/

noncomputable section

open Set
open scoped Real

namespace Synthesis

def quarticFourAtomicMomentBound (k : ℕ) : ℝ :=
  |quarticMomentWeight k 1 0|
    + |quarticMomentWeight k 1 (Real.pi/3)|
    + (2/3 : ℝ) * |quarticMomentWeight k 1 (Real.pi/2)|
    + (1/10 : ℝ) * |quarticMomentWeight k 1 Real.pi|
    + |quarticMomentWeight k 2 0|
    + |quarticMomentWeight k 2 (Real.pi/3)|
    + (2/3 : ℝ) * |quarticMomentWeight k 2 (Real.pi/2)|
    + (1/10 : ℝ) * |quarticMomentWeight k 2 Real.pi|

theorem quarticFourAtomicMomentBound_nonneg (k : ℕ) :
    0 <= quarticFourAtomicMomentBound k := by
  unfold quarticFourAtomicMomentBound
  positivity

theorem quarticFourAtomicMomentResp_abs_le_bound
    {lam mu : ℝ}
    (hlam : lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ))
    (hmu : |mu| <= 1/10)
    (k : ℕ) (s : ℝ) (hs : s=1 ∨ s=2) :
    |quarticFourAtomicMomentRespAt lam mu k s|
      <= quarticFourAtomicMomentBound k := by
  have hlam0 : 0 <= lam := by linarith [hlam.1]
  have hlamAbs : |lam| <= 2/3 := by
    rw [abs_of_nonneg hlam0]
    exact hlam.2
  unfold quarticFourAtomicMomentRespAt
  have htri :
      |0^k*Real.cos (s*0)
        -(Real.pi/3)^k*Real.cos (s*(Real.pi/3))
        +lam*(Real.pi/2)^k*Real.cos (s*(Real.pi/2))
        +mu*Real.pi^k*Real.cos (s*Real.pi)|
      <=
      |quarticMomentWeight k s 0|
        + |quarticMomentWeight k s (Real.pi/3)|
        + |lam|*|quarticMomentWeight k s (Real.pi/2)|
        + |mu|*|quarticMomentWeight k s Real.pi| := by
    unfold quarticMomentWeight
    calc
      |0^k*Real.cos (s*0)
        -(Real.pi/3)^k*Real.cos (s*(Real.pi/3))
        +lam*(Real.pi/2)^k*Real.cos (s*(Real.pi/2))
        +mu*Real.pi^k*Real.cos (s*Real.pi)|
        <=
      |0^k*Real.cos (s*0)
        -(Real.pi/3)^k*Real.cos (s*(Real.pi/3))
        +lam*(Real.pi/2)^k*Real.cos (s*(Real.pi/2))|
        + |mu*Real.pi^k*Real.cos (s*Real.pi)| := abs_add _ _
      _ <=
      (|0^k*Real.cos (s*0)|
        + |(Real.pi/3)^k*Real.cos (s*(Real.pi/3))|
        + |lam|*|(Real.pi/2)^k*Real.cos (s*(Real.pi/2))|)
        + |mu|*|Real.pi^k*Real.cos (s*Real.pi)| := by
          gcongr
          · calc
              |0^k*Real.cos (s*0)
                -(Real.pi/3)^k*Real.cos (s*(Real.pi/3))
                +lam*(Real.pi/2)^k*Real.cos (s*(Real.pi/2))|
                <=
              |0^k*Real.cos (s*0)
                -(Real.pi/3)^k*Real.cos (s*(Real.pi/3))|
                + |lam*(Real.pi/2)^k*Real.cos (s*(Real.pi/2))| :=
                  abs_add _ _
              _ <=
              (|0^k*Real.cos (s*0)|
                + |(Real.pi/3)^k*Real.cos (s*(Real.pi/3))|)
                + |lam|*|(Real.pi/2)^k*Real.cos (s*(Real.pi/2))| := by
                  gcongr
                  · exact abs_sub _ _
                  · rw [abs_mul]
          · rw [abs_mul]
  rcases hs with rfl | rfl
  · exact htri.trans (by
      unfold quarticFourAtomicMomentBound
      have hlamMul :=
        mul_le_mul_of_nonneg_right hlamAbs
          (abs_nonneg (quarticMomentWeight k 1 (Real.pi/2)))
      have hmuMul :=
        mul_le_mul_of_nonneg_right hmu
          (abs_nonneg (quarticMomentWeight k 1 Real.pi))
      positivity
      nlinarith)
  · exact htri.trans (by
      unfold quarticFourAtomicMomentBound
      have hlamMul :=
        mul_le_mul_of_nonneg_right hlamAbs
          (abs_nonneg (quarticMomentWeight k 2 (Real.pi/2)))
      have hmuMul :=
        mul_le_mul_of_nonneg_right hmu
          (abs_nonneg (quarticMomentWeight k 2 Real.pi))
      positivity
      nlinarith)

theorem exists_radius_quarticFourWindowJ_close_atomic
    {k : ℕ}
    (heven1 : ∀ u, quarticMomentWeight k 1 (-u)
      = quarticMomentWeight k 1 u)
    (heven2 : ∀ u, quarticMomentWeight k 2 (-u)
      = quarticMomentWeight k 2 u)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ R lam mu : ℝ,
        0 < R -> R < delta ->
        lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) ->
        |mu| <= 1/10 ->
        |quarticFourWindowJ R lam mu k
          - quarticFourAtomicJAt lam mu k| <= eps := by
  let M : ℝ :=
    quarticFourAtomicMomentBound 0
      + quarticFourAtomicMomentBound k
  have hM : 0 <= M := by
    dsimp [M]
    positivity
  let eta : ℝ := min 1 (eps/(8*(M+1)))
  have hden : 0 < 8*(M+1) := by positivity
  have heta : 0 < eta := by
    dsimp [eta]
    exact lt_min (by norm_num) (div_pos heps hden)
  have heta1 : eta <= 1 := min_le_left _ _

  obtain ⟨d01,hd01,h01⟩ :=
    exists_radius_quarticFourWindowPairing_close_atomic
      (quarticMomentWeight_continuous 0 1)
      (quarticMomentWeight_even_zero 1) heta
  obtain ⟨d02,hd02,h02⟩ :=
    exists_radius_quarticFourWindowPairing_close_atomic
      (quarticMomentWeight_continuous 0 2)
      (quarticMomentWeight_even_zero 2) heta
  obtain ⟨dk1,hdk1,hk1⟩ :=
    exists_radius_quarticFourWindowPairing_close_atomic
      (quarticMomentWeight_continuous k 1) heven1 heta
  obtain ⟨dk2,hdk2,hk2⟩ :=
    exists_radius_quarticFourWindowPairing_close_atomic
      (quarticMomentWeight_continuous k 2) heven2 heta

  let delta := min d01 (min d02 (min dk1 dk2))
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min hd01 (lt_min hd02 (lt_min hdk1 hdk2))
  refine ⟨delta,hdelta,?_⟩
  intro R lam mu hR hRd hlam hmu
  have hR01 : R < d01 :=
    hRd.trans_le (min_le_left _ _)
  have hRest : R < min d02 (min dk1 dk2) :=
    hRd.trans_le (min_le_right _ _)
  have hR02 : R < d02 :=
    hRest.trans_le (min_le_left _ _)
  have hRkk : R < min dk1 dk2 :=
    hRest.trans_le (min_le_right _ _)
  have hRk1 : R < dk1 :=
    hRkk.trans_le (min_le_left _ _)
  have hRk2 : R < dk2 :=
    hRkk.trans_le (min_le_right _ _)

  have ha := h01 R lam mu hR hR01 hlam hmu
  have hc := h02 R lam mu hR hR02 hlam hmu
  have hd := hk1 R lam mu hR hRk1 hlam hmu
  have hb := hk2 R lam mu hR hRk2 hlam hmu

  rw [quarticFourWindowPairing_momentWeight] at ha hc hd hb
  rw [quarticFourAtomicPairing_momentWeight] at ha hc hd hb

  have ha0 :
      |quarticFourAtomicMomentRespAt lam mu 0 1| <= M := by
    have h :=
      quarticFourAtomicMomentResp_abs_le_bound
        hlam hmu 0 1 (Or.inl rfl)
    dsimp [M]
    linarith [quarticFourAtomicMomentBound_nonneg k]
  have hc0 :
      |quarticFourAtomicMomentRespAt lam mu 0 2| <= M := by
    have h :=
      quarticFourAtomicMomentResp_abs_le_bound
        hlam hmu 0 2 (Or.inr rfl)
    dsimp [M]
    linarith [quarticFourAtomicMomentBound_nonneg k]
  have hd0 :
      |quarticFourAtomicMomentRespAt lam mu k 1| <= M := by
    have h :=
      quarticFourAtomicMomentResp_abs_le_bound
        hlam hmu k 1 (Or.inl rfl)
    dsimp [M]
    linarith [quarticFourAtomicMomentBound_nonneg 0]
  have hb0 :
      |quarticFourAtomicMomentRespAt lam mu k 2| <= M := by
    have h :=
      quarticFourAtomicMomentResp_abs_le_bound
        hlam hmu k 2 (Or.inr rfl)
    dsimp [M]
    linarith [quarticFourAtomicMomentBound_nonneg 0]

  have hdet := abs_det_sub_det_le
    hM heta.le heta1
    ha0 hb0 hc0 hd0
    ha hb hc hd
  unfold quarticFourWindowJ quarticFourAtomicJAt
  exact hdet.trans (by
    have hetaDef : eta <= eps/(8*(M+1)) := min_le_right _ _
    have hcoeff : 0 <= 4*M+2 := by positivity
    have hscaled :=
      mul_le_mul_of_nonneg_left hetaDef hcoeff
    have hratio : (4*M+2)/(8*(M+1)) <= 1 := by
      rw [div_le_one hden]
      nlinarith
    calc
      (4*M+2)*eta
        <= (4*M+2)*(eps/(8*(M+1))) := hscaled
      _ = eps*((4*M+2)/(8*(M+1))) := by
        field_simp
        ring
      _ <= eps := mul_le_of_le_one_right heps.le hratio)

theorem exists_radius_quarticFourWindowJ2_close_atomic
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ R lam mu : ℝ,
        0 < R -> R < delta ->
        lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) ->
        |mu| <= 1/10 ->
        |quarticFourWindowJ R lam mu 2
          - quarticFourAtomicJAt lam mu 2| <= eps :=
  exists_radius_quarticFourWindowJ_close_atomic
    (quarticMomentWeight_even_two 1)
    (quarticMomentWeight_even_two 2) heps

theorem exists_radius_quarticFourWindowJ4_close_atomic
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ R lam mu : ℝ,
        0 < R -> R < delta ->
        lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) ->
        |mu| <= 1/10 ->
        |quarticFourWindowJ R lam mu 4
          - quarticFourAtomicJAt lam mu 4| <= eps :=
  exists_radius_quarticFourWindowJ_close_atomic
    (quarticMomentWeight_even_four 1)
    (quarticMomentWeight_even_four 2) heps

end Synthesis
