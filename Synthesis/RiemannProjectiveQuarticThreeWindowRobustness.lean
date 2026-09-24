import Synthesis.RiemannProjectiveQuarticThreeWindowLocalization

/-!
# Robust determinant transport from the atomic family to smooth windows

Uniform control of the four scalar responses entering a 2x2 projective
determinant gives uniform control of the determinant itself.

This file packages that elementary perturbation estimate and applies the
three-window localization theorem to J2 and J4.  The output is an
epsilon-radius theorem uniform in lambda in [1/2,3/4].
-/

noncomputable section

open Set
open scoped Real

namespace Synthesis

def quarticMomentWeight (k : ℕ) (s : ℝ) : ℝ → ℝ :=
  fun u => u^k * Real.cos (s*u)

theorem quarticMomentWeight_continuous (k : ℕ) (s : ℝ) :
    Continuous (quarticMomentWeight k s) := by
  unfold quarticMomentWeight
  fun_prop

theorem quarticMomentWeight_even_zero (s : ℝ) :
    ∀ u, quarticMomentWeight 0 s (-u) = quarticMomentWeight 0 s u := by
  intro u
  simp [quarticMomentWeight, Real.cos_neg]

theorem quarticMomentWeight_even_two (s : ℝ) :
    ∀ u, quarticMomentWeight 2 s (-u) = quarticMomentWeight 2 s u := by
  intro u
  simp [quarticMomentWeight, Real.cos_neg]
  ring

theorem quarticMomentWeight_even_four (s : ℝ) :
    ∀ u, quarticMomentWeight 4 s (-u) = quarticMomentWeight 4 s u := by
  intro u
  simp [quarticMomentWeight, Real.cos_neg]
  ring

theorem quarticAtomicPairing_momentWeight
    (lam : ℝ) (k : ℕ) (s : ℝ) :
    quarticAtomicPairingAt lam (quarticMomentWeight k s)
      = quarticAtomicMomentRespAt lam k s := by
  unfold quarticAtomicPairingAt quarticMomentWeight
    quarticAtomicMomentRespAt
  ring

theorem quarticThreeWindowPairing_momentWeight
    (R lam : ℝ) (k : ℕ) (s : ℝ) :
    quarticThreeWindowPairing R lam (quarticMomentWeight k s)
      = quarticThreeWindowMomentResp R lam k s := by
  rfl

/--
Elementary determinant perturbation bound.  If all four coordinates move by at
most eta and all four reference coordinates have absolute value at most M,
then the determinant moves by at most (4M+2) eta when eta<=1.
-/
theorem abs_det_sub_det_le
    {a b c d a0 b0 c0 d0 M eta : ℝ}
    (hM : 0 ≤ M)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (ha0 : |a0| ≤ M) (hb0 : |b0| ≤ M)
    (hc0 : |c0| ≤ M) (hd0 : |d0| ≤ M)
    (ha : |a-a0| ≤ eta) (hb : |b-b0| ≤ eta)
    (hc : |c-c0| ≤ eta) (hd : |d-d0| ≤ eta) :
    |(a*b-c*d) - (a0*b0-c0*d0)|
      ≤ (4*M+2)*eta := by
  have habsa : |a| ≤ M + eta := by
    calc
      |a| = |(a-a0)+a0| := by ring_nf
      _ ≤ |a-a0| + |a0| := abs_add _ _
      _ ≤ eta + M := add_le_add ha ha0
      _ = M + eta := by ring
  have habsc : |c| ≤ M + eta := by
    calc
      |c| = |(c-c0)+c0| := by ring_nf
      _ ≤ |c-c0| + |c0| := abs_add _ _
      _ ≤ eta + M := add_le_add hc hc0
      _ = M + eta := by ring
  have hprod1 :
      |a*b-a0*b0| ≤ 2*M*eta + eta^2 := by
    have hid : a*b-a0*b0 = a*(b-b0) + (a-a0)*b0 := by ring
    calc
      |a*b-a0*b0|
        ≤ |a|*|b-b0| + |a-a0|*|b0| := by
          rw [hid]
          calc
            |a*(b-b0) + (a-a0)*b0|
              ≤ |a*(b-b0)| + |(a-a0)*b0| := abs_add _ _
            _ = |a|*|b-b0| + |a-a0|*|b0| := by
              rw [abs_mul, abs_mul]
      _ ≤ (M+eta)*eta + eta*M := by
        gcongr
      _ = 2*M*eta + eta^2 := by ring
  have hprod2 :
      |c*d-c0*d0| ≤ 2*M*eta + eta^2 := by
    have hid : c*d-c0*d0 = c*(d-d0) + (c-c0)*d0 := by ring
    calc
      |c*d-c0*d0|
        ≤ |c|*|d-d0| + |c-c0|*|d0| := by
          rw [hid]
          calc
            |c*(d-d0) + (c-c0)*d0|
              ≤ |c*(d-d0)| + |(c-c0)*d0| := abs_add _ _
            _ = |c|*|d-d0| + |c-c0|*|d0| := by
              rw [abs_mul, abs_mul]
      _ ≤ (M+eta)*eta + eta*M := by
        gcongr
      _ = 2*M*eta + eta^2 := by ring
  calc
    |(a*b-c*d) - (a0*b0-c0*d0)|
      = |(a*b-a0*b0) - (c*d-c0*d0)| := by ring_nf
    _ ≤ |a*b-a0*b0| + |c*d-c0*d0| := abs_sub _ _
    _ ≤ (2*M*eta+eta^2) + (2*M*eta+eta^2) :=
      add_le_add hprod1 hprod2
    _ ≤ (4*M+2)*eta := by
      have hetaSq : eta^2 ≤ eta := by nlinarith
      nlinarith

def quarticAtomicMomentBound (k : ℕ) : ℝ :=
  |quarticMomentWeight k 1 0|
    + |quarticMomentWeight k 1 (Real.pi/3)|
    + (3/4 : ℝ) * |quarticMomentWeight k 1 (Real.pi/2)|
    + |quarticMomentWeight k 2 0|
    + |quarticMomentWeight k 2 (Real.pi/3)|
    + (3/4 : ℝ) * |quarticMomentWeight k 2 (Real.pi/2)|

theorem quarticAtomicMomentBound_nonneg (k : ℕ) :
    0 ≤ quarticAtomicMomentBound k := by
  unfold quarticAtomicMomentBound
  positivity

theorem quarticAtomicMomentResp_abs_le_bound
    {lam : ℝ} (hlam : lam ∈ Set.Icc (1/2 : ℝ) (3/4 : ℝ))
    (k : ℕ) (s : ℝ) (hs : s = 1 ∨ s = 2) :
    |quarticAtomicMomentRespAt lam k s|
      ≤ quarticAtomicMomentBound k := by
  have hlam0 : 0 ≤ lam := by linarith [hlam.1]
  have hlam34 : |lam| ≤ 3/4 := by
    rw [abs_of_nonneg hlam0]
    exact hlam.2
  unfold quarticAtomicMomentRespAt
  have htri :
      |0^k * Real.cos (s*0)
        - (Real.pi/3)^k * Real.cos (s*(Real.pi/3))
        + lam*(Real.pi/2)^k*Real.cos (s*(Real.pi/2))|
      ≤
      |quarticMomentWeight k s 0|
        + |quarticMomentWeight k s (Real.pi/3)|
        + |lam|*|quarticMomentWeight k s (Real.pi/2)| := by
    unfold quarticMomentWeight
    calc
      |0^k * Real.cos (s*0)
        - (Real.pi/3)^k * Real.cos (s*(Real.pi/3))
        + lam*(Real.pi/2)^k*Real.cos (s*(Real.pi/2))|
        ≤
      |0^k * Real.cos (s*0)
        - (Real.pi/3)^k * Real.cos (s*(Real.pi/3))|
        + |lam*(Real.pi/2)^k*Real.cos (s*(Real.pi/2))| := abs_add _ _
      _ ≤
      |0^k * Real.cos (s*0)|
        + |(Real.pi/3)^k * Real.cos (s*(Real.pi/3))|
        + |lam|*|(Real.pi/2)^k*Real.cos (s*(Real.pi/2))| := by
          gcongr
          · exact abs_sub _ _
          · rw [abs_mul]
      _ = _ := by ring
  rcases hs with rfl | rfl
  · exact htri.trans (by
      unfold quarticAtomicMomentBound
      have hnon :
          0 ≤ |quarticMomentWeight k 2 0|
            + |quarticMomentWeight k 2 (Real.pi/3)|
            + (3/4 : ℝ)*|quarticMomentWeight k 2 (Real.pi/2)| := by positivity
      have hmul := mul_le_mul_of_nonneg_right hlam34
        (abs_nonneg (quarticMomentWeight k 1 (Real.pi/2)))
      linarith)
  · exact htri.trans (by
      unfold quarticAtomicMomentBound
      have hnon :
          0 ≤ |quarticMomentWeight k 1 0|
            + |quarticMomentWeight k 1 (Real.pi/3)|
            + (3/4 : ℝ)*|quarticMomentWeight k 1 (Real.pi/2)| := by positivity
      have hmul := mul_le_mul_of_nonneg_right hlam34
        (abs_nonneg (quarticMomentWeight k 2 (Real.pi/2)))
      linarith)

/--
For k=2 or k=4, the smooth determinant converges uniformly in lambda to the
atomic determinant on [1/2,3/4].
-/
theorem exists_radius_quarticThreeWindowJ_close_atomic
    {k : ℕ}
    (heven1 : ∀ u, quarticMomentWeight k 1 (-u) = quarticMomentWeight k 1 u)
    (heven2 : ∀ u, quarticMomentWeight k 2 (-u) = quarticMomentWeight k 2 u)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ R lam : ℝ,
        0 < R -> R < delta ->
        lam ∈ Set.Icc (1/2 : ℝ) (3/4 : ℝ) ->
        |quarticThreeWindowJ R lam k - quarticAtomicJAt lam k| ≤ eps := by
  let M : ℝ := quarticAtomicMomentBound 0 + quarticAtomicMomentBound k
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  let eta : ℝ := min 1 (eps / (8*(M+1)))
  have hden : 0 < 8*(M+1) := by positivity
  have heta : 0 < eta := by
    dsimp [eta]
    exact lt_min (by norm_num) (div_pos heps hden)
  have heta1 : eta ≤ 1 := min_le_left _ _

  obtain ⟨d01, hd01, h01⟩ :=
    exists_radius_quarticThreeWindowPairing_close_atomic
      (quarticMomentWeight_continuous 0 1)
      (quarticMomentWeight_even_zero 1) heta
  obtain ⟨d02, hd02, h02⟩ :=
    exists_radius_quarticThreeWindowPairing_close_atomic
      (quarticMomentWeight_continuous 0 2)
      (quarticMomentWeight_even_zero 2) heta
  obtain ⟨dk1, hdk1, hk1⟩ :=
    exists_radius_quarticThreeWindowPairing_close_atomic
      (quarticMomentWeight_continuous k 1) heven1 heta
  obtain ⟨dk2, hdk2, hk2⟩ :=
    exists_radius_quarticThreeWindowPairing_close_atomic
      (quarticMomentWeight_continuous k 2) heven2 heta

  let delta := min d01 (min d02 (min dk1 dk2))
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min hd01 (lt_min hd02 (lt_min hdk1 hdk2))
  refine ⟨delta, hdelta, ?_⟩
  intro R lam hR hRd hlam
  have hR01 : R < d01 := hRd.trans_le (min_le_left _ _)
  have hRest : R < min d02 (min dk1 dk2) :=
    hRd.trans_le (min_le_right _ _)
  have hR02 : R < d02 := hRest.trans_le (min_le_left _ _)
  have hRkk : R < min dk1 dk2 := hRest.trans_le (min_le_right _ _)
  have hRk1 : R < dk1 := hRkk.trans_le (min_le_left _ _)
  have hRk2 : R < dk2 := hRkk.trans_le (min_le_right _ _)

  have ha := h01 R lam hR hR01 hlam
  have hc := h02 R lam hR hR02 hlam
  have hd := hk1 R lam hR hRk1 hlam
  have hb := hk2 R lam hR hRk2 hlam

  rw [quarticThreeWindowPairing_momentWeight] at ha hc hd hb
  rw [quarticAtomicPairing_momentWeight] at ha hc hd hb

  have ha0 :
      |quarticAtomicMomentRespAt lam 0 1| ≤ M := by
    have h := quarticAtomicMomentResp_abs_le_bound hlam 0 1 (Or.inl rfl)
    dsimp [M]
    linarith [quarticAtomicMomentBound_nonneg k]
  have hc0 :
      |quarticAtomicMomentRespAt lam 0 2| ≤ M := by
    have h := quarticAtomicMomentResp_abs_le_bound hlam 0 2 (Or.inr rfl)
    dsimp [M]
    linarith [quarticAtomicMomentBound_nonneg k]
  have hd0 :
      |quarticAtomicMomentRespAt lam k 1| ≤ M := by
    have h := quarticAtomicMomentResp_abs_le_bound hlam k 1 (Or.inl rfl)
    dsimp [M]
    linarith [quarticAtomicMomentBound_nonneg 0]
  have hb0 :
      |quarticAtomicMomentRespAt lam k 2| ≤ M := by
    have h := quarticAtomicMomentResp_abs_le_bound hlam k 2 (Or.inr rfl)
    dsimp [M]
    linarith [quarticAtomicMomentBound_nonneg 0]

  have hdet := abs_det_sub_det_le
    hM heta.le heta1
    ha0 hb0 hc0 hd0
    ha hb hc hd
  unfold quarticThreeWindowJ quarticAtomicJAt
  exact hdet.trans (by
    have hetaDef : eta ≤ eps / (8*(M+1)) := min_le_right _ _
    have hcoeff : 0 ≤ 4*M+2 := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hetaDef hcoeff
    have hratio : (4*M+2) / (8*(M+1)) ≤ 1 := by
      rw [div_le_one hden]
      nlinarith
    calc
      (4*M+2)*eta
        ≤ (4*M+2)*(eps/(8*(M+1))) := hscaled
      _ = eps * ((4*M+2)/(8*(M+1))) := by field_simp; ring
      _ ≤ eps := by
        exact mul_le_of_le_one_right heps.le hratio)

theorem exists_radius_quarticThreeWindowJ2_close_atomic
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ R lam : ℝ,
        0 < R -> R < delta ->
        lam ∈ Set.Icc (1/2 : ℝ) (3/4 : ℝ) ->
        |quarticThreeWindowJ R lam 2 - quarticAtomicJAt lam 2| ≤ eps :=
  exists_radius_quarticThreeWindowJ_close_atomic
    (quarticMomentWeight_even_two 1)
    (quarticMomentWeight_even_two 2)
    heps

theorem exists_radius_quarticThreeWindowJ4_close_atomic
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ R lam : ℝ,
        0 < R -> R < delta ->
        lam ∈ Set.Icc (1/2 : ℝ) (3/4 : ℝ) ->
        |quarticThreeWindowJ R lam 4 - quarticAtomicJAt lam 4| ≤ eps :=
  exists_radius_quarticThreeWindowJ_close_atomic
    (quarticMomentWeight_even_four 1)
    (quarticMomentWeight_even_four 2)
    heps

end Synthesis
