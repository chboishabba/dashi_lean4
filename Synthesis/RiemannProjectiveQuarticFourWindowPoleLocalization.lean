import Synthesis.RiemannProjectiveQuarticFourWindowPoleSameObject
import Synthesis.RiemannProjectiveQuarticFourWindowLocalization
import Synthesis.RiemannProjectiveQuarticThreeWindowRobustness

/-!
# Smooth four-window pole positivity by atomic localization

For each fixed physical ordinate t>=200, the four scalar entries of the
normalized smooth pole determinant converge uniformly, as R->0+, to the atomic
entries, uniformly over

  lambda in [1/2,2/3],  |mu| <= 1/10.

The finite atomic determinant has the uniform lower bound 17/20.  Therefore,
for sufficiently small R, the smooth normalized determinant is positive, and
the literal projective pole defect is positive as well.

This rules out using the free fourth-window parameter to create a pole-sign
crossing in the narrow-window quartic family.
-/

noncomputable section

open Set
open scoped Real

namespace Synthesis

private theorem quarticFourPole_cosh_bounds
    {t : ℝ} (ht : 200 <= t) :
    Real.cosh (8*Real.pi/(3*t)) <= 2
      ∧ Real.cosh (4*Real.pi/t) <= 2
      ∧ Real.cosh (8*Real.pi/t) <= 2 := by
  have htpos : 0 < t := by linarith
  have h3 :
      Real.cosh (8*Real.pi/t) <= 2 := by
    have h :=
      quarticFour_cosh_excess_le_one_of_twoHundred ht
    linarith
  have hx1non : 0 <= 8*Real.pi/(3*t) := by positivity
  have hx2non : 0 <= 4*Real.pi/t := by positivity
  have hx3non : 0 <= 8*Real.pi/t := by positivity
  have hx1 :
      |8*Real.pi/(3*t)| <= |8*Real.pi/t| := by
    rw [abs_of_nonneg hx1non, abs_of_nonneg hx3non]
    have hp := Real.pi_pos
    field_simp [ne_of_gt htpos]
    nlinarith
  have hx2 :
      |4*Real.pi/t| <= |8*Real.pi/t| := by
    rw [abs_of_nonneg hx2non, abs_of_nonneg hx3non]
    have hp := Real.pi_pos
    field_simp [ne_of_gt htpos]
    nlinarith
  have h1le :
      Real.cosh (8*Real.pi/(3*t))
        <= Real.cosh (8*Real.pi/t) :=
    (Real.cosh_le_cosh).2 hx1
  have h2le :
      Real.cosh (4*Real.pi/t)
        <= Real.cosh (8*Real.pi/t) :=
    (Real.cosh_le_cosh).2 hx2
  exact ⟨h1le.trans h3, h2le.trans h3, h3⟩

private theorem quarticFourAtomicPole_entries_abs_le_five
    {t lam mu : ℝ}
    (ht : 200 <= t)
    (hlam : lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ))
    (hmu : |mu| <= 1/10) :
    |quarticFourAtomicPairingAt lam mu
        (quarticFourNormalizedPoleWeight t 1)| <= 5
    ∧
    |quarticFourAtomicPairingAt lam mu
        (quarticFourNormalizedOnLineWeight 2)| <= 5
    ∧
    |quarticFourAtomicPairingAt lam mu
        (quarticFourNormalizedPoleWeight t 2)| <= 5
    ∧
    |quarticFourAtomicPairingAt lam mu
        (quarticFourNormalizedOnLineWeight 1)| <= 5 := by
  have ht0 : t ≠ 0 := by linarith
  rcases quarticFourPole_cosh_bounds ht with ⟨hh1,hh2,hh3⟩
  have hc1 : 1 <= Real.cosh (8*Real.pi/(3*t)) :=
    Real.one_le_cosh _
  have hc2 : 1 <= Real.cosh (4*Real.pi/t) :=
    Real.one_le_cosh _
  have hc3 : 1 <= Real.cosh (8*Real.pi/t) :=
    Real.one_le_cosh _
  have hlam0 : 0 <= lam := by linarith [hlam.1]
  have hmuLo : -1/10 <= mu := (abs_le.mp hmu).1
  have hmuHi : mu <= 1/10 := (abs_le.mp hmu).2
  have hm3abs :
      |mu * Real.cosh (8*Real.pi/t)| <= 1/5 := by
    rw [abs_mul, abs_of_nonneg hc3.le]
    nlinarith
  have hm3lo :
      -(1/5 : ℝ) <= mu * Real.cosh (8*Real.pi/t) :=
    (abs_le.mp hm3abs).1
  have hm3hi :
      mu * Real.cosh (8*Real.pi/t) <= 1/5 :=
    (abs_le.mp hm3abs).2
  constructor
  · rw [quarticFourAtomicPolePairing_one ht0]
    rw [abs_le]
    constructor <;> nlinarith
  constructor
  · rw [quarticFourAtomicOnLinePairing_two]
    rw [abs_le]
    constructor <;> linarith
  constructor
  · rw [quarticFourAtomicPolePairing_two ht0]
    have hlh2 : 0 <= lam * Real.cosh (4*Real.pi/t) := by positivity
    have hlh2hi :
        lam * Real.cosh (4*Real.pi/t) <= 4/3 := by
      nlinarith [hlam.2]
    rw [abs_le]
    constructor <;> nlinarith
  · rw [quarticFourAtomicOnLinePairing_one]
    rw [abs_le]
    constructor <;> linarith

/--
Uniform determinant localization for fixed high t.
-/
theorem exists_radius_quarticFourSmoothPole_close_atomic
    {t eps : ℝ}
    (ht : 200 <= t)
    (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ R lam mu : ℝ,
        0 < R -> R < delta ->
        lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) ->
        |mu| <= 1/10 ->
        |quarticFourSmoothFinitePoleResidual R lam mu t
          - quarticFourAtomicFinitePoleResidual t lam mu|
          <= eps := by
  let M : ℝ := 5
  let eta : ℝ := min 1 (eps / 100)
  have heta : 0 < eta := by
    dsimp [eta]
    exact lt_min (by norm_num) (by positivity)
  have heta1 : eta <= 1 := min_le_left _ _
  obtain ⟨dP1,hdP1,hP1⟩ :=
    exists_radius_quarticFourWindowPairing_close_atomic
      (quarticFourNormalizedPoleWeight_continuous t 1)
      (quarticFourNormalizedPoleWeight_even t 1) heta
  obtain ⟨dA2,hdA2,hA2⟩ :=
    exists_radius_quarticFourWindowPairing_close_atomic
      (quarticFourNormalizedOnLineWeight_continuous 2)
      (quarticFourNormalizedOnLineWeight_even 2) heta
  obtain ⟨dP2,hdP2,hP2⟩ :=
    exists_radius_quarticFourWindowPairing_close_atomic
      (quarticFourNormalizedPoleWeight_continuous t 2)
      (quarticFourNormalizedPoleWeight_even t 2) heta
  obtain ⟨dA1,hdA1,hA1⟩ :=
    exists_radius_quarticFourWindowPairing_close_atomic
      (quarticFourNormalizedOnLineWeight_continuous 1)
      (quarticFourNormalizedOnLineWeight_even 1) heta
  let delta := min dP1 (min dA2 (min dP2 dA1))
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min hdP1 (lt_min hdA2 (lt_min hdP2 hdA1))
  refine ⟨delta,hdelta,?_⟩
  intro R lam mu hR hRd hlam hmu
  have hRP1 : R < dP1 := hRd.trans_le (min_le_left _ _)
  have hrest1 : R < min dA2 (min dP2 dA1) :=
    hRd.trans_le (min_le_right _ _)
  have hRA2 : R < dA2 := hrest1.trans_le (min_le_left _ _)
  have hrest2 : R < min dP2 dA1 :=
    hrest1.trans_le (min_le_right _ _)
  have hRP2 : R < dP2 := hrest2.trans_le (min_le_left _ _)
  have hRA1 : R < dA1 := hrest2.trans_le (min_le_right _ _)

  have ha := hP1 R lam mu hR hRP1 hlam hmu
  have hb := hA2 R lam mu hR hRA2 hlam hmu
  have hc := hP2 R lam mu hR hRP2 hlam hmu
  have hd := hA1 R lam mu hR hRA1 hlam hmu
  rcases quarticFourAtomicPole_entries_abs_le_five ht hlam hmu with
    ⟨ha0,hb0,hc0,hd0⟩
  have hM : 0 <= M := by norm_num
  have hdet :=
    abs_det_sub_det_le hM heta.le heta1
      ha0 hb0 hc0 hd0 ha hb hc hd
  unfold quarticFourSmoothFinitePoleResidual
    quarticFourAtomicFinitePoleDeterminant at hdet
  rw [quarticFourAtomicFinitePoleDeterminant_eq_residual
      (by linarith : t ≠ 0)] at hdet
  exact hdet.trans (by
    have hetaEps : eta <= eps/100 := min_le_right _ _
    have hscale := mul_le_mul_of_nonneg_left hetaEps
      (by norm_num : (0:ℝ) <= 22)
    calc
      (4*M+2)*eta = 22*eta := by dsimp [M]; ring
      _ <= 22*(eps/100) := hscale
      _ <= eps := by nlinarith [heps])

/--
For each high t, sufficiently narrow four-window profiles have strictly positive
normalized pole determinant throughout the whole coefficient corridor.
-/
theorem exists_radius_quarticFourSmoothPole_pos
    {t : ℝ} (ht : 200 <= t) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ R lam mu : ℝ,
        0 < R -> R < delta ->
        lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) ->
        |mu| <= 1/10 ->
        0 < quarticFourSmoothFinitePoleResidual R lam mu t := by
  obtain ⟨delta,hdelta,hclose⟩ :=
    exists_radius_quarticFourSmoothPole_close_atomic
      ht (by norm_num : (0:ℝ) < 17/40)
  refine ⟨delta,hdelta,?_⟩
  intro R lam mu hR hRd hlam hmu
  apply quarticFourSmoothPoleResidual_pos_of_close_atomic
    hlam.1 hlam.2 hmu
    (quarticFour_cosh_excess_le_one_of_twoHundred ht)
  exact hclose R lam mu hR hRd hlam hmu

/--
Same result on the literal projective pole channel.
-/
theorem exists_radius_quarticFour_poleProjectiveDefect_pos
    {t : ℝ} (ht : 200 <= t) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ R lam mu : ℝ,
        0 < R -> R < delta ->
        lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) ->
        |mu| <= 1/10 ->
        0 <
        Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
          (quarticFourPhysicalDetector R lam mu t) t (t/16) := by
  obtain ⟨delta,hdelta,hpos⟩ :=
    exists_radius_quarticFourSmoothPole_pos ht
  refine ⟨delta,hdelta,?_⟩
  intro R lam mu hR hRd hlam hmu
  rw [poleProjectiveDefect_quarticFourPhysicalDetector_eq
      hR (by linarith : 0 < t)]
  have hfac : 0 < 4*(16/t)^2 := by positivity
  exact mul_pos hfac (hpos R lam mu hR hRd hlam hmu)

end Synthesis
