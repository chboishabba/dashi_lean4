import Synthesis.RiemannProjectiveQuarticFourWindowUniformPoleWeight
import Synthesis.RiemannProjectiveQuarticFourWindowUniformPoleLocalization

/-!
# Uniform four-window pole determinant from the explicit pole-weight modulus

This file closes the finite-dimensional quantifier swap without reusing the
private fixed-t atomic-entry helper.

The ingredients are all public:
* the t-uniform pole-weight Lipschitz bound on [-6,6];
* exact support of the repository's scaled bumps;
* the normalized symmetric-bump localization identity;
* the four-window linear combination;
* the generic determinant perturbation estimate.

Atomic pole entries are bounded directly from w(0)=1 and the common Lipschitz
constant, so no fixed-t localization theorem is used in the proof.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set
open scoped Real

private def isQuarticFourCentre (a : ℝ) : Prop :=
  a = 0 ∨ a = Real.pi/3 ∨ a = Real.pi/2 ∨ a = Real.pi

private theorem quarticFourCentre_abs_le_four
    {a : ℝ} (ha : isQuarticFourCentre a) : |a| <= 4 := by
  rcases ha with rfl | rfl | rfl | rfl
  · norm_num
  · rw [abs_of_nonneg (by positivity : (0:ℝ) <= Real.pi/3)]
    nlinarith [Real.pi_pos, Real.pi_lt_four]
  · rw [abs_of_nonneg (by positivity : (0:ℝ) <= Real.pi/2)]
    nlinarith [Real.pi_pos, Real.pi_lt_four]
  · rw [abs_of_pos Real.pi_pos]
    exact Real.pi_lt_four.le

private theorem quarticFourCentre_mem_six
    {a : ℝ} (ha : isQuarticFourCentre a) :
    a ∈ Set.Icc (-6 : ℝ) 6 := by
  have h := quarticFourCentre_abs_le_four ha
  rw [abs_le] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

private theorem quarticFourBumpPoint_mem_six
    {a R u : ℝ}
    (hR : 0 < R) (hR1 : R < 1)
    (ha : isQuarticFourCentre a)
    (hu : scaledUnitBump a R u ≠ 0) :
    u ∈ Set.Icc (-6 : ℝ) 6 := by
  have hs := scaledUnitBump_support hR hu
  have ha4 := quarticFourCentre_abs_le_four ha
  have hutri : |u| <= |u-a| + |a| := by
    have h := abs_add (u-a) a
    simpa [sub_add_cancel] using h
  have hu5 : |u| < 5 := by linarith
  rw [abs_lt] at hu5
  exact ⟨by linarith [hu5.1], by linarith [hu5.2]⟩

private theorem normalizedSymBumpPairing_close_of_support_error
    {a R eta : ℝ}
    (hR : 0 < R) (heta : 0 <= eta)
    {w : ℝ -> ℝ}
    (hw : Continuous w)
    (heven : ∀ u, w (-u) = w u)
    (hosc : ∀ u : ℝ, scaledUnitBump a R u ≠ 0 -> |w u-w a| <= eta) :
    |normalizedSymBumpPairing a R w - w a| <= eta := by
  have hloc := quantitativeSymBump_weighted_localization
    (c:=a) hR heta hw heven hosc
  have hmass : 0 < 2*R*unitBumpMass0 := by
    have hM := unitBumpMass0_pos
    positivity
  unfold normalizedSymBumpPairing
  have hrewrite :
      (∫ u : ℝ, quantitativeSymBump a R u * w u)
          - (2*R*unitBumpMass0)*w a
        =
      (2*R*unitBumpMass0) *
        ((∫ u : ℝ, quantitativeSymBump a R u*w u)/(2*R*unitBumpMass0)-w a) := by
    field_simp [ne_of_gt hmass]
    ring
  rw [hrewrite, abs_mul, abs_of_pos hmass] at hloc
  exact (mul_le_mul_left hmass).mp hloc

private theorem normalizedPoleBump_close_uniform
    {t c a R : ℝ}
    (ht : 200 <= t) (hc : |c| <= 2)
    (hR : 0 < R) (hR1 : R < 1)
    (ha : isQuarticFourCentre a) :
    |normalizedSymBumpPairing a R (quarticFourNormalizedPoleWeight t c)
      - quarticFourNormalizedPoleWeight t c a|
      <= quarticFourUniformPoleLipschitzConstant*R := by
  apply normalizedSymBumpPairing_close_of_support_error hR
    (mul_nonneg quarticFourUniformPoleLipschitzConstant_pos.le hR.le)
    (quarticFourNormalizedPoleWeight_continuous t c)
    (quarticFourNormalizedPoleWeight_even t c)
  intro u hu
  have huu := quarticFourBumpPoint_mem_six hR hR1 ha hu
  have haa := quarticFourCentre_mem_six ha
  have hLip := quarticFourNormalizedPoleWeight_sub_abs_le_uniform
    ht hc huu haa
  have hs := scaledUnitBump_support hR hu
  exact hLip.trans
    (mul_le_mul_of_nonneg_left hs.le
      quarticFourUniformPoleLipschitzConstant_pos.le)

private theorem normalizedOnLineBump_close_uniform
    {c a R : ℝ}
    (hc : |c| <= 2)
    (hR : 0 < R)
    (ha : isQuarticFourCentre a) :
    |normalizedSymBumpPairing a R (quarticFourNormalizedOnLineWeight c)
      - quarticFourNormalizedOnLineWeight c a|
      <= 2*R := by
  apply normalizedSymBumpPairing_close_of_support_error hR (by positivity)
    (quarticFourNormalizedOnLineWeight_continuous c)
    (quarticFourNormalizedOnLineWeight_even c)
  intro u hu
  unfold quarticFourNormalizedOnLineWeight
  have hcos := Real.abs_cos_sub_cos_le (c*u) (c*a)
  have hs := scaledUnitBump_support hR hu
  calc
    |Real.cos (c*u)-Real.cos (c*a)| <= |c*u-c*a| := hcos
    _ = |c|*|u-a| := by
      rw [show c*u-c*a = c*(u-a) by ring, abs_mul]
    _ <= 2*R := by
      exact mul_le_mul hc hs.le (abs_nonneg _) (by norm_num)

private theorem fourWindowPairing_error_le_three
    {R lam mu eta : ℝ} {w : ℝ -> ℝ}
    (heta : 0 <= eta)
    (hlam : lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ))
    (hmu : |mu| <= 1/10)
    (h0 : |normalizedSymBumpPairing 0 R w-w 0| <= eta)
    (h1 : |normalizedSymBumpPairing (Real.pi/3) R w-w (Real.pi/3)| <= eta)
    (h2 : |normalizedSymBumpPairing (Real.pi/2) R w-w (Real.pi/2)| <= eta)
    (h3 : |normalizedSymBumpPairing Real.pi R w-w Real.pi| <= eta) :
    |quarticFourWindowPairing R lam mu w
      - quarticFourAtomicPairingAt lam mu w| <= 3*eta := by
  let e0 := normalizedSymBumpPairing 0 R w-w 0
  let e1 := normalizedSymBumpPairing (Real.pi/3) R w-w (Real.pi/3)
  let e2 := normalizedSymBumpPairing (Real.pi/2) R w-w (Real.pi/2)
  let e3 := normalizedSymBumpPairing Real.pi R w-w Real.pi
  have hlam0 : 0 <= lam := by linarith [hlam.1]
  have hlamAbs : |lam| <= 2/3 := by rw [abs_of_nonneg hlam0]; exact hlam.2
  have htri :
      |e0-e1+lam*e2+mu*e3|
        <= |e0|+|e1|+|lam|*|e2|+|mu|*|e3| := by
    calc
      |e0-e1+lam*e2+mu*e3|
        <= |e0-e1+lam*e2|+|mu*e3| := abs_add _ _
      _ <= (|e0-e1|+|lam*e2|)+|mu|*|e3| := by
        gcongr
        · exact abs_add _ _
        · rw [abs_mul]
      _ <= (|e0|+|e1|)+|lam|*|e2|+|mu|*|e3| := by
        gcongr
        exact abs_sub _ _
  unfold quarticFourWindowPairing quarticFourAtomicPairingAt
  have hid :
      normalizedSymBumpPairing 0 R w
        - normalizedSymBumpPairing (Real.pi/3) R w
        + lam*normalizedSymBumpPairing (Real.pi/2) R w
        + mu*normalizedSymBumpPairing Real.pi R w
        - (w 0-w (Real.pi/3)+lam*w (Real.pi/2)+mu*w Real.pi)
      = e0-e1+lam*e2+mu*e3 := by
    dsimp [e0,e1,e2,e3]
    ring
  rw [hid]
  calc
    |e0-e1+lam*e2+mu*e3|
      <= |e0|+|e1|+|lam|*|e2|+|mu|*|e3| := htri
    _ <= eta+eta+(2/3:ℝ)*eta+(1/10:ℝ)*eta := by gcongr
    _ <= 3*eta := by nlinarith

private theorem fourWindowPolePairing_error_uniform
    {t c R lam mu eta : ℝ}
    (ht : 200 <= t) (hc : |c| <= 2)
    (hR : 0 < R) (hR1 : R < 1)
    (hlam : lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ))
    (hmu : |mu| <= 1/10)
    (hsmall : 3*quarticFourUniformPoleLipschitzConstant*R <= eta) :
    |quarticFourWindowPairing R lam mu (quarticFourNormalizedPoleWeight t c)
      - quarticFourAtomicPairingAt lam mu (quarticFourNormalizedPoleWeight t c)| <= eta := by
  have h0 := normalizedPoleBump_close_uniform ht hc hR hR1 (Or.inl rfl)
  have h1 := normalizedPoleBump_close_uniform ht hc hR hR1 (Or.inr (Or.inl rfl))
  have h2 := normalizedPoleBump_close_uniform ht hc hR hR1 (Or.inr (Or.inr (Or.inl rfl)))
  have h3 := normalizedPoleBump_close_uniform ht hc hR hR1 (Or.inr (Or.inr (Or.inr rfl)))
  have h := fourWindowPairing_error_le_three
    (mul_nonneg quarticFourUniformPoleLipschitzConstant_pos.le hR.le)
    hlam hmu h0 h1 h2 h3
  nlinarith

private theorem fourWindowOnLinePairing_error_uniform
    {c R lam mu eta : ℝ}
    (hc : |c| <= 2) (hR : 0 < R)
    (hlam : lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ))
    (hmu : |mu| <= 1/10)
    (hsmall : 6*R <= eta) :
    |quarticFourWindowPairing R lam mu (quarticFourNormalizedOnLineWeight c)
      - quarticFourAtomicPairingAt lam mu (quarticFourNormalizedOnLineWeight c)| <= eta := by
  have h0 := normalizedOnLineBump_close_uniform hc hR (Or.inl rfl)
  have h1 := normalizedOnLineBump_close_uniform hc hR (Or.inr (Or.inl rfl))
  have h2 := normalizedOnLineBump_close_uniform hc hR (Or.inr (Or.inr (Or.inl rfl)))
  have h3 := normalizedOnLineBump_close_uniform hc hR (Or.inr (Or.inr (Or.inr rfl)))
  have h := fourWindowPairing_error_le_three (by positivity) hlam hmu h0 h1 h2 h3
  nlinarith

private theorem atomicPoleWeight_abs_le_fourL_add_one
    {t c a : ℝ}
    (ht : 200 <= t) (hc : |c| <= 2)
    (ha : isQuarticFourCentre a) :
    |quarticFourNormalizedPoleWeight t c a|
      <= 4*quarticFourUniformPoleLipschitzConstant+1 := by
  have ha6 := quarticFourCentre_mem_six ha
  have h06 : (0:ℝ) ∈ Set.Icc (-6:ℝ) 6 := by norm_num
  have hLip := quarticFourNormalizedPoleWeight_sub_abs_le_uniform
    ht hc ha6 h06
  have ha4 := quarticFourCentre_abs_le_four ha
  have hzero : quarticFourNormalizedPoleWeight t c 0 = 1 := by
    unfold quarticFourNormalizedPoleWeight
    simp
  have htri :
      |quarticFourNormalizedPoleWeight t c a|
        <= |quarticFourNormalizedPoleWeight t c a
              - quarticFourNormalizedPoleWeight t c 0|
          + |quarticFourNormalizedPoleWeight t c 0| := by
    have h := abs_add
      (quarticFourNormalizedPoleWeight t c a-quarticFourNormalizedPoleWeight t c 0)
      (quarticFourNormalizedPoleWeight t c 0)
    simpa using h
  rw [hzero, abs_one] at htri
  exact htri.trans (by
    have hscale := mul_le_mul_of_nonneg_left ha4
      quarticFourUniformPoleLipschitzConstant_pos.le
    nlinarith)

private theorem atomicPairing_abs_le_three_mul
    {lam mu B : ℝ} {w : ℝ -> ℝ}
    (hB : 0 <= B)
    (hlam : lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ))
    (hmu : |mu| <= 1/10)
    (h0 : |w 0| <= B)
    (h1 : |w (Real.pi/3)| <= B)
    (h2 : |w (Real.pi/2)| <= B)
    (h3 : |w Real.pi| <= B) :
    |quarticFourAtomicPairingAt lam mu w| <= 3*B := by
  have hlam0 : 0 <= lam := by linarith [hlam.1]
  have hlamAbs : |lam| <= 2/3 := by rw [abs_of_nonneg hlam0]; exact hlam.2
  unfold quarticFourAtomicPairingAt
  calc
    |w 0-w (Real.pi/3)+lam*w (Real.pi/2)+mu*w Real.pi|
      <= |w 0|+|w (Real.pi/3)|+|lam|*|w (Real.pi/2)|+|mu|*|w Real.pi| := by
        calc
          _ <= |w 0-w (Real.pi/3)+lam*w (Real.pi/2)|+|mu*w Real.pi| := abs_add _ _
          _ <= (|w 0-w (Real.pi/3)|+|lam*w (Real.pi/2)|)+|mu|*|w Real.pi| := by
            gcongr
            · exact abs_add _ _
            · rw [abs_mul]
          _ <= (|w 0|+|w (Real.pi/3)|)+|lam|*|w (Real.pi/2)|+|mu|*|w Real.pi| := by
            gcongr
            exact abs_sub _ _
    _ <= B+B+(2/3:ℝ)*B+(1/10:ℝ)*B := by gcongr
    _ <= 3*B := by nlinarith

private theorem atomicPolePairing_abs_le_uniform
    {t c lam mu : ℝ}
    (ht : 200 <= t) (hc : |c| <= 2)
    (hlam : lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ))
    (hmu : |mu| <= 1/10) :
    |quarticFourAtomicPairingAt lam mu (quarticFourNormalizedPoleWeight t c)|
      <= 3*(4*quarticFourUniformPoleLipschitzConstant+1) := by
  apply atomicPairing_abs_le_three_mul (by positivity) hlam hmu
  · exact atomicPoleWeight_abs_le_fourL_add_one ht hc (Or.inl rfl)
  · exact atomicPoleWeight_abs_le_fourL_add_one ht hc (Or.inr (Or.inl rfl))
  · exact atomicPoleWeight_abs_le_fourL_add_one ht hc (Or.inr (Or.inr (Or.inl rfl)))
  · exact atomicPoleWeight_abs_le_fourL_add_one ht hc (Or.inr (Or.inr (Or.inr rfl)))

private theorem atomicOnLinePairing_abs_le_three
    {c lam mu : ℝ}
    (hlam : lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ))
    (hmu : |mu| <= 1/10) :
    |quarticFourAtomicPairingAt lam mu (quarticFourNormalizedOnLineWeight c)| <= 3 := by
  apply atomicPairing_abs_le_three_mul (by norm_num) hlam hmu <;>
    unfold quarticFourNormalizedOnLineWeight <;>
    rw [abs_le] <;>
    exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

/-- Uniform-in-t localization of the normalized smooth pole determinant. -/
theorem exists_uniform_radius_quarticFourSmoothPole_close_atomic_public
    {eps : ℝ} (heps : 0 < eps) :
    UniformQuarticFourSmoothPoleLocalization eps := by
  let B : ℝ := 3*(4*quarticFourUniformPoleLipschitzConstant+1)+3
  let eta : ℝ := min 1 (eps/(2*(4*B+2)))
  have hB : 0 <= B := by dsimp [B]; positivity
  have heta : 0 < eta := by
    dsimp [eta]
    exact lt_min (by norm_num) (div_pos heps (by positivity))
  let delta : ℝ := min 1 (eta/(12*quarticFourUniformPoleLipschitzConstant))
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (by norm_num) (div_pos heta (by positivity))
  refine ⟨delta,hdelta,?_⟩
  intro t R lam mu ht hR hRd hlam hmu
  have hR1 : R < 1 := hRd.trans_le (min_le_left _ _)
  have hRsmall : R < eta/(12*quarticFourUniformPoleLipschitzConstant) :=
    hRd.trans_le (min_le_right _ _)
  have hPoleSmall : 3*quarticFourUniformPoleLipschitzConstant*R <= eta := by
    have hden : 0 < 12*quarticFourUniformPoleLipschitzConstant := by positivity
    rw [lt_div_iff₀ hden] at hRsmall
    nlinarith [quarticFourUniformPoleLipschitzConstant_pos]
  have hOnSmall : 6*R <= eta := by
    have hL19 : 19 <= quarticFourUniformPoleLipschitzConstant := by
      unfold quarticFourUniformPoleLipschitzConstant
      nlinarith [Real.one_le_cosh 1]
    nlinarith [hPoleSmall]
  have ha := fourWindowPolePairing_error_uniform
    ht (by norm_num : |(1:ℝ)| <= 2) hR hR1 hlam hmu hPoleSmall
  have hb := fourWindowOnLinePairing_error_uniform
    (by norm_num : |(2:ℝ)| <= 2) hR hlam hmu hOnSmall
  have hc := fourWindowPolePairing_error_uniform
    ht (by norm_num : |(2:ℝ)| <= 2) hR hR1 hlam hmu hPoleSmall
  have hd := fourWindowOnLinePairing_error_uniform
    (by norm_num : |(1:ℝ)| <= 2) hR hlam hmu hOnSmall
  have hp1 := atomicPolePairing_abs_le_uniform ht (by norm_num : |(1:ℝ)| <= 2) hlam hmu
  have hp2 := atomicPolePairing_abs_le_uniform ht (by norm_num : |(2:ℝ)| <= 2) hlam hmu
  have ho1 := atomicOnLinePairing_abs_le_three (c:=(1:ℝ)) hlam hmu
  have ho2 := atomicOnLinePairing_abs_le_three (c:=(2:ℝ)) hlam hmu
  have ha0 : |quarticFourAtomicPairingAt lam mu (quarticFourNormalizedPoleWeight t 1)| <= B := by
    dsimp [B]
    linarith
  have hb0 : |quarticFourAtomicPairingAt lam mu (quarticFourNormalizedOnLineWeight 2)| <= B := by
    dsimp [B]
    nlinarith [quarticFourUniformPoleLipschitzConstant_pos]
  have hc0 : |quarticFourAtomicPairingAt lam mu (quarticFourNormalizedPoleWeight t 2)| <= B := by
    dsimp [B]
    linarith
  have hd0 : |quarticFourAtomicPairingAt lam mu (quarticFourNormalizedOnLineWeight 1)| <= B := by
    dsimp [B]
    nlinarith [quarticFourUniformPoleLipschitzConstant_pos]
  have hdet := abs_det_sub_det_le hB heta.le (min_le_left _ _)
    ha0 hb0 hc0 hd0 ha hb hc hd
  unfold quarticFourSmoothFinitePoleResidual quarticFourAtomicFinitePoleDeterminant at hdet
  rw [quarticFourAtomicFinitePoleDeterminant_eq_residual (by linarith : t ≠ 0)] at hdet
  exact hdet.trans (by
    have hetaRight : eta <= eps/(2*(4*B+2)) := min_le_right _ _
    have hcoef : 0 <= 4*B+2 := by positivity
    have hs := mul_le_mul_of_nonneg_left hetaRight hcoef
    have hden : 0 < 4*B+2 := by positivity
    field_simp [ne_of_gt hden] at hs ⊢
    nlinarith)

/-- The determinant compiler target is now inhabited by the explicit uniform
pole-weight modulus. -/
theorem uniformQuarticFourPoleDeterminantCompilerTarget_paid :
    UniformQuarticFourPoleDeterminantCompilerTarget :=
  exists_uniform_radius_quarticFourSmoothPole_close_atomic_public
    quarticFourUniformPoleLocalizationTolerance_pos

/-- Consequently there exists one fixed-width signed-pole core valid for every
physical ordinate t>=200. -/
theorem exists_uniformQuarticFourSignedPoleCore_public :
    Nonempty UniformQuarticFourSignedPoleCore :=
  fixedWidthCore_of_uniformPoleDeterminantCompilerTarget
    uniformQuarticFourPoleDeterminantCompilerTarget_paid

end Synthesis
