import Synthesis.RiemannProjectiveQuarticFourWindowUniformPoleWeight

/-!
# Pay the high-t uniform pole-localization radius

The preceding file gives a t-independent Lipschitz constant for the only
`t`-dependent normalized weights.  Here it is fed through the repository's
actual scaled symmetric bump localization.

For all t>=200, all four window centres lie in [-6,6], and R<1 keeps each
underlying bump inside that interval.  Hence every normalized pole pairing has
an explicit O(R) error with the same constant.  The ordinary on-line cosine
weights obey the smaller 2R error.  Combining the four normalized windows and
the existing determinant perturbation estimate yields

  exists delta>0, forall t>=200, 0<R<delta,
    |P_smooth(R,t)-P_atomic(t)| <= eps.

This is the quantifier swap that the older pointwise-in-t continuity proof did
not expose.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set
open scoped Real

/-- Extract the normalized-bump estimate when a support oscillation bound is
already available. -/
theorem normalizedSymBumpPairing_close_of_support_oscillation
    {a R eta : ℝ}
    (hR : 0 < R)
    (heta : 0 <= eta)
    {w : ℝ -> ℝ}
    (hw : Continuous w)
    (heven : ∀ u, w (-u) = w u)
    (hosc : ∀ u : ℝ, scaledUnitBump a R u ≠ 0 -> |w u-w a| <= eta) :
    |normalizedSymBumpPairing a R w - w a| <= eta := by
  have hloc := quantitativeSymBump_weighted_localization
    (c:=a) hR heta hw heven hosc
  have hmass : 0 < 2 * R * unitBumpMass0 := by
    have hM := unitBumpMass0_pos
    positivity
  unfold normalizedSymBumpPairing
  have hrewrite :
      (∫ u : ℝ, quantitativeSymBump a R u * w u)
          - (2*R*unitBumpMass0) * w a
        =
      (2*R*unitBumpMass0) *
        ((∫ u : ℝ, quantitativeSymBump a R u * w u)
            / (2*R*unitBumpMass0) - w a) := by
    field_simp [ne_of_gt hmass]
    ring
  rw [hrewrite, abs_mul, abs_of_pos hmass] at hloc
  exact (mul_le_mul_left hmass).mp hloc

private theorem windowCentre_abs_le_four
    {a : ℝ}
    (ha : a = 0 ∨ a = Real.pi/3 ∨ a = Real.pi/2 ∨ a = Real.pi) :
    |a| <= 4 := by
  rcases ha with rfl | rfl | rfl | rfl
  · norm_num
  · have hp0 := Real.pi_pos
    have hp4 := Real.pi_lt_four
    rw [abs_of_nonneg (by positivity : 0 <= Real.pi/3)]
    linarith
  · have hp0 := Real.pi_pos
    have hp4 := Real.pi_lt_four
    rw [abs_of_nonneg (by positivity : 0 <= Real.pi/2)]
    linarith
  · rw [abs_of_pos Real.pi_pos]
    exact Real.pi_lt_four.le

private theorem windowCentre_mem_six
    {a : ℝ}
    (ha : a = 0 ∨ a = Real.pi/3 ∨ a = Real.pi/2 ∨ a = Real.pi) :
    a ∈ Set.Icc (-6 : ℝ) 6 := by
  have habs := windowCentre_abs_le_four ha
  rw [abs_le] at habs
  exact ⟨by linarith [habs.1], by linarith [habs.2]⟩

private theorem scaledUnitBump_mem_six
    {a R u : ℝ}
    (hR1 : R < 1)
    (ha : a = 0 ∨ a = Real.pi/3 ∨ a = Real.pi/2 ∨ a = Real.pi)
    (hu : scaledUnitBump a R u ≠ 0) :
    u ∈ Set.Icc (-6 : ℝ) 6 := by
  have hs := scaledUnitBump_support (by
    have : 0 < R := by
      by_contra h
      have hnon : R <= 0 := le_of_not_gt h
      have hpos := scaledUnitBump_support_radius_pos_of_nonzero hu
      linarith
    exact this) hu
  have ha4 := windowCentre_abs_le_four ha
  have hutri : |u| <= |u-a| + |a| := by
    have := abs_add (u-a) a
    simpa [sub_add_cancel] using this
  have hu5 : |u| < 5 := by linarith
  rw [abs_lt] at hu5
  exact ⟨hu5.1.le.trans (by norm_num), hu5.2.le.trans (by norm_num)⟩

/-- One normalized pole bump is uniformly close to point evaluation. -/
theorem normalizedSymBumpPairing_poleWeight_close_uniform
    {t c a R : ℝ}
    (ht : 200 <= t)
    (hc : |c| <= 2)
    (hR : 0 < R) (hR1 : R < 1)
    (ha : a = 0 ∨ a = Real.pi/3 ∨ a = Real.pi/2 ∨ a = Real.pi) :
    |normalizedSymBumpPairing a R (quarticFourNormalizedPoleWeight t c)
      - quarticFourNormalizedPoleWeight t c a|
      <= quarticFourUniformPoleLipschitzConstant * R := by
  apply normalizedSymBumpPairing_close_of_support_oscillation hR
    (mul_nonneg quarticFourUniformPoleLipschitzConstant_pos.le hR.le)
    (quarticFourNormalizedPoleWeight_continuous t c)
    (quarticFourNormalizedPoleWeight_even t c)
  intro u hu
  have hu6 := scaledUnitBump_mem_six hR1 ha hu
  have ha6 := windowCentre_mem_six ha
  have hLip := quarticFourNormalizedPoleWeight_sub_abs_le_uniform
    ht hc hu6 ha6
  have hs := scaledUnitBump_support hR hu
  exact hLip.trans (mul_le_mul_of_nonneg_left hs.le
    quarticFourUniformPoleLipschitzConstant_pos.le)

/-- On-line cosine weights have the simpler uniform 2R localization error. -/
theorem normalizedSymBumpPairing_onLineWeight_close_uniform
    {c a R : ℝ}
    (hc : |c| <= 2)
    (hR : 0 < R)
    (ha : a = 0 ∨ a = Real.pi/3 ∨ a = Real.pi/2 ∨ a = Real.pi) :
    |normalizedSymBumpPairing a R (quarticFourNormalizedOnLineWeight c)
      - quarticFourNormalizedOnLineWeight c a|
      <= 2*R := by
  apply normalizedSymBumpPairing_close_of_support_oscillation hR (by positivity)
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
      have hmul := mul_le_mul hc hs.le (abs_nonneg _) (by norm_num : (0:ℝ) <= 2)
      exact hmul

private theorem fourWindowPairing_close_of_window_errors
    {R lam mu eta : ℝ}
    {w : ℝ -> ℝ}
    (heta : 0 <= eta)
    (hlam : lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ))
    (hmu : |mu| <= 1/10)
    (h0 : |normalizedSymBumpPairing 0 R w - w 0| <= eta)
    (h1 : |normalizedSymBumpPairing (Real.pi/3) R w - w (Real.pi/3)| <= eta)
    (h2 : |normalizedSymBumpPairing (Real.pi/2) R w - w (Real.pi/2)| <= eta)
    (h3 : |normalizedSymBumpPairing Real.pi R w - w Real.pi| <= eta) :
    |quarticFourWindowPairing R lam mu w
      - quarticFourAtomicPairingAt lam mu w| <= 3*eta := by
  let e0 := normalizedSymBumpPairing 0 R w - w 0
  let e1 := normalizedSymBumpPairing (Real.pi/3) R w - w (Real.pi/3)
  let e2 := normalizedSymBumpPairing (Real.pi/2) R w - w (Real.pi/2)
  let e3 := normalizedSymBumpPairing Real.pi R w - w Real.pi
  have hlam0 : 0 <= lam := by linarith [hlam.1]
  have hlamAbs : |lam| <= 2/3 := by rw [abs_of_nonneg hlam0]; exact hlam.2
  have htri :
      |e0-e1+lam*e2+mu*e3|
        <= |e0|+|e1|+|lam|*|e2|+|mu|*|e3| := by
    calc
      |e0-e1+lam*e2+mu*e3|
        <= |e0-e1+lam*e2| + |mu*e3| := abs_add _ _
      _ <= (|e0-e1|+|lam*e2|) + |mu|*|e3| := by
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
    _ <= eta+eta+(2/3:ℝ)*eta+(1/10:ℝ)*eta := by
      gcongr
    _ <= 3*eta := by nlinarith

/-- Uniform whole four-window pairing localization for the t-dependent pole
weight. -/
theorem quarticFourWindowPolePairing_close_atomic_uniform
    {t c R lam mu eta : ℝ}
    (ht : 200 <= t)
    (hc : |c| <= 2)
    (hR : 0 < R) (hR1 : R < 1)
    (hlam : lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ))
    (hmu : |mu| <= 1/10)
    (hsmall : 3 * quarticFourUniformPoleLipschitzConstant * R <= eta) :
    |quarticFourWindowPairing R lam mu (quarticFourNormalizedPoleWeight t c)
      - quarticFourAtomicPairingAt lam mu (quarticFourNormalizedPoleWeight t c)| <= eta := by
  have hL0 := normalizedSymBumpPairing_poleWeight_close_uniform ht hc hR hR1
    (Or.inl rfl : (0:ℝ)=0 ∨ _)
  have hL1 := normalizedSymBumpPairing_poleWeight_close_uniform ht hc hR hR1
    (Or.inr (Or.inl rfl) : (Real.pi/3:ℝ)=0 ∨ _)
  have hL2 := normalizedSymBumpPairing_poleWeight_close_uniform ht hc hR hR1
    (Or.inr (Or.inr (Or.inl rfl)) : (Real.pi/2:ℝ)=0 ∨ _)
  have hL3 := normalizedSymBumpPairing_poleWeight_close_uniform ht hc hR hR1
    (Or.inr (Or.inr (Or.inr rfl)) : (Real.pi:ℝ)=0 ∨ _)
  have h3 := fourWindowPairing_close_of_window_errors
    (mul_nonneg quarticFourUniformPoleLipschitzConstant_pos.le hR.le)
    hlam hmu hL0 hL1 hL2 hL3
  exact h3.trans (by ring_nf at hsmall ⊢; exact hsmall)

/-- Same uniform whole-pairing estimate for the t-independent on-line weights. -/
theorem quarticFourWindowOnLinePairing_close_atomic_uniform
    {c R lam mu eta : ℝ}
    (hc : |c| <= 2)
    (hR : 0 < R)
    (hlam : lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ))
    (hmu : |mu| <= 1/10)
    (hsmall : 6*R <= eta) :
    |quarticFourWindowPairing R lam mu (quarticFourNormalizedOnLineWeight c)
      - quarticFourAtomicPairingAt lam mu (quarticFourNormalizedOnLineWeight c)| <= eta := by
  have h0 := normalizedSymBumpPairing_onLineWeight_close_uniform hc hR
    (Or.inl rfl : (0:ℝ)=0 ∨ _)
  have h1 := normalizedSymBumpPairing_onLineWeight_close_uniform hc hR
    (Or.inr (Or.inl rfl) : (Real.pi/3:ℝ)=0 ∨ _)
  have h2 := normalizedSymBumpPairing_onLineWeight_close_uniform hc hR
    (Or.inr (Or.inr (Or.inl rfl)) : (Real.pi/2:ℝ)=0 ∨ _)
  have h3 := normalizedSymBumpPairing_onLineWeight_close_uniform hc hR
    (Or.inr (Or.inr (Or.inr rfl)) : (Real.pi:ℝ)=0 ∨ _)
  have h := fourWindowPairing_close_of_window_errors (by positivity)
    hlam hmu h0 h1 h2 h3
  exact h.trans (by nlinarith)

/-- The previously-open uniform high-t smooth-pole localization theorem. -/
theorem exists_uniform_radius_quarticFourSmoothPole_close_atomic
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ t R lam mu : ℝ,
        200 <= t ->
        0 < R -> R < delta ->
        lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) ->
        |mu| <= 1/10 ->
        |quarticFourSmoothFinitePoleResidual R lam mu t
          - quarticFourAtomicFinitePoleResidual t lam mu| <= eps := by
  let M : ℝ := 5
  let eta : ℝ := min 1 (eps/100)
  have heta : 0 < eta := by
    dsimp [eta]
    exact lt_min (by norm_num) (by positivity)
  have hL : 0 < quarticFourUniformPoleLipschitzConstant :=
    quarticFourUniformPoleLipschitzConstant_pos
  let delta : ℝ := min 1 (eta / (12*quarticFourUniformPoleLipschitzConstant))
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
    nlinarith [hL]
  have hOnSmall : 6*R <= eta := by
    have hcosh1 : 1 <= Real.cosh 1 := Real.one_le_cosh 1
    have hL19 : 19 <= quarticFourUniformPoleLipschitzConstant := by
      unfold quarticFourUniformPoleLipschitzConstant
      nlinarith
    nlinarith [hPoleSmall]
  have ha := quarticFourWindowPolePairing_close_atomic_uniform
    ht (by norm_num : |(1:ℝ)| <= 2) hR hR1 hlam hmu hPoleSmall
  have hb := quarticFourWindowOnLinePairing_close_atomic_uniform
    (by norm_num : |(2:ℝ)| <= 2) hR hlam hmu hOnSmall
  have hc := quarticFourWindowPolePairing_close_atomic_uniform
    ht (by norm_num : |(2:ℝ)| <= 2) hR hR1 hlam hmu hPoleSmall
  have hd := quarticFourWindowOnLinePairing_close_atomic_uniform
    (by norm_num : |(1:ℝ)| <= 2) hR hlam hmu hOnSmall
  have ha0 :
      |quarticFourAtomicPairingAt lam mu (quarticFourNormalizedPoleWeight t 1)| <= M := by
    exact (quarticFourAtomicPole_entries_abs_le_five ht hlam hmu).1
  have hb0 :
      |quarticFourAtomicPairingAt lam mu (quarticFourNormalizedOnLineWeight 2)| <= M := by
    exact (quarticFourAtomicPole_entries_abs_le_five ht hlam hmu).2.1
  have hc0 :
      |quarticFourAtomicPairingAt lam mu (quarticFourNormalizedPoleWeight t 2)| <= M := by
    exact (quarticFourAtomicPole_entries_abs_le_five ht hlam hmu).2.2.1
  have hd0 :
      |quarticFourAtomicPairingAt lam mu (quarticFourNormalizedOnLineWeight 1)| <= M := by
    exact (quarticFourAtomicPole_entries_abs_le_five ht hlam hmu).2.2.2
  have hdet := abs_det_sub_det_le (by norm_num : (0:ℝ) <= M)
    heta.le (min_le_left _ _) ha0 hb0 hc0 hd0 ha hb hc hd
  unfold quarticFourSmoothFinitePoleResidual quarticFourAtomicFinitePoleDeterminant at hdet
  rw [quarticFourAtomicFinitePoleDeterminant_eq_residual (by linarith : t ≠ 0)] at hdet
  exact hdet.trans (by
    have hetaEps : eta <= eps/100 := min_le_right _ _
    have hscale := mul_le_mul_of_nonneg_left hetaEps (by norm_num : (0:ℝ) <= 22)
    calc
      (4*M+2)*eta = 22*eta := by dsimp [M]; ring
      _ <= 22*(eps/100) := hscale
      _ <= eps := by nlinarith [heps])

/-- The uniform-pole-localization proposition is now inhabited at every positive
tolerance. -/
theorem uniformQuarticFourSmoothPoleLocalization
    {eta : ℝ} (heta : 0 < eta) :
    UniformQuarticFourSmoothPoleLocalization eta :=
  exists_uniform_radius_quarticFourSmoothPole_close_atomic heta

/-- Consequently the fixed-width smooth signed-pole core exists unconditionally
on the high-t regime. -/
theorem exists_uniformQuarticFourSignedPoleCore :
    Nonempty UniformQuarticFourSignedPoleCore :=
  exists_uniformQuarticFourSignedPoleCore_of_uniformPoleLocalization
    (uniformQuarticFourSmoothPoleLocalization
      quarticFourUniformPoleLocalizationTolerance_pos)

end Synthesis
