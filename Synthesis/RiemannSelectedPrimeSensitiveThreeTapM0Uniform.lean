import Synthesis.RiemannSelectedPrimeSensitiveThreeTapM0Envelope
import Synthesis.RiemannQuantitativeSymmetricBumpMass

/-!
# Explicit uniform M0 bound

The previous owner reduced the translated/projectivized mass to two elementary
source quantities: endpoint-profile L1 mass and signed pole coefficients.
Both are uniformly bounded on the actual four-window witness corridor.

* each normalized four-window source has L1 mass <= 3;
* each normalized finite pole determinant has absolute value <= 18 cosh(1)
  for t >= 200 and R < 1;
* therefore

    M0 <= 2592 cosh(1)^2 (1 + 2 |eps|)^2.

This removes M0 as a zeta-distribution input.  The bound is intentionally
coarse; its role is to prove the finite core is genuinely O(log t / t) for a
fixed tap strength.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set
open scoped Real BigOperators

/-- L1 triangle inequality for continuous compact real profiles. -/
theorem taperMass_add_le
    {f g : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    taperMass (fun u => f u + g u) <= taperMass f + taperMass g := by
  have hfi : Integrable (fun u : ℝ => |f u|) :=
    hf.abs.integrable_of_hasCompactSupport hfc.abs
  have hgi : Integrable (fun u : ℝ => |g u|) :=
    hg.abs.integrable_of_hasCompactSupport hgc.abs
  have hfgi : Integrable (fun u : ℝ => |f u + g u|) :=
    (hf.add hg).abs.integrable_of_hasCompactSupport (hfc.add hgc).abs
  unfold taperMass
  have h := integral_mono hfgi (hfi.add hgi) (fun u => abs_add _ _)
  rw [integral_add hfi hgi] at h
  exact h

/-- L1 triangle inequality for subtraction. -/
theorem taperMass_sub_le
    {f g : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    taperMass (fun u => f u - g u) <= taperMass f + taperMass g := by
  have hfi : Integrable (fun u : ℝ => |f u|) :=
    hf.abs.integrable_of_hasCompactSupport hfc.abs
  have hgi : Integrable (fun u : ℝ => |g u|) :=
    hg.abs.integrable_of_hasCompactSupport hgc.abs
  have hfgi : Integrable (fun u : ℝ => |f u - g u|) :=
    (hf.sub hg).abs.integrable_of_hasCompactSupport (hfc.sub hgc).abs
  unfold taperMass
  have h := integral_mono hfgi (hfi.add hgi) (fun u => abs_sub _ _)
  rw [integral_add hfi hgi] at h
  exact h

/-- Absolute mass scales by the absolute scalar. -/
theorem taperMass_const_mul_eq
    (a : ℝ) (f : ℝ → ℝ) :
    taperMass (fun u => a * f u) = |a| * taperMass f := by
  unfold taperMass
  rw [show (fun u : ℝ => |a * f u|) = fun u => |a| * |f u| by
    funext u
    rw [abs_mul], integral_const_mul]

/-- The normalized four-window carrier has a uniform source L1 bound on the
full coefficient corridor used by the selected witness. -/
theorem quarticFourWindowProfile_taperMass_le_three
    {R lam mu : ℝ}
    (hR : 0 < R)
    (hlam : lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ))
    (hmu : |mu| <= 1/10) :
    taperMass (quarticFourWindowProfile R lam mu) <= 3 := by
  let b0 : ℝ → ℝ := quantitativeSymBump 0 R
  let b1 : ℝ → ℝ := quantitativeSymBump (Real.pi/3) R
  let b2 : ℝ → ℝ := quantitativeSymBump (Real.pi/2) R
  let b3 : ℝ → ℝ := quantitativeSymBump Real.pi R
  have h0c : Continuous b0 :=
    (quantitativeSymBump_contDiff (c:=0) hR.ne').continuous
  have h1c : Continuous b1 :=
    (quantitativeSymBump_contDiff (c:=Real.pi/3) hR.ne').continuous
  have h2c : Continuous b2 :=
    (quantitativeSymBump_contDiff (c:=Real.pi/2) hR.ne').continuous
  have h3c : Continuous b3 :=
    (quantitativeSymBump_contDiff (c:=Real.pi) hR.ne').continuous
  have h0k : HasCompactSupport b0 := quantitativeSymBump_hasCompactSupport hR
  have h1k : HasCompactSupport b1 := quantitativeSymBump_hasCompactSupport hR
  have h2k : HasCompactSupport b2 := quantitativeSymBump_hasCompactSupport hR
  have h3k : HasCompactSupport b3 := quantitativeSymBump_hasCompactSupport hR
  let m := quarticWindowMass R
  have hm : 0 < m := quarticWindowMass_pos hR
  have hb0 : taperMass b0 <= m := by
    dsimp [b0,m]
    simpa [quarticWindowMass] using
      (taperMass_quantitativeSymBump_le (c:=0) hR)
  have hb1 : taperMass b1 <= m := by
    dsimp [b1,m]
    simpa [quarticWindowMass] using
      (taperMass_quantitativeSymBump_le (c:=Real.pi/3) hR)
  have hb2 : taperMass b2 <= m := by
    dsimp [b2,m]
    simpa [quarticWindowMass] using
      (taperMass_quantitativeSymBump_le (c:=Real.pi/2) hR)
  have hb3 : taperMass b3 <= m := by
    dsimp [b3,m]
    simpa [quarticWindowMass] using
      (taperMass_quantitativeSymBump_le (c:=Real.pi) hR)
  have hlam0 : 0 <= lam := by linarith [hlam.1]
  have hlamAbs : |lam| <= 2/3 := by
    rw [abs_of_nonneg hlam0]
    exact hlam.2
  have h01 := taperMass_sub_le h0c h0k h1c h1k
  have h2scale : taperMass (fun u => lam * b2 u) = |lam| * taperMass b2 :=
    taperMass_const_mul_eq lam b2
  have h3scale : taperMass (fun u => mu * b3 u) = |mu| * taperMass b3 :=
    taperMass_const_mul_eq mu b3
  have h012 := taperMass_add_le
    (h0c.sub h1c) (h0k.sub h1k)
    (continuous_const.mul h2c) h2k.mul_left
  have hraw := taperMass_add_le
    ((h0c.sub h1c).add (continuous_const.mul h2c))
    ((h0k.sub h1k).add h2k.mul_left)
    (continuous_const.mul h3c) h3k.mul_left
  have hrawBound : taperMass (quarticFourWindowRaw R lam mu) <= 3*m := by
    unfold quarticFourWindowRaw at hraw ⊢
    rw [h2scale, h3scale] at h012 hraw
    have h2mul := mul_le_mul hlamAbs hb2 (by positivity) (by positivity)
    have h3mul := mul_le_mul hmu hb3 (by positivity) (by positivity)
    calc
      taperMass (fun u => b0 u - b1 u + lam*b2 u + mu*b3 u)
        <= taperMass (fun u => b0 u-b1 u+lam*b2 u)
          + |mu| * taperMass b3 := hraw
      _ <= (taperMass (fun u => b0 u-b1 u) + |lam|*taperMass b2)
          + |mu|*taperMass b3 := by linarith
      _ <= (m+m) + (2/3:ℝ)*m + (1/10:ℝ)*m := by
        gcongr
      _ <= 3*m := by nlinarith [hm.le]
  unfold quarticFourWindowProfile
  rw [taperMass_const_mul_eq]
  rw [abs_of_pos (inv_pos.mpr hm)]
  have hscaled := mul_le_mul_of_nonneg_left hrawBound (inv_nonneg.mpr hm.le)
  calc
    m⁻¹ * taperMass (quarticFourWindowRaw R lam mu)
      <= m⁻¹ * (3*m) := hscaled
    _ = 3 := by field_simp [ne_of_gt hm]

/-- A normalized pairing is bounded by profile mass times a pointwise bound on
its weight over the profile support. -/
theorem abs_quarticFourWindowPairing_le
    {R lam mu K : ℝ}
    (hR : 0 < R)
    (hK : 0 <= K)
    {w : ℝ → ℝ}
    (hw : Continuous w)
    (hwBound : ∀ v : ℝ,
      quarticFourWindowProfile R lam mu v ≠ 0 -> |w v| <= K) :
    |quarticFourWindowPairing R lam mu w|
      <= K * taperMass (quarticFourWindowProfile R lam mu) := by
  let G := quarticFourWindowProfile R lam mu
  have hGc : Continuous G := quarticFourWindowProfile_continuous hR
  have hGk : HasCompactSupport G := quarticFourWindowProfile_compact hR
  have hi : Integrable (fun v : ℝ => G v * w v) :=
    (hGc.mul hw).integrable_of_hasCompactSupport hGk.mul_right
  have hGabs : Integrable (fun v : ℝ => |G v|) :=
    hGc.abs.integrable_of_hasCompactSupport hGk.abs
  rw [← quarticFourWindowProfile_pairing_eq hR hw]
  calc
    |∫ v : ℝ, G v * w v|
      <= ∫ v : ℝ, |G v * w v| := abs_integral_le_integral_abs
    _ <= ∫ v : ℝ, K * |G v| := by
      apply integral_mono hi.abs (hGabs.const_mul K)
      intro v
      by_cases hv : G v = 0
      · simp [hv, hK]
      · rw [abs_mul]
        have hb := hwBound v hv
        have hG0 : 0 <= |G v| := abs_nonneg _
        nlinarith
    _ = K * taperMass G := by
      rw [integral_const_mul]
      rfl

/-- On the actual support and for t>=200 the pole weight is bounded by cosh(1). -/
theorem quarticFourNormalizedPoleWeight_abs_le_cosh_one
    {R lam mu t c v : ℝ}
    (ht : 200 <= t)
    (hR : 0 < R)
    (hRone : R < 1)
    (hv : quarticFourWindowProfile R lam mu v ≠ 0) :
    |quarticFourNormalizedPoleWeight t c v| <= Real.cosh 1 := by
  have hs := quarticFourWindowProfile_support_abs_lt hR hv
  have hv5 : |v| < 5 := by
    nlinarith [Real.pi_lt_four, hRone]
  have ht0 : 0 < t := by linarith
  have hx : |8*v/t| <= 1 := by
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) <= 8),
      abs_of_pos ht0]
    rw [div_le_iff₀ ht0]
    nlinarith
  have hcosh : Real.cosh (8*v/t) <= Real.cosh 1 := by
    apply (Real.cosh_le_cosh).2
    simpa using hx
  have hc1 : |Real.cos (16*v)| <= 1 := by
    rw [abs_le]
    exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hc2 : |Real.cos (c*v)| <= 1 := by
    rw [abs_le]
    exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  unfold quarticFourNormalizedPoleWeight
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.cosh_nonneg _)]
  calc
    Real.cosh (8*v/t) * |Real.cos (16*v)| * |Real.cos (c*v)|
      <= Real.cosh (8*v/t) * 1 * 1 := by
        gcongr
    _ <= Real.cosh 1 := by simpa using hcosh

/-- On-line cosine weights have unit modulus bound. -/
theorem quarticFourNormalizedOnLineWeight_abs_le_one
    (c v : ℝ) :
    |quarticFourNormalizedOnLineWeight c v| <= 1 := by
  unfold quarticFourNormalizedOnLineWeight
  rw [abs_le]
  exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

/-- Uniform absolute bound for the normalized finite pole determinant. -/
theorem quarticFourSmoothFinitePoleResidual_abs_le
    {R lam mu t : ℝ}
    (ht : 200 <= t)
    (hR : 0 < R)
    (hRone : R < 1)
    (hlam : lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ))
    (hmu : |mu| <= 1/10) :
    |quarticFourSmoothFinitePoleResidual R lam mu t|
      <= 18 * Real.cosh 1 := by
  have hmass := quarticFourWindowProfile_taperMass_le_three hR hlam hmu
  have hp1 := abs_quarticFourWindowPairing_le hR (Real.cosh_nonneg 1)
    (quarticFourNormalizedPoleWeight_continuous t 1)
    (fun v hv => quarticFourNormalizedPoleWeight_abs_le_cosh_one ht hR hRone hv)
  have hp2 := abs_quarticFourWindowPairing_le hR (Real.cosh_nonneg 1)
    (quarticFourNormalizedPoleWeight_continuous t 2)
    (fun v hv => quarticFourNormalizedPoleWeight_abs_le_cosh_one ht hR hRone hv)
  have ho1 := abs_quarticFourWindowPairing_le hR (by norm_num : (0:ℝ) <= 1)
    (quarticFourNormalizedOnLineWeight_continuous 1)
    (fun v hv => quarticFourNormalizedOnLineWeight_abs_le_one 1 v)
  have ho2 := abs_quarticFourWindowPairing_le hR (by norm_num : (0:ℝ) <= 1)
    (quarticFourNormalizedOnLineWeight_continuous 2)
    (fun v hv => quarticFourNormalizedOnLineWeight_abs_le_one 2 v)
  have hp1' : |quarticFourWindowPairing R lam mu
      (quarticFourNormalizedPoleWeight t 1)| <= 3*Real.cosh 1 := by
    exact hp1.trans (mul_le_mul_of_nonneg_left hmass (Real.cosh_nonneg 1))
  have hp2' : |quarticFourWindowPairing R lam mu
      (quarticFourNormalizedPoleWeight t 2)| <= 3*Real.cosh 1 := by
    exact hp2.trans (mul_le_mul_of_nonneg_left hmass (Real.cosh_nonneg 1))
  have ho1' : |quarticFourWindowPairing R lam mu
      (quarticFourNormalizedOnLineWeight 1)| <= 3 := by simpa using ho1.trans hmass
  have ho2' : |quarticFourWindowPairing R lam mu
      (quarticFourNormalizedOnLineWeight 2)| <= 3 := by simpa using ho2.trans hmass
  unfold quarticFourSmoothFinitePoleResidual
  calc
    |quarticFourWindowPairing R lam mu (quarticFourNormalizedPoleWeight t 1)
        * quarticFourWindowPairing R lam mu (quarticFourNormalizedOnLineWeight 2)
      - quarticFourWindowPairing R lam mu (quarticFourNormalizedPoleWeight t 2)
        * quarticFourWindowPairing R lam mu (quarticFourNormalizedOnLineWeight 1)|
      <= |quarticFourWindowPairing R lam mu (quarticFourNormalizedPoleWeight t 1)|
          * |quarticFourWindowPairing R lam mu (quarticFourNormalizedOnLineWeight 2)|
        + |quarticFourWindowPairing R lam mu (quarticFourNormalizedPoleWeight t 2)|
          * |quarticFourWindowPairing R lam mu (quarticFourNormalizedOnLineWeight 1)| := by
            rw [abs_mul, abs_mul]
            exact abs_sub _ _
    _ <= (3*Real.cosh 1)*3 + (3*Real.cosh 1)*3 := by
      gcongr
    _ = 18 * Real.cosh 1 := by ring

/-- The selected witness endpoint source masses are uniformly <= 3. -/
theorem QuarticFourSignedPolePair.endpointSourceMass_le_three
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    taperMass (quarticFourWindowProfile W.R (1/2) W.muHalf) <= 3
      ∧ taperMass (quarticFourWindowProfile W.R (2/3) W.muTwo) <= 3 := by
  have hHalfMu := quarticFourAtomicMu_corridor_abs_lt_tenth
    (by norm_num : (1/2 : ℝ) <= 1/2)
    (by norm_num : (1/2 : ℝ) <= 2/3) W.muHalfNear
  have hTwoMu := quarticFourAtomicMu_corridor_abs_lt_tenth
    (by norm_num : (1/2 : ℝ) <= 2/3)
    (by norm_num : (2/3 : ℝ) <= 2/3) W.muTwoNear
  constructor
  · exact quarticFourWindowProfile_taperMass_le_three W.Rpos
      ⟨le_rfl, by norm_num⟩ hHalfMu.le
  · exact quarticFourWindowProfile_taperMass_le_three W.Rpos
      ⟨by norm_num, le_rfl⟩ hTwoMu.le

/-- The selected witness pole coefficients are uniformly bounded. -/
theorem QuarticFourSignedPolePair.endpointPoleAbs_le
    {t : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    |W.poleHalf| <= 18 * Real.cosh 1
      ∧ |W.poleTwo| <= 18 * Real.cosh 1 := by
  have hHalfMu := quarticFourAtomicMu_corridor_abs_lt_tenth
    (by norm_num : (1/2 : ℝ) <= 1/2)
    (by norm_num : (1/2 : ℝ) <= 2/3) W.muHalfNear
  have hTwoMu := quarticFourAtomicMu_corridor_abs_lt_tenth
    (by norm_num : (1/2 : ℝ) <= 2/3)
    (by norm_num : (2/3 : ℝ) <= 2/3) W.muTwoNear
  unfold QuarticFourSignedPolePair.poleHalf QuarticFourSignedPolePair.poleTwo
  constructor
  · exact quarticFourSmoothFinitePoleResidual_abs_le ht W.Rpos W.RltOne
      ⟨le_rfl, by norm_num⟩ hHalfMu.le
  · exact quarticFourSmoothFinitePoleResidual_abs_le ht W.Rpos W.RltOne
      ⟨by norm_num, le_rfl⟩ hTwoMu.le

/-- Explicit uniform canonical mass bound.  In particular, for fixed eps the
finite one-scale budget really is O(log t / t). -/
theorem QuarticFourSignedPolePair.threeTapCanonicalM0_le_uniform
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapCanonicalM0 eps
      <= 2592 * (Real.cosh 1)^2 * (1 + 2*|eps|)^2 := by
  rcases W.endpointSourceMass_le_three with ⟨hHalf,hTwo⟩
  rcases W.endpointPoleAbs_le ht with ⟨hpHalf,hpTwo⟩
  have h := W.threeTapCanonicalM0_le_of_sourceMass_poleBounds
    (B:=3) (P:=18*Real.cosh 1) (eps:=eps)
    (by norm_num) hHalf hTwo
    (mul_nonneg (by norm_num) (Real.cosh_nonneg 1)) hpHalf hpTwo
  calc
    W.threeTapCanonicalM0 eps
      <= Real.cosh 1 *
        (16 * (18*Real.cosh 1) * ((1 + 2*|eps|) * 3)^2) := h
    _ = 2592 * (Real.cosh 1)^2 * (1 + 2*|eps|)^2 := by ring

end Synthesis
