import Synthesis.RiemannProjectiveQuarticFourWindowHighWitness
import Synthesis.RiemannProjectiveQuarticFourWindowAtomicPoleSign
import Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition

/-!
# Same-object four-window pole determinant

For the physical four-window detector

  g_t(u) = G((t/16)u),

the change of variables v=(t/16)u turns the two pole responses into normalized
four-window pairings against

  w_c(v) = cosh(8v/t) cos(16v) cos(cv),   c=1,2.

The on-line responses are the same pairings against cos(v) and cos(2v).
Therefore the literal projective pole defect is exactly a positive scale factor
times one normalized determinant.

This is the bridge required to transport the atomic pole sign through the
existing four-window bump localization machinery.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition

def quarticFourNormalizedPoleWeight
    (t c v : ℝ) : ℝ :=
  Real.cosh (8*v/t) * Real.cos (16*v) * Real.cos (c*v)

def quarticFourNormalizedOnLineWeight
    (c v : ℝ) : ℝ :=
  Real.cos (c*v)

theorem quarticFourNormalizedPoleWeight_continuous
    (t c : ℝ) :
    Continuous (quarticFourNormalizedPoleWeight t c) := by
  unfold quarticFourNormalizedPoleWeight
  fun_prop

theorem quarticFourNormalizedPoleWeight_even
    (t c v : ℝ) :
    quarticFourNormalizedPoleWeight t c (-v)
      = quarticFourNormalizedPoleWeight t c v := by
  unfold quarticFourNormalizedPoleWeight
  rw [show 8*(-v)/t = -(8*v/t) by ring,
      show 16*(-v)=-(16*v) by ring,
      show c*(-v)=-(c*v) by ring,
      Real.cosh_neg, Real.cos_neg, Real.cos_neg]

theorem quarticFourNormalizedOnLineWeight_continuous
    (c : ℝ) :
    Continuous (quarticFourNormalizedOnLineWeight c) := by
  unfold quarticFourNormalizedOnLineWeight
  fun_prop

theorem quarticFourNormalizedOnLineWeight_even
    (c v : ℝ) :
    quarticFourNormalizedOnLineWeight c (-v)
      = quarticFourNormalizedOnLineWeight c v := by
  unfold quarticFourNormalizedOnLineWeight
  rw [show c*(-v)=-(c*v) by ring, Real.cos_neg]

/-- Physical pole response after the exact v=(t/16)u normalization. -/
theorem poleEvenResp_quarticFourPhysicalDetector_eq_pairing
    {R lam mu t : ℝ}
    (hR : 0 < R) (ht : 0 < t)
    (c : ℝ) :
    poleEvenResp
        (quarticFourPhysicalDetector R lam mu t)
        t (c*(t/16))
      =
    (16/t) *
      quarticFourWindowPairing R lam mu
        (quarticFourNormalizedPoleWeight t c) := by
  let r : ℝ := t/16
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hr0 : r ≠ 0 := ne_of_gt hr
  let G : ℝ -> ℝ := quarticFourWindowProfile R lam mu
  let F : ℝ -> ℝ := fun v =>
    G v * quarticFourNormalizedPoleWeight t c v
  have hpoint :
      (fun u : ℝ =>
        quarticFourPhysicalDetector R lam mu t u *
          (Real.cosh (u/2) * Real.cos (t*u) * Real.cos ((c*(t/16))*u)))
        =
      fun u => F (r*u) := by
    funext u
    dsimp [F,G,r]
    unfold quarticFourPhysicalDetector projectiveRescaleProfile
      quarticFourNormalizedPoleWeight
    have ht0 : t ≠ 0 := ne_of_gt ht
    have h1 : 8*((t/16)*u)/t = u/2 := by
      field_simp [ht0]
      ring
    have h2 : 16*((t/16)*u) = t*u := by ring
    have h3 : c*((t/16)*u) = (c*(t/16))*u := by ring
    rw [h1,h2,h3]
  unfold poleEvenResp
  rw [hpoint]
  have hscale := Measure.integral_comp_mul_left F r
  have habs : |r⁻¹| = 1/r := by
    rw [abs_of_pos (inv_pos.mpr hr)]
    rfl
  have hscale' :
      (∫ u : ℝ, F (r*u))
        = (1/r) * ∫ v : ℝ, F v := by
    simpa [habs, smul_eq_mul] using hscale
  rw [hscale']
  have hpair :
      (∫ v : ℝ, F v)
        =
      quarticFourWindowPairing R lam mu
        (quarticFourNormalizedPoleWeight t c) := by
    dsimp [F,G]
    exact quarticFourWindowProfile_pairing_eq
      hR (quarticFourNormalizedPoleWeight_continuous t c)
  rw [hpair]
  dsimp [r]
  field_simp [ne_of_gt ht]
  ring

/-- Physical on-line response on the same normalized pairing carrier. -/
theorem evenResp_quarticFourPhysicalDetector_eq_pairing
    {R lam mu t : ℝ}
    (hR : 0 < R) (ht : 0 < t)
    (c : ℝ) :
    evenResp
        (quarticFourPhysicalDetector R lam mu t)
        0 (c*(t/16))
      =
    (16/t) *
      quarticFourWindowPairing R lam mu
        (quarticFourNormalizedOnLineWeight c) := by
  have hr : 0 < t/16 := by positivity
  unfold quarticFourPhysicalDetector
  rw [evenResp_projectiveRescale hr c]
  unfold evenResp
  simp only [zero_mul, Real.cosh_zero, one_mul]
  have hpair :=
    quarticFourWindowProfile_pairing_eq
      (lam:=lam) (mu:=mu) hR
      (quarticFourNormalizedOnLineWeight_continuous c)
  unfold quarticFourNormalizedOnLineWeight at hpair
  rw [hpair]
  field_simp [ne_of_gt ht]
  ring

def quarticFourSmoothFinitePoleResidual
    (R lam mu t : ℝ) : ℝ :=
  quarticFourWindowPairing R lam mu
      (quarticFourNormalizedPoleWeight t 1)
    * quarticFourWindowPairing R lam mu
      (quarticFourNormalizedOnLineWeight 2)
  -
  quarticFourWindowPairing R lam mu
      (quarticFourNormalizedPoleWeight t 2)
    * quarticFourWindowPairing R lam mu
      (quarticFourNormalizedOnLineWeight 1)

/--
The literal projective pole defect is a positive scale multiple of the normalized
four-window pole determinant.
-/
theorem poleProjectiveDefect_quarticFourPhysicalDetector_eq
    {R lam mu t : ℝ}
    (hR : 0 < R) (ht : 0 < t) :
    poleProjectiveDefect
        (quarticFourPhysicalDetector R lam mu t)
        t (t/16)
      =
    4 * (16/t)^2 *
      quarticFourSmoothFinitePoleResidual R lam mu t := by
  have hc :=
    quarticFourPhysicalDetector_contDiff
      (t:=t) (lam:=lam) (mu:=mu) hR
  have hk :=
    quarticFourPhysicalDetector_compact
      (t:=t) (lam:=lam) (mu:=mu) hR ht
  have he :=
    quarticFourPhysicalDetector_even R lam mu t
  rw [poleProjectiveDefect_eq hc.continuous hk he t (t/16)]
  rw [show 2*(t/16) = (2:ℝ)*(t/16) by ring,
      show t/16 = (1:ℝ)*(t/16) by ring,
      poleEvenResp_quarticFourPhysicalDetector_eq_pairing hR ht 2,
      poleEvenResp_quarticFourPhysicalDetector_eq_pairing hR ht 1,
      evenResp_quarticFourPhysicalDetector_eq_pairing hR ht 1,
      evenResp_quarticFourPhysicalDetector_eq_pairing hR ht 2]
  unfold quarticFourSmoothFinitePoleResidual
  ring


def quarticFourAtomicFinitePoleDeterminant
    (t lam mu : ℝ) : ℝ :=
  quarticFourAtomicPairingAt lam mu
      (quarticFourNormalizedPoleWeight t 1)
    * quarticFourAtomicPairingAt lam mu
      (quarticFourNormalizedOnLineWeight 2)
  -
  quarticFourAtomicPairingAt lam mu
      (quarticFourNormalizedPoleWeight t 2)
    * quarticFourAtomicPairingAt lam mu
      (quarticFourNormalizedOnLineWeight 1)

private theorem cos_two_pi_div_three :
    Real.cos (2*Real.pi/3) = -1/2 := by
  have harg : 2*Real.pi/3 = Real.pi - Real.pi/3 := by ring
  rw [harg, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

private theorem cos_sixteen_pi_div_three :
    Real.cos (16*(Real.pi/3)) = -1/2 := by
  have harg :
      16*(Real.pi/3)
        = (-2*Real.pi/3) + (3:ℕ) * (2*Real.pi) := by ring
  rw [harg, Real.cos_add_nat_mul_two_pi, Real.cos_neg]
  exact cos_two_pi_div_three

private theorem cos_eight_pi :
    Real.cos (16*(Real.pi/2)) = 1 := by
  have harg :
      16*(Real.pi/2) = (4:ℕ) * (2*Real.pi) := by ring
  rw [harg, Real.cos_nat_mul_two_pi]

private theorem cos_sixteen_pi :
    Real.cos (16*Real.pi) = 1 := by
  have harg :
      16*Real.pi = (8:ℕ) * (2*Real.pi) := by ring
  rw [harg, Real.cos_nat_mul_two_pi]

theorem quarticFourAtomicOnLinePairing_one
    (lam mu : ℝ) :
    quarticFourAtomicPairingAt lam mu
      (quarticFourNormalizedOnLineWeight 1)
      = 1/2-mu := by
  unfold quarticFourAtomicPairingAt
    quarticFourNormalizedOnLineWeight
  simp only [one_mul, Real.cos_zero,
    Real.cos_pi_div_three, Real.cos_pi_div_two, Real.cos_pi]
  ring

theorem quarticFourAtomicOnLinePairing_two
    (lam mu : ℝ) :
    quarticFourAtomicPairingAt lam mu
      (quarticFourNormalizedOnLineWeight 2)
      = 3/2-lam+mu := by
  unfold quarticFourAtomicPairingAt
    quarticFourNormalizedOnLineWeight
  simp only [mul_zero, Real.cos_zero]
  rw [show 2*(Real.pi/3)=2*Real.pi/3 by ring,
      cos_two_pi_div_three,
      show 2*(Real.pi/2)=Real.pi by ring,
      Real.cos_pi,
      Real.cos_two_pi]
  ring

theorem quarticFourAtomicPolePairing_one
    {t lam mu : ℝ} (ht : t ≠ 0) :
    quarticFourAtomicPairingAt lam mu
      (quarticFourNormalizedPoleWeight t 1)
      =
    1 + Real.cosh (8*Real.pi/(3*t))/4
      - mu*Real.cosh (8*Real.pi/t) := by
  unfold quarticFourAtomicPairingAt
    quarticFourNormalizedPoleWeight
  simp only [mul_zero, zero_div, Real.cosh_zero, Real.cos_zero,
    one_mul, Real.cos_pi_div_three, Real.cos_pi_div_two, Real.cos_pi]
  rw [show 8*(Real.pi/3)/t = 8*Real.pi/(3*t) by field_simp [ht]; ring,
      cos_sixteen_pi_div_three,
      cos_eight_pi,
      show 8*Real.pi/t = 8*Real.pi/t by rfl,
      cos_sixteen_pi]
  ring

theorem quarticFourAtomicPolePairing_two
    {t lam mu : ℝ} (ht : t ≠ 0) :
    quarticFourAtomicPairingAt lam mu
      (quarticFourNormalizedPoleWeight t 2)
      =
    1 - Real.cosh (8*Real.pi/(3*t))/4
      - lam*Real.cosh (4*Real.pi/t)
      + mu*Real.cosh (8*Real.pi/t) := by
  unfold quarticFourAtomicPairingAt
    quarticFourNormalizedPoleWeight
  simp only [mul_zero, zero_div, Real.cosh_zero, Real.cos_zero, one_mul]
  rw [show 8*(Real.pi/3)/t = 8*Real.pi/(3*t) by field_simp [ht]; ring,
      cos_sixteen_pi_div_three,
      show 2*(Real.pi/3)=2*Real.pi/3 by ring,
      cos_two_pi_div_three,
      show 8*(Real.pi/2)/t = 4*Real.pi/t by field_simp [ht]; ring,
      cos_eight_pi,
      show 2*(Real.pi/2)=Real.pi by ring,
      Real.cos_pi,
      cos_sixteen_pi,
      Real.cos_two_pi]
  ring

theorem quarticFourAtomicFinitePoleDeterminant_eq_residual
    {t lam mu : ℝ} (ht : t ≠ 0) :
    quarticFourAtomicFinitePoleDeterminant t lam mu
      = quarticFourAtomicFinitePoleResidual t lam mu := by
  unfold quarticFourAtomicFinitePoleDeterminant
  rw [quarticFourAtomicPolePairing_one ht,
      quarticFourAtomicPolePairing_two ht,
      quarticFourAtomicOnLinePairing_one,
      quarticFourAtomicOnLinePairing_two]
  unfold quarticFourAtomicFinitePoleResidual
  ring

end Synthesis
