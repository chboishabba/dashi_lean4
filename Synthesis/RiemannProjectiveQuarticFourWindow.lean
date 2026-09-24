import Synthesis.RiemannProjectiveQuarticFourWindowAtomic
import Synthesis.RiemannProjectiveQuarticThreeWindow

/-!
# Smooth signed four-window quartic family

Lift the atomic radii

  0, pi/3, pi/2, pi

to equal-radius symmetric C² bump windows.  With common mass m_R define

  G_{R,lambda,mu}
    = (B_0 - B_{pi/3} + lambda B_{pi/2} + mu B_pi) / m_R.

For every continuous weight w the pairing is exactly the corresponding signed
combination of normalized bump pairings.  This is the smooth carrier for the
one-parameter J2-null manifold.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

def quarticFourWindowRaw
    (R lam mu : ℝ) : ℝ -> ℝ :=
  fun u =>
    quantitativeSymBump 0 R u
      - quantitativeSymBump (Real.pi/3) R u
      + lam * quantitativeSymBump (Real.pi/2) R u
      + mu * quantitativeSymBump Real.pi R u

def quarticFourWindowProfile
    (R lam mu : ℝ) : ℝ -> ℝ :=
  fun u =>
    (quarticWindowMass R)⁻¹
      * quarticFourWindowRaw R lam mu u

theorem quarticFourWindowRaw_contDiff
    {R lam mu : ℝ} (hR : 0 < R) :
    ContDiff ℝ 2 (quarticFourWindowRaw R lam mu) := by
  unfold quarticFourWindowRaw
  exact
    (((quantitativeSymBump_contDiff
        (c:=0) (R:=R) hR.ne').sub
      (quantitativeSymBump_contDiff
        (c:=Real.pi/3) (R:=R) hR.ne')).add
      (contDiff_const.mul
        (quantitativeSymBump_contDiff
          (c:=Real.pi/2) (R:=R) hR.ne'))).add
      (contDiff_const.mul
        (quantitativeSymBump_contDiff
          (c:=Real.pi) (R:=R) hR.ne'))

theorem quarticFourWindowRaw_continuous
    {R lam mu : ℝ} (hR : 0 < R) :
    Continuous (quarticFourWindowRaw R lam mu) :=
  (quarticFourWindowRaw_contDiff
    (lam:=lam) (mu:=mu) hR).continuous

theorem quarticFourWindowRaw_compact
    {R lam mu : ℝ} (hR : 0 < R) :
    HasCompactSupport (quarticFourWindowRaw R lam mu) := by
  unfold quarticFourWindowRaw
  exact
    (((quantitativeSymBump_hasCompactSupport
        (c:=0) hR).sub
      (quantitativeSymBump_hasCompactSupport
        (c:=Real.pi/3) hR)).add
      (quantitativeSymBump_hasCompactSupport
        (c:=Real.pi/2) hR).mul_left).add
      (quantitativeSymBump_hasCompactSupport
        (c:=Real.pi) hR).mul_left

theorem quarticFourWindowProfile_contDiff
    {R lam mu : ℝ} (hR : 0 < R) :
    ContDiff ℝ 2 (quarticFourWindowProfile R lam mu) := by
  unfold quarticFourWindowProfile
  exact contDiff_const.mul
    (quarticFourWindowRaw_contDiff
      (lam:=lam) (mu:=mu) hR)

theorem quarticFourWindowProfile_continuous
    {R lam mu : ℝ} (hR : 0 < R) :
    Continuous (quarticFourWindowProfile R lam mu) :=
  (quarticFourWindowProfile_contDiff
    (lam:=lam) (mu:=mu) hR).continuous

theorem quarticFourWindowProfile_compact
    {R lam mu : ℝ} (hR : 0 < R) :
    HasCompactSupport (quarticFourWindowProfile R lam mu) := by
  unfold quarticFourWindowProfile
  exact (quarticFourWindowRaw_compact
    (lam:=lam) (mu:=mu) hR).mul_left

theorem quarticFourWindowProfile_even
    (R lam mu u : ℝ) :
    quarticFourWindowProfile R lam mu (-u)
      = quarticFourWindowProfile R lam mu u := by
  unfold quarticFourWindowProfile quarticFourWindowRaw
  simp only [quantitativeSymBump]
  unfold Zeta23Bridge.LiteralWeilOddChannelTaper.symmetrize
  ring

def quarticFourWindowPairing
    (R lam mu : ℝ) (w : ℝ -> ℝ) : ℝ :=
  normalizedSymBumpPairing 0 R w
    - normalizedSymBumpPairing (Real.pi/3) R w
    + lam * normalizedSymBumpPairing (Real.pi/2) R w
    + mu * normalizedSymBumpPairing Real.pi R w

theorem quarticFourWindowProfile_pairing_eq
    {R lam mu : ℝ} (hR : 0 < R)
    {w : ℝ -> ℝ}
    (hw : Continuous w) :
    (∫ u : ℝ, quarticFourWindowProfile R lam mu u * w u)
      =
    quarticFourWindowPairing R lam mu w := by
  have hm : quarticWindowMass R ≠ 0 :=
    ne_of_gt (quarticWindowMass_pos hR)
  let b0 : ℝ -> ℝ := quantitativeSymBump 0 R
  let b1 : ℝ -> ℝ := quantitativeSymBump (Real.pi/3) R
  let b2 : ℝ -> ℝ := quantitativeSymBump (Real.pi/2) R
  let b3 : ℝ -> ℝ := quantitativeSymBump Real.pi R
  have h0c : Continuous b0 :=
    (quantitativeSymBump_contDiff (c:=0) (R:=R) hR.ne').continuous
  have h1c : Continuous b1 :=
    (quantitativeSymBump_contDiff (c:=Real.pi/3) (R:=R) hR.ne').continuous
  have h2c : Continuous b2 :=
    (quantitativeSymBump_contDiff (c:=Real.pi/2) (R:=R) hR.ne').continuous
  have h3c : Continuous b3 :=
    (quantitativeSymBump_contDiff (c:=Real.pi) (R:=R) hR.ne').continuous
  have h0k : HasCompactSupport b0 :=
    quantitativeSymBump_hasCompactSupport (c:=0) hR
  have h1k : HasCompactSupport b1 :=
    quantitativeSymBump_hasCompactSupport (c:=Real.pi/3) hR
  have h2k : HasCompactSupport b2 :=
    quantitativeSymBump_hasCompactSupport (c:=Real.pi/2) hR
  have h3k : HasCompactSupport b3 :=
    quantitativeSymBump_hasCompactSupport (c:=Real.pi) hR
  have h0i : Integrable (fun u => b0 u*w u) :=
    (h0c.mul hw).integrable_of_hasCompactSupport h0k.mul_right
  have h1i : Integrable (fun u => b1 u*w u) :=
    (h1c.mul hw).integrable_of_hasCompactSupport h1k.mul_right
  have h2i : Integrable (fun u => b2 u*w u) :=
    (h2c.mul hw).integrable_of_hasCompactSupport h2k.mul_right
  have h3i : Integrable (fun u => b3 u*w u) :=
    (h3c.mul hw).integrable_of_hasCompactSupport h3k.mul_right

  unfold quarticFourWindowProfile quarticFourWindowRaw
    quarticFourWindowPairing normalizedSymBumpPairing
  rw [integral_const_mul]
  have hsplit :
      (∫ u : ℝ,
        (b0 u-b1 u+lam*b2 u+mu*b3 u)*w u)
        =
      (∫ u : ℝ,b0 u*w u)
        -(∫ u : ℝ,b1 u*w u)
        +lam*(∫ u : ℝ,b2 u*w u)
        +mu*(∫ u : ℝ,b3 u*w u) := by
    have hpoint :
        (fun u : ℝ =>
          (b0 u-b1 u+lam*b2 u+mu*b3 u)*w u)
          =
        fun u =>
          b0 u*w u-b1 u*w u
            +lam*(b2 u*w u)+mu*(b3 u*w u) := by
      funext u
      ring
    rw [hpoint,
      integral_add
        ((h0i.sub h1i).add (h2i.const_mul lam))
        (h3i.const_mul mu),
      integral_add (h0i.sub h1i) (h2i.const_mul lam),
      integral_sub h0i h1i,
      integral_const_mul,integral_const_mul]
  change
    (quarticWindowMass R)⁻¹ *
      (∫ u : ℝ,(b0 u-b1 u+lam*b2 u+mu*b3 u)*w u)
      = _
  rw [hsplit]
  unfold quarticWindowMass
  field_simp [hm]
  ring

def quarticFourWindowMomentResp
    (R lam mu : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  quarticFourWindowPairing R lam mu
    (fun u => u^k * Real.cos (s*u))

def quarticFourWindowJ
    (R lam mu : ℝ) (k : ℕ) : ℝ :=
  quarticFourWindowMomentResp R lam mu 0 1
      * quarticFourWindowMomentResp R lam mu k 2
    -
  quarticFourWindowMomentResp R lam mu 0 2
      * quarticFourWindowMomentResp R lam mu k 1

theorem evenResp_zero_fourWindow
    {R lam mu s : ℝ} (hR : 0 < R) :
    Zeta23Bridge.LiteralWeilParityBalance.evenResp
        (quarticFourWindowProfile R lam mu) 0 s
      =
    quarticFourWindowMomentResp R lam mu 0 s := by
  unfold Zeta23Bridge.LiteralWeilParityBalance.evenResp
    quarticFourWindowMomentResp
  simp only [zero_mul, Real.cosh_zero, one_mul, pow_zero]
  rw [quarticFourWindowProfile_pairing_eq hR (by fun_prop)]
  rfl

theorem projectiveBracketSecondMoment_fourWindow_one
    {R lam mu : ℝ} (hR : 0 < R) :
    projectiveBracketSecondMoment
        (quarticFourWindowProfile R lam mu) 1
      =
    quarticFourWindowJ R lam mu 2 := by
  rw [projectiveBracketSecondMoment_eq_response_det
      (quarticFourWindowProfile_continuous hR)
      (quarticFourWindowProfile_compact hR) 1,
    evenResp_zero_fourWindow hR,
    evenResp_zero_fourWindow hR]
  unfold projectiveSqEvenResp quarticFourWindowJ
    quarticFourWindowMomentResp
  rw [quarticFourWindowProfile_pairing_eq hR (by fun_prop),
      quarticFourWindowProfile_pairing_eq hR (by fun_prop)]
  norm_num

theorem projectiveBracketFourthMoment_fourWindow_one
    {R lam mu : ℝ} (hR : 0 < R) :
    projectiveBracketFourthMoment
        (quarticFourWindowProfile R lam mu) 1
      =
    quarticFourWindowJ R lam mu 4 := by
  rw [projectiveBracketFourthMoment_eq_response_det
      (quarticFourWindowProfile_continuous hR)
      (quarticFourWindowProfile_compact hR) 1,
    evenResp_zero_fourWindow hR,
    evenResp_zero_fourWindow hR]
  unfold projectiveFourthEvenResp quarticFourWindowJ
    quarticFourWindowMomentResp
  rw [quarticFourWindowProfile_pairing_eq hR (by fun_prop),
      quarticFourWindowProfile_pairing_eq hR (by fun_prop)]
  norm_num

end Synthesis
