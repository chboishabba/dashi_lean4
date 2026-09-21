import Synthesis.RiemannProjectiveQuarticAtomicFamily
import Synthesis.RiemannQuantitativeSymBumpLocalization
import Synthesis.RiemannProjectiveQuarticTargetLocalSign

/-!
# Smooth three-window quartic-escape family

Lift the atomic radii 0, pi/3, pi/2 to the repository's actual symmetric C^2
bump windows.  All three windows use the same radius R and exact mass

  m_R = 2 R M0.

The mass-normalized signed profile is

  G_{R,lambda}
    = (B_{0,R} - B_{pi/3,R} + lambda B_{pi/2,R}) / m_R.

For every even weight w its pairing is therefore exactly the same signed
combination of the three normalized window pairings.  This is the same-object
bridge from the atomic certificate to an admissible smooth compact test.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

def quarticWindowMass (R : ℝ) : ℝ :=
  2 * R * unitBumpMass0

def quarticThreeWindowRaw
    (R lam : ℝ) : ℝ → ℝ :=
  fun u =>
    quantitativeSymBump 0 R u
      - quantitativeSymBump (Real.pi/3) R u
      + lam * quantitativeSymBump (Real.pi/2) R u

def quarticThreeWindowProfile
    (R lam : ℝ) : ℝ → ℝ :=
  fun u => (quarticWindowMass R)⁻¹ * quarticThreeWindowRaw R lam u

theorem quarticWindowMass_pos
    {R : ℝ} (hR : 0 < R) :
    0 < quarticWindowMass R := by
  unfold quarticWindowMass
  have hM := unitBumpMass0_pos
  positivity

theorem quarticThreeWindowRaw_continuous
    {R lam : ℝ} (hR : 0 < R) :
    Continuous (quarticThreeWindowRaw R lam) := by
  unfold quarticThreeWindowRaw
  have h0 := (quantitativeSymBump_contDiff
    (c := 0) (R := R) hR.ne').continuous
  have h1 := (quantitativeSymBump_contDiff
    (c := Real.pi/3) (R := R) hR.ne').continuous
  have h2 := (quantitativeSymBump_contDiff
    (c := Real.pi/2) (R := R) hR.ne').continuous
  fun_prop

theorem quarticThreeWindowRaw_contDiff
    {R lam : ℝ} (hR : 0 < R) :
    ContDiff ℝ 2 (quarticThreeWindowRaw R lam) := by
  unfold quarticThreeWindowRaw
  exact
    ((quantitativeSymBump_contDiff
      (c := 0) (R := R) hR.ne').sub
      (quantitativeSymBump_contDiff
        (c := Real.pi/3) (R := R) hR.ne')).add
      (contDiff_const.mul
        (quantitativeSymBump_contDiff
          (c := Real.pi/2) (R := R) hR.ne'))

theorem quarticThreeWindowRaw_compact
    {R lam : ℝ} (hR : 0 < R) :
    HasCompactSupport (quarticThreeWindowRaw R lam) := by
  unfold quarticThreeWindowRaw
  exact
    ((quantitativeSymBump_hasCompactSupport
      (c := 0) hR).sub
      (quantitativeSymBump_hasCompactSupport
        (c := Real.pi/3) hR)).add
      (quantitativeSymBump_hasCompactSupport
        (c := Real.pi/2) hR).mul_left

theorem quarticThreeWindowProfile_continuous
    {R lam : ℝ} (hR : 0 < R) :
    Continuous (quarticThreeWindowProfile R lam) := by
  unfold quarticThreeWindowProfile
  exact continuous_const.mul (quarticThreeWindowRaw_continuous hR)

theorem quarticThreeWindowProfile_contDiff
    {R lam : ℝ} (hR : 0 < R) :
    ContDiff ℝ 2 (quarticThreeWindowProfile R lam) := by
  unfold quarticThreeWindowProfile
  exact contDiff_const.mul (quarticThreeWindowRaw_contDiff hR)

theorem quarticThreeWindowProfile_compact
    {R lam : ℝ} (hR : 0 < R) :
    HasCompactSupport (quarticThreeWindowProfile R lam) := by
  unfold quarticThreeWindowProfile
  exact (quarticThreeWindowRaw_compact hR).mul_left

theorem quarticThreeWindowProfile_even
    (R lam u : ℝ) :
    quarticThreeWindowProfile R lam (-u)
      = quarticThreeWindowProfile R lam u := by
  unfold quarticThreeWindowProfile quarticThreeWindowRaw
  simp only [quantitativeSymBump]
  unfold Zeta23Bridge.LiteralWeilOddChannelTaper.symmetrize
  ring

def quarticThreeWindowPairing
    (R lam : ℝ) (w : ℝ → ℝ) : ℝ :=
  normalizedSymBumpPairing 0 R w
    - normalizedSymBumpPairing (Real.pi/3) R w
    + lam * normalizedSymBumpPairing (Real.pi/2) R w

theorem quarticThreeWindowProfile_pairing_eq
    {R lam : ℝ} (hR : 0 < R)
    {w : ℝ → ℝ}
    (hw : Continuous w) :
    (∫ u : ℝ, quarticThreeWindowProfile R lam u * w u)
      = quarticThreeWindowPairing R lam w := by
  have hm : quarticWindowMass R ≠ 0 :=
    ne_of_gt (quarticWindowMass_pos hR)
  let b0 : ℝ → ℝ := quantitativeSymBump 0 R
  let b1 : ℝ → ℝ := quantitativeSymBump (Real.pi/3) R
  let b2 : ℝ → ℝ := quantitativeSymBump (Real.pi/2) R
  have h0c : Continuous b0 :=
    (quantitativeSymBump_contDiff (c := 0) (R := R) hR.ne').continuous
  have h1c : Continuous b1 :=
    (quantitativeSymBump_contDiff (c := Real.pi/3) (R := R) hR.ne').continuous
  have h2c : Continuous b2 :=
    (quantitativeSymBump_contDiff (c := Real.pi/2) (R := R) hR.ne').continuous
  have h0k : HasCompactSupport b0 :=
    quantitativeSymBump_hasCompactSupport (c := 0) hR
  have h1k : HasCompactSupport b1 :=
    quantitativeSymBump_hasCompactSupport (c := Real.pi/3) hR
  have h2k : HasCompactSupport b2 :=
    quantitativeSymBump_hasCompactSupport (c := Real.pi/2) hR
  have h0i : Integrable (fun u => b0 u * w u) :=
    (h0c.mul hw).integrable_of_hasCompactSupport h0k.mul_right
  have h1i : Integrable (fun u => b1 u * w u) :=
    (h1c.mul hw).integrable_of_hasCompactSupport h1k.mul_right
  have h2i : Integrable (fun u => b2 u * w u) :=
    (h2c.mul hw).integrable_of_hasCompactSupport h2k.mul_right
  unfold quarticThreeWindowProfile quarticThreeWindowRaw
    quarticThreeWindowPairing normalizedSymBumpPairing
  rw [integral_const_mul]
  have hsplit :
      (∫ u : ℝ,
        (b0 u - b1 u + lam*b2 u) * w u)
        =
      (∫ u : ℝ, b0 u*w u)
        - (∫ u : ℝ, b1 u*w u)
        + lam*(∫ u : ℝ, b2 u*w u) := by
    have hpoint :
        (fun u : ℝ => (b0 u - b1 u + lam*b2 u)*w u)
          =
        (fun u : ℝ => b0 u*w u - b1 u*w u + lam*(b2 u*w u)) := by
      funext u
      ring
    rw [hpoint, integral_add (h0i.sub h1i) (h2i.const_mul lam),
      integral_sub h0i h1i, integral_const_mul]
  change
    (quarticWindowMass R)⁻¹ *
      (∫ u : ℝ, (b0 u - b1 u + lam*b2 u)*w u)
      = _
  rw [hsplit]
  unfold quarticWindowMass
  field_simp [hm]
  ring

def quarticThreeWindowMomentResp
    (R lam : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  quarticThreeWindowPairing R lam
    (fun u => u^k * Real.cos (s*u))

def quarticThreeWindowJ
    (R lam : ℝ) (k : ℕ) : ℝ :=
  quarticThreeWindowMomentResp R lam 0 1
      * quarticThreeWindowMomentResp R lam k 2
    - quarticThreeWindowMomentResp R lam 0 2
      * quarticThreeWindowMomentResp R lam k 1

theorem projectiveSqEvenResp_threeWindow
    {R lam s : ℝ} (hR : 0 < R) :
    projectiveSqEvenResp (quarticThreeWindowProfile R lam) s
      = quarticThreeWindowMomentResp R lam 2 s := by
  unfold projectiveSqEvenResp quarticThreeWindowMomentResp
  rw [quarticThreeWindowProfile_pairing_eq hR (by fun_prop)]
  rfl

theorem projectiveFourthEvenResp_threeWindow
    {R lam s : ℝ} (hR : 0 < R) :
    projectiveFourthEvenResp (quarticThreeWindowProfile R lam) s
      = quarticThreeWindowMomentResp R lam 4 s := by
  unfold projectiveFourthEvenResp quarticThreeWindowMomentResp
  rw [quarticThreeWindowProfile_pairing_eq hR (by fun_prop)]
  rfl

end Synthesis
