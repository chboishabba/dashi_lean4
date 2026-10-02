import Mathlib.Tactic

/-!
# The R815 complete signed payment: viscous reserve and amplitude checks

These theorems are *necessary algebraic accounting* for candidate W2 estimates,
not the signed PDE estimate itself. The live identity supplies

  R = 2*(9*nested - q) + touched + 6*(2*nu - delta)*d.

The isolated viscosity coefficient is nonnegative only if delta <= 2*nu.
Increasing delta reduces this reserve for nonnegative integrated dissipation.

At arbitrary instantaneous data, the odd cubic+quintic part changes sign
under u -> -u while the quadratic viscous part does not. Positivity at both
signs therefore implies a concrete absolute signed-amplitude restriction;
no sign or witness for the actual live NS carrier is presumed.
-/

namespace NSBControl
namespace SignedOrbitReserveAudit

structure Slice where
  nested : ℝ
  q : ℝ
  touched : ℝ
  twoNu : ℝ
  margin : ℝ
  dissipation : ℝ

def nonlinear (s : Slice) : ℝ :=
  2 * (9 * s.nested - s.q) + s.touched

def reserve (s : Slice) : ℝ :=
  6 * (s.twoNu - s.margin) * s.dissipation

def signedPayment (s : Slice) : ℝ :=
  nonlinear s + reserve s

theorem reserve_nonneg (s : Slice)
    (hMargin : s.margin ≤ s.twoNu)
    (hDiss : 0 ≤ s.dissipation) :
    0 ≤ reserve s := by
  dsimp [reserve]
  nlinarith [mul_nonneg (sub_nonneg.mpr hMargin) hDiss]

/-- Exact, signed acceptance test, with no positive-part or individual
    norm bounds. This is the minimal nonlinear/viscous spending condition. -/
theorem signedPayment_nonneg_iff (s : Slice) :
    0 ≤ signedPayment s ↔ -nonlinear s ≤ reserve s := by
  simp only [signedPayment]
  constructor <;> intro h <;> linarith

/-- The viscosity budget is monotone in the *opposite* direction to
    retained margin when integrated dissipation is nonnegative. -/
theorem reserve_antitone (twoNu marginA marginB diss : ℝ)
    (hMargin : marginA ≤ marginB) (hDiss : 0 ≤ diss) :
    6 * (twoNu - marginB) * diss ≤
      6 * (twoNu - marginA) * diss := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hMargin) hDiss]

/-- One should not infer a nonnegative reserve from margin > 0 alone. -/
example : (0 : ℝ) < 3 ∧ (6 * (2 - 3) * 1 : ℝ) < 0 := by
  norm_num

def signedAtScale (quadratic cubic quintic a : ℝ) : ℝ :=
  a ^ 2 * quadratic + a ^ 3 * cubic + a ^ 5 * quintic

theorem signedAtScale_neg (quadratic cubic quintic a : ℝ) :
    signedAtScale quadratic cubic quintic (-a) =
      a ^ 2 * quadratic - a ^ 3 * cubic - a ^ 5 * quintic := by
  dsimp [signedAtScale]
  ring

/-- For an amplitude-closed initial-data family, a uniform pointwise W2
    claim must in particular pay both signs of every scale. The following
    condition is testable on a concrete initial datum without any
    normalization, upper bounds or smooth continuation hypotheses. -/
theorem bothSigns_require_oddPart_below_quadratic
    (quadratic cubic quintic a : ℝ)
    (hPlus : 0 ≤ signedAtScale quadratic cubic quintic a)
    (hMinus : 0 ≤ signedAtScale quadratic cubic quintic (-a)) :
    |a ^ 3 * cubic + a ^ 5 * quintic| ≤ a ^ 2 * quadratic := by
  have hneg := signedAtScale_neg quadratic cubic quintic a
  rw [hneg] at hMinus
  apply abs_le.mpr
  constructor <;> nlinarith [hPlus, hMinus]

theorem failure_of_bothSigns_at_scale
    (quadratic cubic quintic a : ℝ)
    (hAdverse :
      a ^ 2 * quadratic < |a ^ 3 * cubic + a ^ 5 * quintic|) :
    ¬ (0 ≤ signedAtScale quadratic cubic quintic a ∧
       0 ≤ signedAtScale quadratic cubic quintic (-a)) := by
  rintro ⟨hp, hm⟩
  have h := bothSigns_require_oddPart_below_quadratic
    quadratic cubic quintic a hp hm
  linarith

/-- This does not assert such a witness for the physical R815 scalar:
    it supplies a fail-closed diagnostic criterion for any candidate
    *universal pointwise* estimate. The integrated W2 target may use
    nonlinear time evolution and is not refuted by the criterion alone. -/
theorem unitScale_falsification_certificate
    (quadratic cubic quintic : ℝ)
    (h : quadratic < |cubic + quintic|) :
    ¬ (0 ≤ signedAtScale quadratic cubic quintic 1 ∧
       0 ≤ signedAtScale quadratic cubic quintic (-1)) := by
  apply failure_of_bothSigns_at_scale quadratic cubic quintic 1
  simpa only [one_pow, one_mul] using h

end SignedOrbitReserveAudit
end NSBControl
