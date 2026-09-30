import Mathlib

/-!
# Source-independent two-prime cosine phase obstruction

The signed three-tap experiment yields, after the *separate* detector
sample computation, a candidate two-prime oscillatory term

  a*cos(theta*log 2) + b*cos(theta*log 3).

This lemma shows that when 0 <= b < a its phase cannot be uniformly
nonnegative: it is positive at theta=0 and negative at theta=pi/log 2.
The relative phase at prime 3 requires no number theory, only cos<=1.

These theorems do not claim that source-native selected RH witnesses
satisfy 0<=b<a, that the completed explicit formula has this sign,
or that theta may be varied independently in the selected witness.
-/

namespace Integration.SignedTwoPrimePhaseObstruction

def phaseResponse (a b omega nu theta : ℝ) : ℝ :=
  a * Real.cos (theta * omega) + b * Real.cos (theta * nu)

theorem phaseResponse_at_zero (a b omega nu : ℝ) :
    phaseResponse a b omega nu 0 = a + b := by
  simp [phaseResponse]

theorem phaseResponse_antiphase_upper
    (a b omega nu : ℝ)
    (homega : omega ≠ 0) (hb : 0 ≤ b) :
    phaseResponse a b omega nu (Real.pi / omega) ≤ -a + b := by
  have hcos : Real.cos ((Real.pi / omega) * nu) ≤ 1 :=
    Real.cos_le_one _
  have hbound :
      b * Real.cos ((Real.pi / omega) * nu) ≤ b := by
    exact (mul_le_mul_of_nonneg_left hcos hb).trans_eq (mul_one b)
  have hphase : (Real.pi / omega) * omega = Real.pi := by
    field_simp [homega]
  simp only [phaseResponse, hphase, Real.cos_pi, mul_neg, mul_one]
  linarith

theorem phaseResponse_antiphase_negative
    (a b omega nu : ℝ)
    (homega : omega ≠ 0) (hb : 0 ≤ b) (hdom : b < a) :
    phaseResponse a b omega nu (Real.pi / omega) < 0 := by
  have h := phaseResponse_antiphase_upper a b omega nu homega hb
  linarith

theorem phaseResponse_sign_flip
    (a b omega nu : ℝ)
    (homega : omega ≠ 0) (hb : 0 ≤ b) (hdom : b < a) :
    0 < phaseResponse a b omega nu 0 ∧
    phaseResponse a b omega nu (Real.pi / omega) < 0 := by
  constructor
  · rw [phaseResponse_at_zero]
    linarith
  · exact phaseResponse_antiphase_negative a b omega nu homega hb hdom

end Integration.SignedTwoPrimePhaseObstruction
