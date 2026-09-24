import Synthesis.RiemannProjectiveQuarticMomentMixing

/-!
# Exact three-radius atomic certificate for quartic escape

Before lifting to smooth compact windows, isolate the finite-dimensional design.

At normalized sample radius r=1 take three even atomic radii

  x0 = 0,
  x1 = pi/3,
  x2 = pi/2

with signed weights

  w0 = 1,
  w1 = -1,
  w2 = 8/13.

For an atomic profile define

  A(s)  = sum_i w_i cos(s x_i),
  Mk(s) = sum_i w_i x_i^k cos(s x_i),

and the two-radius determinant

  Jk = A(1) Mk(2) - A(2) Mk(1).

The exact calculation gives

  J2 = 0,
  J4 = -175*pi^4/4212 < 0.

Thus the quartic-escape moment pattern is algebraically feasible.  The remaining
construction problem is to replace the atoms by narrow C^2 compact windows and
preserve J4<0 while correcting the small J2 perturbation back to zero.
-/

noncomputable section

open scoped Real

namespace Synthesis

def quarticAtomicX0 : ℝ := 0
def quarticAtomicX1 : ℝ := Real.pi / 3
def quarticAtomicX2 : ℝ := Real.pi / 2

def quarticAtomicW0 : ℝ := 1
def quarticAtomicW1 : ℝ := -1
def quarticAtomicW2 : ℝ := 8 / 13

def quarticAtomicResp (s : ℝ) : ℝ :=
  quarticAtomicW0 * Real.cos (s * quarticAtomicX0)
    + quarticAtomicW1 * Real.cos (s * quarticAtomicX1)
    + quarticAtomicW2 * Real.cos (s * quarticAtomicX2)

def quarticAtomicMomentResp (k : ℕ) (s : ℝ) : ℝ :=
  quarticAtomicW0 * quarticAtomicX0^k * Real.cos (s * quarticAtomicX0)
    + quarticAtomicW1 * quarticAtomicX1^k * Real.cos (s * quarticAtomicX1)
    + quarticAtomicW2 * quarticAtomicX2^k * Real.cos (s * quarticAtomicX2)

def quarticAtomicJ (k : ℕ) : ℝ :=
  quarticAtomicResp 1 * quarticAtomicMomentResp k 2
    - quarticAtomicResp 2 * quarticAtomicMomentResp k 1

private theorem cos_two_pi_div_three :
    Real.cos (2 * (Real.pi / 3)) = -(1/2 : ℝ) := by
  have harg : 2 * (Real.pi / 3) = Real.pi - Real.pi / 3 := by ring
  rw [harg, Real.cos_sub, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_three]
  norm_num

private theorem atomic_cos_values :
    Real.cos quarticAtomicX0 = 1
      ∧ Real.cos quarticAtomicX1 = 1/2
      ∧ Real.cos quarticAtomicX2 = 0
      ∧ Real.cos (2 * quarticAtomicX0) = 1
      ∧ Real.cos (2 * quarticAtomicX1) = -1/2
      ∧ Real.cos (2 * quarticAtomicX2) = -1 := by
  unfold quarticAtomicX0 quarticAtomicX1 quarticAtomicX2
  constructor
  · simp
  constructor
  · simpa using Real.cos_pi_div_three
  constructor
  · simpa using Real.cos_pi_div_two
  constructor
  · simp
  constructor
  · exact cos_two_pi_div_three
  · have h : 2 * (Real.pi / 2) = Real.pi := by ring
    rw [h, Real.cos_pi]

theorem quarticAtomicJ_two_zero :
    quarticAtomicJ 2 = 0 := by
  rcases atomic_cos_values with ⟨hc0,hc1,hc2,h2c0,h2c1,h2c2⟩
  unfold quarticAtomicJ quarticAtomicResp quarticAtomicMomentResp
    quarticAtomicW0 quarticAtomicW1 quarticAtomicW2
    quarticAtomicX0 quarticAtomicX1 quarticAtomicX2
  simp only [one_mul] at *
  rw [hc0, hc1, hc2, h2c0, h2c1, h2c2]
  ring

theorem quarticAtomicJ_four_exact :
    quarticAtomicJ 4 = -(175 * Real.pi^4 / 4212) := by
  rcases atomic_cos_values with ⟨hc0,hc1,hc2,h2c0,h2c1,h2c2⟩
  unfold quarticAtomicJ quarticAtomicResp quarticAtomicMomentResp
    quarticAtomicW0 quarticAtomicW1 quarticAtomicW2
    quarticAtomicX0 quarticAtomicX1 quarticAtomicX2
  simp only [one_mul] at *
  rw [hc0, hc1, hc2, h2c0, h2c1, h2c2]
  ring

theorem quarticAtomicJ_four_neg :
    quarticAtomicJ 4 < 0 := by
  rw [quarticAtomicJ_four_exact]
  have hp : 0 < Real.pi^4 := by positivity
  positivity

theorem quarticAtomic_escape_certificate :
    quarticAtomicJ 2 = 0 ∧ quarticAtomicJ 4 < 0 :=
  ⟨quarticAtomicJ_two_zero, quarticAtomicJ_four_neg⟩

end Synthesis
