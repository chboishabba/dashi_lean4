import Synthesis.RiemannSelectedPrimeSensitiveThreeTapJ2Normalized
import Synthesis.RiemannProjectiveQuarticFourWindowAtomic

/-!
# Atomic donor for the transformed J2 phase coefficients

The smooth selected four-window witnesses are robust lifts of the four atomic
sites 0, pi/3, pi/2, pi.  This module computes the response data entering the
normalized three-tap J2 phase normal form exactly on that atomic donor.

No transfer from the atomic model to the smooth witness is asserted here.
That requires a quantitative robustness theorem for these new sine-first
coordinates.
-/

noncomputable section
namespace Synthesis

open scoped Real

def quarticFourAtomicSinFirstRespAt
    (lam mu s : ℝ) : ℝ :=
  1 * 0 * Real.sin (s*0)
    - (Real.pi/3) * Real.sin (s*(Real.pi/3))
    + lam * (Real.pi/2) * Real.sin (s*(Real.pi/2))
    + mu * Real.pi * Real.sin (s*Real.pi)

theorem quarticFourAtomicRespAt_one
    (lam mu : ℝ) :
    quarticFourAtomicRespAt lam mu 1 = 1/2 - mu := by
  unfold quarticFourAtomicRespAt
  simp only [one_mul, mul_zero, Real.cos_zero]
  rw [Real.cos_pi_div_three, Real.cos_pi_div_two, Real.cos_pi]
  ring

theorem quarticFourAtomicRespAt_two
    (lam mu : ℝ) :
    quarticFourAtomicRespAt lam mu 2 = 3/2 - lam + mu := by
  unfold quarticFourAtomicRespAt
  simp only [mul_zero, Real.cos_zero]
  have h1 : 2 * (Real.pi/3) = Real.pi - Real.pi/3 := by ring
  have h2 : 2 * (Real.pi/2) = Real.pi := by ring
  have hp : 2 * Real.pi = Real.pi + Real.pi := by ring
  rw [h1, Real.cos_sub, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_three,
      h2, Real.cos_pi,
      hp, Real.cos_add, Real.cos_pi, Real.sin_pi]
  ring

theorem quarticFourAtomicSinFirstRespAt_one
    (lam mu : ℝ) :
    quarticFourAtomicSinFirstRespAt lam mu 1
      =
    -(Real.pi/3) * (Real.sqrt 3/2)
      + lam * (Real.pi/2) := by
  unfold quarticFourAtomicSinFirstRespAt
  simp only [one_mul, mul_zero, zero_mul, Real.sin_zero]
  rw [Real.sin_pi_div_three, Real.sin_pi_div_two, Real.sin_pi]
  ring

theorem quarticFourAtomicSinFirstRespAt_two
    (lam mu : ℝ) :
    quarticFourAtomicSinFirstRespAt lam mu 2
      =
    -(Real.pi/3) * (Real.sqrt 3/2) := by
  unfold quarticFourAtomicSinFirstRespAt
  simp only [mul_zero, Real.sin_zero]
  have h1 : 2 * (Real.pi/3) = Real.pi - Real.pi/3 := by ring
  have h2 : 2 * (Real.pi/2) = Real.pi := by ring
  have hp : 2 * Real.pi = Real.pi + Real.pi := by ring
  rw [h1, Real.sin_sub, Real.sin_pi, Real.cos_pi,
      Real.sin_pi_div_three,
      h2, Real.sin_pi,
      hp, Real.sin_add, Real.sin_pi, Real.cos_pi]
  ring

def quarticFourAtomicThreeTapJ2LinearPhase
    (lam mu B : ℝ) : ℝ :=
  let A1 := quarticFourAtomicRespAt lam mu 1
  let A2 := quarticFourAtomicRespAt lam mu 2
  let U1 := quarticFourAtomicSinFirstRespAt lam mu 1
  let U2 := quarticFourAtomicSinFirstRespAt lam mu 2
  2 * B^2 * A1 * A2 * (Real.cos (2*B) - Real.cos B)
    +
  4 * B *
    (A2 * Real.sin B * U1
      - A1 * Real.sin (2*B) * U2)

def quarticFourAtomicThreeTapJ2QuadraticPhase
    (lam mu B : ℝ) : ℝ :=
  let A1 := quarticFourAtomicRespAt lam mu 1
  let A2 := quarticFourAtomicRespAt lam mu 2
  let U1 := quarticFourAtomicSinFirstRespAt lam mu 1
  let U2 := quarticFourAtomicSinFirstRespAt lam mu 2
  8 * B *
    (Real.cos (2*B) * A2 * Real.sin B * U1
      - Real.cos B * A1 * Real.sin (2*B) * U2)

theorem quarticFourAtomicThreeTapJ2LinearPhase_formula
    (lam mu B : ℝ) :
    quarticFourAtomicThreeTapJ2LinearPhase lam mu B
      =
    2 * B^2 * (1/2-mu) * (3/2-lam+mu)
      * (Real.cos (2*B)-Real.cos B)
    +
    4 * B *
      (
        (3/2-lam+mu) * Real.sin B
          * (-(Real.pi/3)*(Real.sqrt 3/2)+lam*(Real.pi/2))
        -
        (1/2-mu) * Real.sin (2*B)
          * (-(Real.pi/3)*(Real.sqrt 3/2))
      ) := by
  unfold quarticFourAtomicThreeTapJ2LinearPhase
  rw [quarticFourAtomicRespAt_one,
      quarticFourAtomicRespAt_two,
      quarticFourAtomicSinFirstRespAt_one,
      quarticFourAtomicSinFirstRespAt_two]

theorem quarticFourAtomicThreeTapJ2QuadraticPhase_formula
    (lam mu B : ℝ) :
    quarticFourAtomicThreeTapJ2QuadraticPhase lam mu B
      =
    8 * B *
      (
        Real.cos (2*B) * (3/2-lam+mu) * Real.sin B
          * (-(Real.pi/3)*(Real.sqrt 3/2)+lam*(Real.pi/2))
        -
        Real.cos B * (1/2-mu) * Real.sin (2*B)
          * (-(Real.pi/3)*(Real.sqrt 3/2))
      ) := by
  unfold quarticFourAtomicThreeTapJ2QuadraticPhase
  rw [quarticFourAtomicRespAt_one,
      quarticFourAtomicRespAt_two,
      quarticFourAtomicSinFirstRespAt_one,
      quarticFourAtomicSinFirstRespAt_two]

theorem quarticFourAtomicMu_half :
    quarticFourAtomicMu (1/2) = -(1/78 : ℝ) := by
  unfold quarticFourAtomicMu
  norm_num

theorem quarticFourAtomicMu_twoThirds :
    quarticFourAtomicMu (2/3) = (1/162 : ℝ) := by
  unfold quarticFourAtomicMu
  norm_num

theorem quarticFourAtomic_half_response_one :
    quarticFourAtomicRespAt
      (1/2) (quarticFourAtomicMu (1/2)) 1 = 20/39 := by
  rw [quarticFourAtomicRespAt_one, quarticFourAtomicMu_half]
  norm_num

theorem quarticFourAtomic_half_response_two :
    quarticFourAtomicRespAt
      (1/2) (quarticFourAtomicMu (1/2)) 2 = 77/78 := by
  rw [quarticFourAtomicRespAt_two, quarticFourAtomicMu_half]
  norm_num

theorem quarticFourAtomic_twoThirds_response_one :
    quarticFourAtomicRespAt
      (2/3) (quarticFourAtomicMu (2/3)) 1 = 40/81 := by
  rw [quarticFourAtomicRespAt_one, quarticFourAtomicMu_twoThirds]
  norm_num

theorem quarticFourAtomic_twoThirds_response_two :
    quarticFourAtomicRespAt
      (2/3) (quarticFourAtomicMu (2/3)) 2 = 68/81 := by
  rw [quarticFourAtomicRespAt_two, quarticFourAtomicMu_twoThirds]
  norm_num

theorem quarticFourAtomic_half_sinFirst_one :
    quarticFourAtomicSinFirstRespAt
      (1/2) (quarticFourAtomicMu (1/2)) 1
      =
    Real.pi * (1/4 - Real.sqrt 3/6) := by
  rw [quarticFourAtomicSinFirstRespAt_one]
  ring

theorem quarticFourAtomic_twoThirds_sinFirst_one :
    quarticFourAtomicSinFirstRespAt
      (2/3) (quarticFourAtomicMu (2/3)) 1
      =
    Real.pi * (1/3 - Real.sqrt 3/6) := by
  rw [quarticFourAtomicSinFirstRespAt_one]
  ring

theorem quarticFourAtomic_sinFirst_two
    (lam : ℝ) :
    quarticFourAtomicSinFirstRespAt
      lam (quarticFourAtomicMu lam) 2
      =
    -(Real.pi * Real.sqrt 3 / 6) := by
  rw [quarticFourAtomicSinFirstRespAt_two]
  ring

/-- Atomic endpoint-half phase formula on the exact J2-null donor. -/
theorem quarticFourAtomic_half_threeTapLinear_formula
    (B : ℝ) :
    quarticFourAtomicThreeTapJ2LinearPhase
      (1/2) (quarticFourAtomicMu (1/2)) B
      =
    2 * B^2 * (20/39 : ℝ) * (77/78)
      * (Real.cos (2*B)-Real.cos B)
    +
    4 * B *
      (
        (77/78 : ℝ) * Real.sin B
          * (Real.pi * (1/4-Real.sqrt 3/6))
        -
        (20/39 : ℝ) * Real.sin (2*B)
          * (-(Real.pi*Real.sqrt 3/6))
      ) := by
  unfold quarticFourAtomicThreeTapJ2LinearPhase
  rw [quarticFourAtomic_half_response_one,
      quarticFourAtomic_half_response_two,
      quarticFourAtomic_half_sinFirst_one,
      quarticFourAtomic_sinFirst_two]

/-- Atomic endpoint-two-thirds phase formula on the exact J2-null donor. -/
theorem quarticFourAtomic_twoThirds_threeTapLinear_formula
    (B : ℝ) :
    quarticFourAtomicThreeTapJ2LinearPhase
      (2/3) (quarticFourAtomicMu (2/3)) B
      =
    2 * B^2 * (40/81 : ℝ) * (68/81)
      * (Real.cos (2*B)-Real.cos B)
    +
    4 * B *
      (
        (68/81 : ℝ) * Real.sin B
          * (Real.pi * (1/3-Real.sqrt 3/6))
        -
        (40/81 : ℝ) * Real.sin (2*B)
          * (-(Real.pi*Real.sqrt 3/6))
      ) := by
  unfold quarticFourAtomicThreeTapJ2LinearPhase
  rw [quarticFourAtomic_twoThirds_response_one,
      quarticFourAtomic_twoThirds_response_two,
      quarticFourAtomic_twoThirds_sinFirst_one,
      quarticFourAtomic_sinFirst_two]

theorem quarticFourAtomic_half_threeTapQuadratic_formula
    (B : ℝ) :
    quarticFourAtomicThreeTapJ2QuadraticPhase
      (1/2) (quarticFourAtomicMu (1/2)) B
      =
    8 * B *
      (
        Real.cos (2*B) * (77/78 : ℝ) * Real.sin B
          * (Real.pi * (1/4-Real.sqrt 3/6))
        -
        Real.cos B * (20/39 : ℝ) * Real.sin (2*B)
          * (-(Real.pi*Real.sqrt 3/6))
      ) := by
  unfold quarticFourAtomicThreeTapJ2QuadraticPhase
  rw [quarticFourAtomic_half_response_one,
      quarticFourAtomic_half_response_two,
      quarticFourAtomic_half_sinFirst_one,
      quarticFourAtomic_sinFirst_two]

theorem quarticFourAtomic_twoThirds_threeTapQuadratic_formula
    (B : ℝ) :
    quarticFourAtomicThreeTapJ2QuadraticPhase
      (2/3) (quarticFourAtomicMu (2/3)) B
      =
    8 * B *
      (
        Real.cos (2*B) * (68/81 : ℝ) * Real.sin B
          * (Real.pi * (1/3-Real.sqrt 3/6))
        -
        Real.cos B * (40/81 : ℝ) * Real.sin (2*B)
          * (-(Real.pi*Real.sqrt 3/6))
      ) := by
  unfold quarticFourAtomicThreeTapJ2QuadraticPhase
  rw [quarticFourAtomic_twoThirds_response_one,
      quarticFourAtomic_twoThirds_response_two,
      quarticFourAtomic_twoThirds_sinFirst_one,
      quarticFourAtomic_sinFirst_two]

end Synthesis
