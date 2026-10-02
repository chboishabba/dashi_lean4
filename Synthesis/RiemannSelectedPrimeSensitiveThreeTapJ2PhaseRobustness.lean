import Synthesis.RiemannSelectedPrimeSensitiveThreeTapJ2AtomicRobustness

/-!
# Quantitative perturbation bounds for the transformed J2 phase coefficients

The normalized linear and quadratic phase coefficients depend only on four
scalar coordinates:
  A1, A2, U1, U2.

This file gives a reusable deterministic perturbation bound.  If each smooth
coordinate is within eta of an atomic coordinate whose magnitude is at most M,
then the phase-coefficient error is explicitly bounded.

This is the sign-transfer firewall: an atomic sign may be promoted only when
its strict margin exceeds this source-written error.
-/

noncomputable section
namespace Synthesis

open scoped Real

def j2LinearPhaseOfCoords
    (B A1 A2 U1 U2 : ℝ) : ℝ :=
  2 * B^2 * A1 * A2 * (Real.cos (2*B) - Real.cos B)
    +
  4 * B *
    (A2 * Real.sin B * U1
      - A1 * Real.sin (2*B) * U2)

def j2QuadraticPhaseOfCoords
    (B A1 A2 U1 U2 : ℝ) : ℝ :=
  8 * B *
    (Real.cos (2*B) * A2 * Real.sin B * U1
      - Real.cos B * A1 * Real.sin (2*B) * U2)

theorem normalizedJ2LinearPhase_eq_coords
    (g : ℝ → ℝ) (B : ℝ) :
    normalizedJ2LinearPhase g B
      =
    j2LinearPhaseOfCoords B
      (Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 1)
      (Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 2)
      (projectiveSinFirstResp g 1)
      (projectiveSinFirstResp g 2) := by
  rfl

theorem normalizedJ2QuadraticPhase_eq_coords
    (g : ℝ → ℝ) (B : ℝ) :
    normalizedJ2QuadraticPhase g B
      =
    j2QuadraticPhaseOfCoords B
      (Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 1)
      (Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 2)
      (projectiveSinFirstResp g 1)
      (projectiveSinFirstResp g 2) := by
  rfl

theorem quarticFourAtomicThreeTapJ2LinearPhase_eq_coords
    (lam mu B : ℝ) :
    quarticFourAtomicThreeTapJ2LinearPhase lam mu B
      =
    j2LinearPhaseOfCoords B
      (quarticFourAtomicRespAt lam mu 1)
      (quarticFourAtomicRespAt lam mu 2)
      (quarticFourAtomicSinFirstRespAt lam mu 1)
      (quarticFourAtomicSinFirstRespAt lam mu 2) := by
  rfl

theorem quarticFourAtomicThreeTapJ2QuadraticPhase_eq_coords
    (lam mu B : ℝ) :
    quarticFourAtomicThreeTapJ2QuadraticPhase lam mu B
      =
    j2QuadraticPhaseOfCoords B
      (quarticFourAtomicRespAt lam mu 1)
      (quarticFourAtomicRespAt lam mu 2)
      (quarticFourAtomicSinFirstRespAt lam mu 1)
      (quarticFourAtomicSinFirstRespAt lam mu 2) := by
  rfl

private theorem coord_abs_le
    {x x0 eta M : ℝ}
    (heta : 0 <= eta)
    (hM : 0 <= M)
    (herr : |x-x0| <= eta)
    (h0 : |x0| <= M) :
    |x| <= M + eta := by
  have htri : |x| <= |x-x0| + |x0| := by
    have h := abs_add (x-x0) x0
    simpa [sub_add_cancel] using h
  linarith

private theorem product_perturbation_bound
    {x y x0 y0 eta M : ℝ}
    (heta : 0 <= eta)
    (hM : 0 <= M)
    (hx : |x-x0| <= eta)
    (hy : |y-y0| <= eta)
    (hx0 : |x0| <= M)
    (hy0 : |y0| <= M) :
    |x*y-x0*y0| <= (2*M+eta)*eta := by
  have hxa := coord_abs_le heta hM hx hx0
  rw [show x*y-x0*y0 = x*(y-y0)+y0*(x-x0) by ring]
  calc
    |x*(y-y0)+y0*(x-x0)|
      <= |x*(y-y0)| + |y0*(x-x0)| := abs_add _ _
    _ = |x|*|y-y0| + |y0|*|x-x0| := by
      rw [abs_mul, abs_mul]
    _ <= (M+eta)*eta + M*eta := by
      gcongr
    _ = (2*M+eta)*eta := by ring

theorem j2LinearPhaseOfCoords_perturbation_bound
    {B A1 A2 U1 U2 a1 a2 u1 u2 eta M : ℝ}
    (heta : 0 <= eta)
    (hM : 0 <= M)
    (hA1 : |A1-a1| <= eta)
    (hA2 : |A2-a2| <= eta)
    (hU1 : |U1-u1| <= eta)
    (hU2 : |U2-u2| <= eta)
    (ha1 : |a1| <= M)
    (ha2 : |a2| <= M)
    (hu1 : |u1| <= M)
    (hu2 : |u2| <= M) :
    |j2LinearPhaseOfCoords B A1 A2 U1 U2
      - j2LinearPhaseOfCoords B a1 a2 u1 u2|
      <=
    (4*|B|^2 + 8*|B|) * ((2*M+eta)*eta) := by
  have hAA :=
    product_perturbation_bound heta hM hA1 hA2 ha1 ha2
  have hAU1 :=
    product_perturbation_bound heta hM hA2 hU1 ha2 hu1
  have hAU2 :=
    product_perturbation_bound heta hM hA1 hU2 ha1 hu2
  have hdc :
      |Real.cos (2*B)-Real.cos B| <= 2 := by
    calc
      |Real.cos (2*B)-Real.cos B|
        <= |Real.cos (2*B)| + |Real.cos B| := abs_sub _ _
      _ <= 1+1 := by
        gcongr <;> exact Real.abs_cos_le_one _
      _ = 2 := by norm_num
  have hs1 : |Real.sin B| <= 1 := Real.abs_sin_le_one _
  have hs2 : |Real.sin (2*B)| <= 1 := Real.abs_sin_le_one _
  unfold j2LinearPhaseOfCoords
  rw [show
      2*B^2*A1*A2*(Real.cos (2*B)-Real.cos B)
        + 4*B*(A2*Real.sin B*U1-A1*Real.sin (2*B)*U2)
        -
      (2*B^2*a1*a2*(Real.cos (2*B)-Real.cos B)
        + 4*B*(a2*Real.sin B*u1-a1*Real.sin (2*B)*u2))
      =
      2*B^2*(A1*A2-a1*a2)*(Real.cos (2*B)-Real.cos B)
        +
      4*B*
        ((A2*U1-a2*u1)*Real.sin B
          -(A1*U2-a1*u2)*Real.sin (2*B)) by ring]
  calc
    |2*B^2*(A1*A2-a1*a2)*(Real.cos (2*B)-Real.cos B)
        +
      4*B*
        ((A2*U1-a2*u1)*Real.sin B
          -(A1*U2-a1*u2)*Real.sin (2*B))|
      <=
    |2*B^2*(A1*A2-a1*a2)*(Real.cos (2*B)-Real.cos B)|
      +
    |4*B*
        ((A2*U1-a2*u1)*Real.sin B
          -(A1*U2-a1*u2)*Real.sin (2*B))| := abs_add _ _
    _ <=
    4*|B|^2*((2*M+eta)*eta)
      + 8*|B|*((2*M+eta)*eta) := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_pow,
          abs_of_nonneg (by norm_num : (0:ℝ) <= 2),
          abs_of_nonneg (by norm_num : (0:ℝ) <= 4)]
      have hdiff :
          |(A2*U1-a2*u1)*Real.sin B
            -(A1*U2-a1*u2)*Real.sin (2*B)|
          <= 2*((2*M+eta)*eta) := by
        calc
          |(A2*U1-a2*u1)*Real.sin B
            -(A1*U2-a1*u2)*Real.sin (2*B)|
            <=
          |(A2*U1-a2*u1)*Real.sin B|
            + |(A1*U2-a1*u2)*Real.sin (2*B)| := abs_sub _ _
          _ =
          |A2*U1-a2*u1|*|Real.sin B|
            + |A1*U2-a1*u2|*|Real.sin (2*B)| := by
              rw [abs_mul, abs_mul]
          _ <=
          ((2*M+eta)*eta)*1 + ((2*M+eta)*eta)*1 := by
            gcongr
          _ = 2*((2*M+eta)*eta) := by ring
      have hnonneg : 0 <= (2*M+eta)*eta := by positivity
      gcongr
    _ = (4*|B|^2+8*|B|)*((2*M+eta)*eta) := by ring

theorem j2QuadraticPhaseOfCoords_perturbation_bound
    {B A1 A2 U1 U2 a1 a2 u1 u2 eta M : ℝ}
    (heta : 0 <= eta)
    (hM : 0 <= M)
    (hA1 : |A1-a1| <= eta)
    (hA2 : |A2-a2| <= eta)
    (hU1 : |U1-u1| <= eta)
    (hU2 : |U2-u2| <= eta)
    (ha1 : |a1| <= M)
    (ha2 : |a2| <= M)
    (hu1 : |u1| <= M)
    (hu2 : |u2| <= M) :
    |j2QuadraticPhaseOfCoords B A1 A2 U1 U2
      - j2QuadraticPhaseOfCoords B a1 a2 u1 u2|
      <=
    16*|B|*((2*M+eta)*eta) := by
  have hAU1 :=
    product_perturbation_bound heta hM hA2 hU1 ha2 hu1
  have hAU2 :=
    product_perturbation_bound heta hM hA1 hU2 ha1 hu2
  have hc1 : |Real.cos B| <= 1 := Real.abs_cos_le_one _
  have hc2 : |Real.cos (2*B)| <= 1 := Real.abs_cos_le_one _
  have hs1 : |Real.sin B| <= 1 := Real.abs_sin_le_one _
  have hs2 : |Real.sin (2*B)| <= 1 := Real.abs_sin_le_one _
  unfold j2QuadraticPhaseOfCoords
  rw [show
      8*B*
        (Real.cos (2*B)*A2*Real.sin B*U1
          -Real.cos B*A1*Real.sin (2*B)*U2)
        -
      8*B*
        (Real.cos (2*B)*a2*Real.sin B*u1
          -Real.cos B*a1*Real.sin (2*B)*u2)
      =
      8*B*
        (Real.cos (2*B)*Real.sin B*(A2*U1-a2*u1)
          -Real.cos B*Real.sin (2*B)*(A1*U2-a1*u2)) by ring]
  rw [abs_mul,
      abs_of_nonneg (by norm_num : (0:ℝ) <= 8)]
  have hinside :
      |Real.cos (2*B)*Real.sin B*(A2*U1-a2*u1)
        -Real.cos B*Real.sin (2*B)*(A1*U2-a1*u2)|
        <= 2*((2*M+eta)*eta) := by
    calc
      |Real.cos (2*B)*Real.sin B*(A2*U1-a2*u1)
        -Real.cos B*Real.sin (2*B)*(A1*U2-a1*u2)|
        <=
      |Real.cos (2*B)*Real.sin B*(A2*U1-a2*u1)|
        +
      |Real.cos B*Real.sin (2*B)*(A1*U2-a1*u2)| := abs_sub _ _
      _ =
      |Real.cos (2*B)|*|Real.sin B|*|A2*U1-a2*u1|
        +
      |Real.cos B|*|Real.sin (2*B)|*|A1*U2-a1*u2| := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul]
      _ <=
      1*1*((2*M+eta)*eta) + 1*1*((2*M+eta)*eta) := by
        gcongr
      _ = 2*((2*M+eta)*eta) := by ring
  nlinarith [abs_nonneg B]

/-- A strict negative atomic margin transfers whenever it dominates the
source-written perturbation envelope. -/
theorem j2LinearPhaseOfCoords_neg_of_atomic_margin
    {B A1 A2 U1 U2 a1 a2 u1 u2 eta M margin : ℝ}
    (hbound :
      |j2LinearPhaseOfCoords B A1 A2 U1 U2
        - j2LinearPhaseOfCoords B a1 a2 u1 u2|
        <= margin)
    (hatomic :
      j2LinearPhaseOfCoords B a1 a2 u1 u2 < -margin) :
    j2LinearPhaseOfCoords B A1 A2 U1 U2 < 0 := by
  have hlow := (abs_le.mp hbound).2
  linarith

theorem j2LinearPhaseOfCoords_pos_of_atomic_margin
    {B A1 A2 U1 U2 a1 a2 u1 u2 margin : ℝ}
    (hbound :
      |j2LinearPhaseOfCoords B A1 A2 U1 U2
        - j2LinearPhaseOfCoords B a1 a2 u1 u2|
        <= margin)
    (hatomic :
      margin < j2LinearPhaseOfCoords B a1 a2 u1 u2) :
    0 < j2LinearPhaseOfCoords B A1 A2 U1 U2 := by
  have hup := (abs_le.mp hbound).1
  linarith

end Synthesis
