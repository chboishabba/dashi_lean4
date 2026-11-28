import Mathlib

/-!
# Signed Mellin moment progression on the actual two-crossing chart

The selected 234446.a1 source has positive/negative/positive density and
vanishing zeroth moment. This file proves the *unbounded degree* algebraic
factorization used to compare consecutive Mellin moments. It neither
assumes nor proves the missing second complex derivative vanishes.
-/

namespace DASHI.BSD.SignedCrossing

/-- Complete homogeneous polynomial of degree n in the two crossing addresses. -/
def h (a b : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => a * h a b n + b^(n+1)

theorem h_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    0 ≤ h a b n := by
  induction n with
  | zero => simp [h]
  | succ n ih =>
    exact add_nonneg (mul_nonneg ha ih) (pow_nonneg hb _)

theorem h_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    0 < h a b n := by
  induction n with
  | zero => simp [h]
  | succ n ih =>
    exact add_pos (mul_pos ha ih) (pow_pos hb _)

theorem h_recurrence (a b : ℝ) (n : ℕ) :
    h a b (n+2) = (a+b)*h a b (n+1) - a*b*h a b n := by
  calc
    h a b (n+2) = a*h a b (n+1) + b^(n+2) := rfl
    _ = a*h a b (n+1) + b*(h a b (n+1)-a*h a b n) := by
      rw [show h a b (n+1)-a*h a b n = b^(n+1) by
        rw [show h a b (n+1) = a*h a b n+b^(n+1) from rfl]
        ring]
      rw [show b^(n+2) = b^(n+1)*b by rw [pow_succ]]
      ring
    _ = _ := by ring

/-- Quotient by the original two-crossing polynomial; no division at either
crossing and all coefficients retain their signs. Index n corresponds to j=n+1. -/
def quotient (a b x : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => a*b*quotient a b x n + h a b (n+1)*x^(n+1)

theorem quotient_pos {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 ≤ x) (n : ℕ) : 0 < quotient a b x n := by
  induction n with
  | zero => simp [quotient]
  | succ n ih =>
    exact add_pos_of_pos_of_nonneg (mul_pos (mul_pos ha hb) ih)
      (mul_nonneg (h_nonneg ha.le hb.le _) (pow_nonneg hx _))

def signedPolynomial (a b x : ℝ) (n : ℕ) : ℝ :=
  h a b n * x^(n+2) - h a b (n+1) * x^(n+1) + (a*b)^(n+1)

theorem signedPolynomial_factor (a b x : ℝ) (n : ℕ) :
    signedPolynomial a b x n = (x-a)*(x-b)*quotient a b x n := by
  induction n with
  | zero => simp [signedPolynomial, h, quotient]; ring
  | succ n ih =>
    have hr : signedPolynomial a b x (n+1) =
        a*b*signedPolynomial a b x n +
          (x-a)*(x-b)*h a b (n+1)*x^(n+1) := by
      unfold signedPolynomial
      rw [h_recurrence]
      simp only [Nat.succ_eq_add_one, Nat.add_assoc, pow_succ]
      ring
    rw [hr, ih]
    change _ = (x-a)*(x-b)*(a*b*quotient a b x n + h a b (n+1)*x^(n+1))
    ring

/-- Every degree has the original pointwise signed geometry, including zero
density at crossing points. -/
theorem density_times_signedPolynomial_nonneg
    {a b x f : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 ≤ x)
    (hs : 0 ≤ f*(x-a)*(x-b)) (n : ℕ) :
    0 ≤ f*signedPolynomial a b x n := by
  rw [signedPolynomial_factor]
  calc
    0 ≤ (f*(x-a)*(x-b))*quotient a b x n :=
      mul_nonneg hs (quotient_pos ha hb hx n).le
    _ = _ := by ring

theorem density_times_signedPolynomial_pos
    {a b x f : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 ≤ x)
    (hs : 0 < f*(x-a)*(x-b)) (n : ℕ) :
    0 < f*signedPolynomial a b x n := by
  rw [signedPolynomial_factor]
  calc
    0 < (f*(x-a)*(x-b))*quotient a b x n :=
      mul_pos hs (quotient_pos ha hb hx n)
    _ = _ := by ring

/-- Once the actual integrated signed polynomial is strictly positive and
the zeroth mass is exactly zero, a nonnegative moment forces the next moment
strictly positive. Integration and source positivity must be supplied by
the original two-crossing Mellin measure, not inferred from fixtures. -/
theorem next_moment_pos {a b m0 mj mj1 : ℝ} (ha : 0 < a) (hb : 0 < b)
    (n : ℕ) (hz : m0 = 0) (hm : 0 ≤ mj)
    (hp : 0 < h a b n * mj1 - h a b (n+1) * mj + (a*b)^(n+1)*m0) :
    0 < mj1 := by
  rw [hz, mul_zero, add_zero] at hp
  have hh := h_pos ha hb n
  have hm' := mul_nonneg (h_nonneg ha.le hb.le (n+1)) hm
  have hp' : 0 < h a b n * mj1 := by linarith
  exact pos_of_mul_pos_left hp' hh.le


/-- The actual B-M7s outward Mellin interval gives a strict comparison
on the circle |z| = 7/50000000. The tail bound comes from the original
coefficient majorant 2/(c*t)^2, with c > 1/80. This is the arithmetic
input to Rouché, not a native complex zero-count theorem. -/
def centralDiskRadius : ℝ := 7 / 50000000

theorem centralDiskMarginExact :
    (13 / 10^12 : ℝ) +
      25600 * centralDiskRadius^4 / (1 - centralDiskRadius^2) <
      (8270793387711404 / 10^12 : ℝ) * centralDiskRadius^2 / 12 := by
  norm_num [centralDiskRadius]

theorem centralDiskBoundaryDominance (m1 m2 tail : ℝ)
    (h1 : |m1| ≤ 13 / 10^12)
    (h2 : 8270793387711404 / 10^12 ≤ m2)
    (htail : tail ≤ 25600 * centralDiskRadius^4 / (1 - centralDiskRadius^2)) :
    |m1| + tail < m2 * centralDiskRadius^2 / 12 := by
  calc
    |m1| + tail ≤ (13 / 10^12 : ℝ) +
        25600 * centralDiskRadius^4 / (1 - centralDiskRadius^2) :=
      add_le_add h1 htail
    _ < (8270793387711404 / 10^12 : ℝ) * centralDiskRadius^2 / 12 :=
      centralDiskMarginExact
    _ ≤ m2 * centralDiskRadius^2 / 12 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right h2 (sq_nonneg _)) (by norm_num)

theorem centralDiskSquaredRootError :
    12 * (25600 * centralDiskRadius^4 / (1 - centralDiskRadius^2)) /
        (8270793387711404 / 10^12 : ℝ) < 2 / 10^26 := by
  norm_num [centralDiskRadius]


/-- Squared central coordinate w=z² retains the sign. The Mellin
tail in w has coefficients bounded by 25600 starting at degree 2. -/
def centralSquaredRadius : ℝ := centralDiskRadius ^ 2

def centralQuadraticLower : ℝ := 8270793387711404 / (12 * 10^12)

def centralContractionBound : ℝ :=
  25600 * (2 * centralSquaredRadius - centralSquaredRadius^2) /
    (centralQuadraticLower * (1-centralSquaredRadius)^2)

theorem centralContractionBound_small :
    0 < centralContractionBound ∧ centralContractionBound < 1 / 10^11 := by
  norm_num [centralContractionBound, centralSquaredRadius, centralDiskRadius,
    centralQuadraticLower]

theorem centralSquared_self_map :
    (13 / 10^12 + 25600 * centralSquaredRadius^2 /
      (1-centralSquaredRadius)) / centralQuadraticLower <
        centralSquaredRadius := by
  norm_num [centralSquaredRadius, centralDiskRadius, centralQuadraticLower]

/-- Difference estimate for every degree, used in the absolutely
convergent tail rather than a finite Taylor truncation. -/
theorem norm_pow_sub_pow_bound {x y : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (n : ℕ) :
    ‖x^(n+1)-y^(n+1)‖ ≤ (n+1 : ℝ)*R^n*‖x-y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hdecomp : x^(n+1+1)-y^(n+1+1) =
        x*(x^(n+1)-y^(n+1))+(x-y)*y^(n+1) := by
      rw [pow_succ x, pow_succ y]
      ring
    rw [hdecomp]
    calc
      ‖x*(x^(n+1)-y^(n+1))+(x-y)*y^(n+1)‖ ≤
          ‖x*(x^(n+1)-y^(n+1))‖+‖(x-y)*y^(n+1)‖ := norm_add_le _ _
      _ ≤ R*((n+1 : ℝ)*R^n*‖x-y‖)+‖x-y‖*R^(n+1) := by
        rw [norm_mul, norm_mul, norm_pow]
        exact add_le_add
          (mul_le_mul hx ih (norm_nonneg _) hR)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy _) (norm_nonneg _))
      _ = _ := by
        push_cast
        rw [pow_succ]
        ring

/-- Algebraic fixed-point identity: no claim that a numerically small
signed scalar is exactly zero. -/
theorem signed_squared_fixed_point_iff
    (m a w tail : ℂ) (ha : a ≠ 0) :
    w = -(m+tail)/a ↔ m+a*w+tail=0 := by
  constructor
  · intro h
    have h' := (eq_div_iff ha).mp h
    linear_combination h'
  · intro h
    apply (eq_div_iff ha).mpr
    linear_combination h

end DASHI.BSD.SignedCrossing
