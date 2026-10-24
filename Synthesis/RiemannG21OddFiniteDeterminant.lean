import Mathlib.Tactic
import Synthesis.RiemannG21SupportPolynomial

/-!
# G21 literal odd finite determinant algebra

The six-scaled cubic odd response is

  T_y(r) = -6 r N1(y) + r^3 N3(y).

At radii `r` and `2r`, the cubic determinant is exactly

  D_cubic = T_a(r) T_p(2r) - T_a(2r) T_p(r)
          = -(36 r^4) * Delta_odd,

where `Delta_odd = N1(a)N3(p)-N3(a)N1(p)`.

Adding remainders `E_y(r)` and `E_y(2r)` gives an actual determinant whose
exact difference from `D_cubic` is the six-term carrier proved/bounded in the
preceding module.
-/

namespace Synthesis

/-- Six-scaled cubic truncation. -/
def oddCubicTrunc (r n1 n3 : ℝ) : ℝ :=
  -6*r*n1 + r^3*n3

/-- Cubic determinant at radii r and 2r. -/
def oddCubicDeterminant
    (r n1a n3a n1p n3p : ℝ) : ℝ :=
  oddCubicTrunc r n1a n3a * oddCubicTrunc (2*r) n1p n3p
    - oddCubicTrunc (2*r) n1a n3a * oddCubicTrunc r n1p n3p

/-- Actual determinant after adding remainder values at r and 2r. -/
def oddActualDeterminant
    (r n1a n3a n1p n3p ea1 ea2 ep1 ep2 : ℝ) : ℝ :=
  (oddCubicTrunc r n1a n3a + ea1) *
      (oddCubicTrunc (2*r) n1p n3p + ep2)
    - (oddCubicTrunc (2*r) n1a n3a + ea2) *
      (oddCubicTrunc r n1p n3p + ep1)

/-- Exact cubic signal factorization. -/
theorem oddCubicDeterminant_eq_signal
    {r n1a n3a n1p n3p : ℝ} :
    oddCubicDeterminant r n1a n3a n1p n3p =
      -(36*r^4) * (n1a*n3p - n3a*n1p) := by
  unfold oddCubicDeterminant oddCubicTrunc
  ring

/-- Exact six-term remainder decomposition. -/
theorem oddActualDeterminant_sub_cubic
    {r n1a n3a n1p n3p ea1 ea2 ep1 ep2 : ℝ} :
    oddActualDeterminant r n1a n3a n1p n3p ea1 ea2 ep1 ep2
      - oddCubicDeterminant r n1a n3a n1p n3p
      = sixTermDetError
          (oddCubicTrunc r n1a n3a) (oddCubicTrunc (2*r) n1a n3a)
          (oddCubicTrunc r n1p n3p) (oddCubicTrunc (2*r) n1p n3p)
          ea1 ea2 ep1 ep2 := by
  unfold oddActualDeterminant oddCubicDeterminant sixTermDetError
  ring

/-- Unit-radius truncation bound at r. -/
theorem oddCubicTrunc_abs_le_r_A1
    {r n1 n3 : ℝ}
    (hr0 : 0 <= r) (hr1 : r <= 1)
    (h1 : 0 <= n1) (h3 : 0 <= n3) :
    |oddCubicTrunc r n1 n3| <= r*(6*n1+n3) := by
  unfold oddCubicTrunc
  calc
    |-6*r*n1 + r^3*n3| <= |-6*r*n1| + |r^3*n3| := abs_add _ _
    _ = 6*r*n1 + r^3*n3 := by
      rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg hr0,
        abs_of_nonneg h1, abs_of_nonneg (by positivity : 0 <= r^3), abs_of_nonneg h3]
      ring
    _ <= r*(6*n1+n3) := by
      have hr2 : r^2 <= 1 := pow_le_one₀ hr0 hr1
      have hr3 : r^3 <= r := by
        rw [show r^3 = r*r^2 by ring]
        nlinarith [mul_le_mul_of_nonneg_left hr2 hr0]
      nlinarith

/-- Unit-radius truncation bound at 2r in the coefficient normalization used by
G21.  No assumption `2r<=1` is needed; only `r<=1`. -/
theorem oddCubicTrunc_two_mul_abs_le_r_A2
    {r n1 n3 : ℝ}
    (hr0 : 0 <= r) (hr1 : r <= 1)
    (h1 : 0 <= n1) (h3 : 0 <= n3) :
    |oddCubicTrunc (2*r) n1 n3| <= r*(12*n1+8*n3) := by
  unfold oddCubicTrunc
  have hr2 : r^2 <= 1 := pow_le_one₀ hr0 hr1
  have hr3 : r^3 <= r := by
    rw [show r^3 = r*r^2 by ring]
    nlinarith [mul_le_mul_of_nonneg_left hr2 hr0]
  calc
    |-6*(2*r)*n1 + (2*r)^3*n3|
        <= |-6*(2*r)*n1| + |(2*r)^3*n3| := abs_add _ _
    _ = 12*r*n1 + 8*r^3*n3 := by
      rw [abs_mul, abs_mul, abs_mul, abs_neg,
        abs_of_nonneg hr0, abs_of_nonneg h1, abs_of_nonneg h3]
      have : |(2:ℝ)| = 2 := by norm_num
      rw [abs_mul, this]
      ring
    _ <= r*(12*n1+8*n3) := by nlinarith

end Synthesis
