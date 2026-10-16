import Mathlib.Tactic
import Synthesis.RiemannG21LiteralOddSupportBounds

/-!
# G21 six-term determinant remainder coefficient

At sample radii `r` and `2r`, write the actual odd responses as
`T + E`, where `T` is the cubic truncation and `E` the fifth-order remainder.
The exact determinant difference has six bilinear terms.  Under the component
bounds already isolated by the Agda ledger,

  |T_a(r)|  <= r A_a1,      |T_a(2r)| <= r A_a2,
  |E_a(r)|  <= r^5 c_a,    |E_a(2r)| <= 32 r^5 c_a,

and likewise at height p, the full determinant error is bounded by

  r^6 * C,

where

  C = 32 A_a1 c_p + c_a A_p2 + A_a2 c_p
      + 32 c_a A_p1 + 64 c_a c_p.

The last `64` is the two remainder×remainder terms after using `r^10<=r^6`
for `0<=r<=1`.  This is the exact coefficient shape recorded in the Agda
frontier, now as an ordered-real theorem candidate.
-/

namespace Synthesis

/-- Exact six-term determinant correction after replacing both entries in each
row/column by truncation + remainder. -/
def sixTermDetError
    (ta1 ta2 tp1 tp2 ea1 ea2 ep1 ep2 : ℝ) : ℝ :=
  ta1*ep2 + ea1*tp2 + ea1*ep2
    - ta2*ep1 - ea2*tp1 - ea2*ep1

/-- Historical explicit coefficient. -/
def determinantErrorConstant
    (aa1 aa2 ap1 ap2 ca cp : ℝ) : ℝ :=
  32*aa1*cp + ca*ap2 + aa2*cp + 32*ca*ap1 + 64*ca*cp

private theorem six_abs_triangle (a b c d e f : ℝ) :
    |a+b+c-d-e-f| <= |a|+|b|+|c|+|d|+|e|+|f| := by
  calc
    |a+b+c-d-e-f| <= |a+b+c-d-e| + |f| := abs_sub _ _
    _ <= |a+b+c-d| + |e| + |f| := by
      nlinarith [abs_sub (a+b+c-d) e]
    _ <= |a+b+c| + |d| + |e| + |f| := by
      nlinarith [abs_sub (a+b+c) d]
    _ <= |a+b| + |c| + |d| + |e| + |f| := by
      nlinarith [abs_add (a+b) c]
    _ <= |a| + |b| + |c| + |d| + |e| + |f| := by
      nlinarith [abs_add a b]

/-- Six-term determinant error bound with the exact G21 coefficient. -/
theorem sixTermDetError_le_coefficient
    {r ta1 ta2 tp1 tp2 ea1 ea2 ep1 ep2 aa1 aa2 ap1 ap2 ca cp : ℝ}
    (hr0 : 0 <= r) (hr1 : r <= 1)
    (haa1 : 0 <= aa1) (haa2 : 0 <= aa2)
    (hap1 : 0 <= ap1) (hap2 : 0 <= ap2)
    (hca : 0 <= ca) (hcp : 0 <= cp)
    (hta1 : |ta1| <= r*aa1) (hta2 : |ta2| <= r*aa2)
    (htp1 : |tp1| <= r*ap1) (htp2 : |tp2| <= r*ap2)
    (hea1 : |ea1| <= r^5*ca) (hea2 : |ea2| <= 32*r^5*ca)
    (hep1 : |ep1| <= r^5*cp) (hep2 : |ep2| <= 32*r^5*cp) :
    |sixTermDetError ta1 ta2 tp1 tp2 ea1 ea2 ep1 ep2| <=
      r^6 * determinantErrorConstant aa1 aa2 ap1 ap2 ca cp := by
  have hr5 : 0 <= r^5 := by positivity
  have hr6 : 0 <= r^6 := by positivity
  have hr10le6 : r^10 <= r^6 := by
    rw [show r^10 = r^6 * r^4 by ring]
    have h4 : r^4 <= 1 := pow_le_one₀ hr0 hr1
    nlinarith [mul_le_mul_of_nonneg_left h4 hr6]
  have h1 : |ta1*ep2| <= r^6 * (32*aa1*cp) := by
    rw [abs_mul]
    have := mul_le_mul hta1 hep2 (abs_nonneg _) (mul_nonneg hr0 haa1)
    nlinarith
  have h2 : |ea1*tp2| <= r^6 * (ca*ap2) := by
    rw [abs_mul]
    have := mul_le_mul hea1 htp2 (abs_nonneg _) (mul_nonneg hr5 hca)
    nlinarith
  have h3 : |ea1*ep2| <= r^6 * (32*ca*cp) := by
    rw [abs_mul]
    have hmul := mul_le_mul hea1 hep2 (abs_nonneg _) (mul_nonneg hr5 hca)
    have hconst : 0 <= 32*ca*cp := by positivity
    have hpow := mul_le_mul_of_nonneg_right hr10le6 hconst
    nlinarith
  have h4 : |ta2*ep1| <= r^6 * (aa2*cp) := by
    rw [abs_mul]
    have := mul_le_mul hta2 hep1 (abs_nonneg _) (mul_nonneg hr0 haa2)
    nlinarith
  have h5 : |ea2*tp1| <= r^6 * (32*ca*ap1) := by
    rw [abs_mul]
    have := mul_le_mul hea2 htp1 (abs_nonneg _) (by positivity)
    nlinarith
  have h6 : |ea2*ep1| <= r^6 * (32*ca*cp) := by
    rw [abs_mul]
    have hmul := mul_le_mul hea2 hep1 (abs_nonneg _) (by positivity)
    have hconst : 0 <= 32*ca*cp := by positivity
    have hpow := mul_le_mul_of_nonneg_right hr10le6 hconst
    nlinarith
  unfold sixTermDetError determinantErrorConstant
  have htri := six_abs_triangle
    (ta1*ep2) (ea1*tp2) (ea1*ep2) (ta2*ep1) (ea2*tp1) (ea2*ep1)
  nlinarith

end Synthesis
