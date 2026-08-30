/-
# The radius expansion of the two-taper cross determinant

Each literal channel coordinate is quadratically small in the sampling radius,

    |c_j(r) - r² L_j| ≤ r⁴ B_j,        0 ≤ r ≤ 1,

(this is the shape proved for the two-radius height defect in
`LiteralWeilTargetDefectLeadingCoefficient`).  The cross determinant of two such
pairs therefore has leading term of order `r⁴`, with a *relative* error of order
`r²`:

    |Δ(r) - r⁴ Δ₀| ≤ r⁶ C,     Δ₀ = L_{n,0} L_{t,1} - L_{n,1} L_{t,0}.

Consequently the admission test of `TwoTaperCrossDetSchur` becomes a **radius-free
coefficient comparison**:

    r² C < |Δ₀|   ⟹   Δ(r) ≠ 0.

Everything here is elementary algebra with explicit constants; nothing is asserted
about the size of `Δ₀` itself.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Mathlib.Tactic

noncomputable section

namespace Zeta23Bridge
namespace TwoTaperCrossDetLeading

/-- The explicit remainder constant of one product `c · d` of two quadratically
small channels. -/
def prodRemainder (Lc Bc Ld Bd : ℝ) : ℝ := |Lc| * Bd + Bc * |Ld| + Bc * Bd

theorem prodRemainder_nonneg {Lc Bc Ld Bd : ℝ} (hBc : 0 ≤ Bc) (hBd : 0 ≤ Bd) :
    0 ≤ prodRemainder Lc Bc Ld Bd := by
  unfold prodRemainder
  have := abs_nonneg Lc
  have := abs_nonneg Ld
  positivity

/-- The product of two quadratically small channels is quartically small, with an
explicit sextic remainder. -/
theorem abs_prod_sub_leading_le {c d Lc Bc Ld Bd r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hc : |c - r ^ 2 * Lc| ≤ r ^ 4 * Bc) (hd : |d - r ^ 2 * Ld| ≤ r ^ 4 * Bd)
    (hBc : 0 ≤ Bc) (hBd : 0 ≤ Bd) :
    |c * d - r ^ 4 * (Lc * Ld)| ≤ r ^ 6 * prodRemainder Lc Bc Ld Bd := by
  have hr2 : (0:ℝ) ≤ r ^ 2 := by positivity
  have hr4 : (0:ℝ) ≤ r ^ 4 := by positivity
  have hr6 : (0:ℝ) ≤ r ^ 6 := by positivity
  have hd' : |d| ≤ r ^ 2 * |Ld| + r ^ 4 * Bd := by
    have h := abs_sub_abs_le_abs_sub d (r ^ 2 * Ld)
    have : |r ^ 2 * Ld| = r ^ 2 * |Ld| := by
      rw [abs_mul, abs_of_nonneg hr2]
    linarith [hd, h, this.le, this.ge]
  have hsplit : c * d - r ^ 4 * (Lc * Ld)
      = (c - r ^ 2 * Lc) * d + (r ^ 2 * Lc) * (d - r ^ 2 * Ld) := by ring
  have hb1 : |(c - r ^ 2 * Lc) * d| ≤ (r ^ 4 * Bc) * (r ^ 2 * |Ld| + r ^ 4 * Bd) := by
    rw [abs_mul]
    exact mul_le_mul hc hd' (abs_nonneg _) (by positivity)
  have hb2 : |(r ^ 2 * Lc) * (d - r ^ 2 * Ld)| ≤ (r ^ 2 * |Lc|) * (r ^ 4 * Bd) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hr2]
    exact mul_le_mul_of_nonneg_left hd (by positivity)
  have htri : |c * d - r ^ 4 * (Lc * Ld)|
      ≤ (r ^ 4 * Bc) * (r ^ 2 * |Ld| + r ^ 4 * Bd) + (r ^ 2 * |Lc|) * (r ^ 4 * Bd) := by
    rw [hsplit]
    exact (abs_add_le _ _).trans (by linarith)
  have habsorb : r ^ 8 * (Bc * Bd) ≤ r ^ 6 * (Bc * Bd) := by
    have hsq : r ^ 2 ≤ 1 := by nlinarith
    have h1 : r ^ 8 ≤ r ^ 6 :=
      calc r ^ 8 = r ^ 6 * r ^ 2 := by ring
        _ ≤ r ^ 6 * 1 := mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = r ^ 6 := by ring
    exact mul_le_mul_of_nonneg_right h1 (mul_nonneg hBc hBd)
  unfold prodRemainder
  nlinarith [htri, habsorb]

/-- The explicit remainder constant of the two-taper cross determinant. -/
def crossRemainder (Ln0 Bn0 Ln1 Bn1 Lt0 Bt0 Lt1 Bt1 : ℝ) : ℝ :=
  prodRemainder Ln0 Bn0 Lt1 Bt1 + prodRemainder Ln1 Bn1 Lt0 Bt0

theorem crossRemainder_nonneg {Ln0 Bn0 Ln1 Bn1 Lt0 Bt0 Lt1 Bt1 : ℝ}
    (hBn0 : 0 ≤ Bn0) (hBn1 : 0 ≤ Bn1) (hBt0 : 0 ≤ Bt0) (hBt1 : 0 ≤ Bt1) :
    0 ≤ crossRemainder Ln0 Bn0 Ln1 Bn1 Lt0 Bt0 Lt1 Bt1 :=
  add_nonneg (prodRemainder_nonneg hBn0 hBt1) (prodRemainder_nonneg hBn1 hBt0)

/-- **The cross determinant of two quadratically small channel pairs has leading
term of order `r⁴`, with a relative error of order `r²`.** -/
theorem abs_crossDet_sub_leading_le {n0 n1 t0 t1 Ln0 Bn0 Ln1 Bn1 Lt0 Bt0 Lt1 Bt1 r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hn0 : |n0 - r ^ 2 * Ln0| ≤ r ^ 4 * Bn0) (hn1 : |n1 - r ^ 2 * Ln1| ≤ r ^ 4 * Bn1)
    (ht0 : |t0 - r ^ 2 * Lt0| ≤ r ^ 4 * Bt0) (ht1 : |t1 - r ^ 2 * Lt1| ≤ r ^ 4 * Bt1)
    (hBn0 : 0 ≤ Bn0) (hBn1 : 0 ≤ Bn1) (hBt0 : 0 ≤ Bt0) (hBt1 : 0 ≤ Bt1) :
    |n0 * t1 - n1 * t0 - r ^ 4 * (Ln0 * Lt1 - Ln1 * Lt0)|
      ≤ r ^ 6 * crossRemainder Ln0 Bn0 Ln1 Bn1 Lt0 Bt0 Lt1 Bt1 := by
  have h1 := abs_prod_sub_leading_le hr0 hr1 hn0 ht1 hBn0 hBt1
  have h2 := abs_prod_sub_leading_le hr0 hr1 hn1 ht0 hBn1 hBt0
  have hsplit : n0 * t1 - n1 * t0 - r ^ 4 * (Ln0 * Lt1 - Ln1 * Lt0)
      = (n0 * t1 - r ^ 4 * (Ln0 * Lt1)) - (n1 * t0 - r ^ 4 * (Ln1 * Lt0)) := by ring
  have htri : |n0 * t1 - n1 * t0 - r ^ 4 * (Ln0 * Lt1 - Ln1 * Lt0)|
      ≤ |n0 * t1 - r ^ 4 * (Ln0 * Lt1)| + |n1 * t0 - r ^ 4 * (Ln1 * Lt0)| := by
    rw [hsplit]
    exact abs_sub _ _
  unfold crossRemainder
  nlinarith [htri, h1, h2]

/-- **The radius-free coefficient gate.**  If the leading cross determinant beats the
explicit relative remainder at the radius used, the cross determinant itself is
nonzero — and hence, by `TwoTaperCrossDetSchur`, the Gram wedge is strict. -/
theorem crossDet_ne_zero_of_coefficient_gate
    {n0 n1 t0 t1 Ln0 Bn0 Ln1 Bn1 Lt0 Bt0 Lt1 Bt1 r : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hn0 : |n0 - r ^ 2 * Ln0| ≤ r ^ 4 * Bn0) (hn1 : |n1 - r ^ 2 * Ln1| ≤ r ^ 4 * Bn1)
    (ht0 : |t0 - r ^ 2 * Lt0| ≤ r ^ 4 * Bt0) (ht1 : |t1 - r ^ 2 * Lt1| ≤ r ^ 4 * Bt1)
    (hBn0 : 0 ≤ Bn0) (hBn1 : 0 ≤ Bn1) (hBt0 : 0 ≤ Bt0) (hBt1 : 0 ≤ Bt1)
    (hgate : r ^ 2 * crossRemainder Ln0 Bn0 Ln1 Bn1 Lt0 Bt0 Lt1 Bt1
      < |Ln0 * Lt1 - Ln1 * Lt0|) :
    n0 * t1 - n1 * t0 ≠ 0 := by
  intro hzero
  have hbd := abs_crossDet_sub_leading_le hr0.le hr1 hn0 hn1 ht0 ht1 hBn0 hBn1 hBt0 hBt1
  rw [hzero, zero_sub, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ r ^ 4)] at hbd
  have hr4 : (0:ℝ) < r ^ 4 := by positivity
  have hlt : r ^ 4 * (r ^ 2 * crossRemainder Ln0 Bn0 Ln1 Bn1 Lt0 Bt0 Lt1 Bt1)
      < r ^ 4 * |Ln0 * Lt1 - Ln1 * Lt0| := by
    exact mul_lt_mul_of_pos_left hgate hr4
  nlinarith [hbd, hlt]

/-! ## When is the leading determinant nonzero? -/

/-- **Response-ratio separation.**  The leading cross determinant is nonzero exactly
when the two tapers see the nuisance and the target in different proportions. -/
theorem leadingDet_ne_zero_of_ratio_ne {Ln0 Ln1 Lt0 Lt1 : ℝ}
    (h0 : Lt0 ≠ 0) (h1 : Lt1 ≠ 0) (hratio : Ln0 / Lt0 ≠ Ln1 / Lt1) :
    Ln0 * Lt1 - Ln1 * Lt0 ≠ 0 := by
  intro hzero
  apply hratio
  field_simp
  linarith [hzero]

/-- The converse: proportional responses give a vanishing leading determinant, so a
nuisance zero whose two-taper response profile is parallel to the target's cannot be
eliminated by this mechanism. -/
theorem leadingDet_eq_zero_of_ratio_eq {Ln0 Ln1 Lt0 Lt1 : ℝ}
    (h0 : Lt0 ≠ 0) (h1 : Lt1 ≠ 0) (hratio : Ln0 / Lt0 = Ln1 / Lt1) :
    Ln0 * Lt1 - Ln1 * Lt0 = 0 := by
  field_simp at hratio
  linarith [hratio]

end TwoTaperCrossDetLeading
end Zeta23Bridge
