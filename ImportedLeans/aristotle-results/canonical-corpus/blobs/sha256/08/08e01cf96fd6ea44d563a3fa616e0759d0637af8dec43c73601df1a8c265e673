import Mathlib

/-!
# Why the palettes all look the same

The plates of this project read a function on the triangles of the Euclid ladder and
colour each triangle by the *rank* of its reading in the sorted palette of the plate
(`DeltaTriangles.sortedReadings`, `PaletteCharacterTable`).  Drawing a gallery of
modular forms one notices at once that the interesting plates are *the same picture*:
the McKay--Thompson series `T₁ₐ`, `T₂ₐ`, `T₃ₐ` are indistinguishable from each other,
and the newforms of the LMFDB gallery are indistinguishable from `Δ`.

This file proves that this is forced, and says exactly where.  A normalised `q`-series

  `f(z) = ∑_{n ≥ 1} a n qⁿ`,  `q = e^{2πiz}`,  `a 1 = 1`,  `‖a n‖ ≤ C (n+1)^k`

has `‖f(z)‖` within `C·K·‖q‖²` of `‖q‖ = e^{-2π Im z}`; so high enough above the real
axis the reading is a strictly decreasing function of `Im z` *and of nothing else*.
Two such series therefore order any separated sample of points identically, and a rank
palette computed from one is literally equal to the rank palette computed from the
other.  A hauptmodul `1/q + ∑_{n ≥ 0} c n qⁿ` behaves the same way with the order
reversed, which is why the whole `T` series shares one picture, and why that picture is
the negative of the `Δ` picture.

The hypothesis `‖a n‖ ≤ C (n+1)^k` is what Deligne's bound gives for the Hecke
eigenvalues of a newform (`|a n| ≤ d(n) n^{(k-1)/2}`); it is assumed here, not proved.
-/

namespace PaletteUniversality

open scoped Real
open Complex

/-! ### Definitions -/

/-- The nome `q = e^{2πiz}`. -/
noncomputable def qq (z : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * z)

/-- A `q`-series `∑ₙ a n qⁿ`.  For a cusp form `a 0 = 0` and `a 1 = 1`. -/
noncomputable def qSeries (a : ℕ → ℂ) (z : ℂ) : ℂ := ∑' n : ℕ, a n * qq z ^ n

/-- A hauptmodul-shaped series `1/q + ∑_{n ≥ 0} c n qⁿ`: this is the shape of `j`,
of `T₁ₐ = j - 744` and of the McKay--Thompson series `T₂ₐ`, `T₃ₐ`. -/
noncomputable def hauptSeries (c : ℕ → ℂ) (z : ℂ) : ℂ := (qq z)⁻¹ + ∑' n : ℕ, c n * qq z ^ n

/-- The coefficients are polynomially bounded: `‖a n‖ ≤ C (n+1)^k`. -/
def PolyBound (a : ℕ → ℂ) (C : ℝ) (k : ℕ) : Prop := ∀ n : ℕ, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ k

/-- A normalised cusp-form-shaped `q`-series: no constant term, leading coefficient one,
polynomially bounded coefficients. -/
structure Normalized (a : ℕ → ℂ) (C : ℝ) (k : ℕ) : Prop where
  zero : a 0 = 0
  one : a 1 = 1
  bound : PolyBound a C k

/-- The constant of the tail bound, `K k = ∑_{n ≥ 0} (n+3)^k 2^{-n}`. -/
noncomputable def tailConst (k : ℕ) : ℝ := ∑' n : ℕ, ((n : ℝ) + 3) ^ k * (1 / 2 : ℝ) ^ n

/-- The colour of a tile: the number of samples of `S` whose reading is strictly smaller
than the reading at `z`.  This is the rank the plates paint with. -/
noncomputable def paletteRank (f : ℂ → ℂ) (S : Finset ℂ) (z : ℂ) : ℕ :=
  (S.filter fun w => ‖f w‖ < ‖f z‖).card

/-! ### The nome -/

theorem norm_qq (z : ℂ) : ‖qq z‖ = Real.exp (-(2 * Real.pi * z.im)) := by
  simp [qq, Complex.norm_exp]

theorem norm_qq_pos (z : ℂ) : 0 < ‖qq z‖ := by
  rw [norm_qq]; positivity

theorem qq_ne_zero (z : ℂ) : qq z ≠ 0 := by
  simpa using (norm_pos_iff.mp (norm_qq_pos z))

theorem norm_qq_le_of_im_le {z w : ℂ} (h : w.im ≤ z.im) : ‖qq z‖ ≤ ‖qq w‖ := by
  rw [norm_qq, norm_qq]
  exact Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])

/-! ### Summability and the tail bound -/

/-- `∑ₙ (n+m)^k rⁿ` converges for `0 < r < 1`. -/
theorem summable_shift (m k : ℕ) {r : ℝ} (hr0 : 0 < r) (hr : r < 1) :
    Summable fun n : ℕ => ((n : ℝ) + m) ^ k * r ^ n := by
  have h : Summable fun n : ℕ => (n : ℝ) ^ k * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one k
      (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr)
  have h3 := ((summable_nat_add_iff m).2 h).mul_left ((r ^ m)⁻¹)
  refine h3.congr fun n => ?_
  have : r ^ m ≠ 0 := by positivity
  push_cast
  field_simp [pow_add]
  ring

theorem summable_tailConst (k : ℕ) :
    Summable fun n : ℕ => ((n : ℝ) + 3) ^ k * (1 / 2 : ℝ) ^ n :=
  summable_shift 3 k (by norm_num) (by norm_num)

theorem tailConst_nonneg (k : ℕ) : 0 ≤ tailConst k := by
  refine tsum_nonneg fun n => ?_
  positivity

theorem PolyBound.nonneg {a : ℕ → ℂ} {C : ℝ} {k : ℕ} (hb : PolyBound a C k) : 0 ≤ C := by
  have h := hb 0
  simp at h
  nlinarith [norm_nonneg (a 0)]

theorem summable_norm_qSeries {a : ℕ → ℂ} {C : ℝ} {k : ℕ} (hb : PolyBound a C k) {z : ℂ}
    (hz : ‖qq z‖ < 1) : Summable fun n : ℕ => ‖a n * qq z ^ n‖ := by
  have hsum : Summable (fun n : ℕ => C * (((n : ℝ) + 1) ^ k * ‖qq z‖ ^ n)) := by
    simpa using (summable_shift 1 k (norm_qq_pos z) hz).mul_left C
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hsum
  rw [norm_mul, norm_pow]
  calc ‖a n‖ * ‖qq z‖ ^ n ≤ (C * ((n : ℝ) + 1) ^ k) * ‖qq z‖ ^ n :=
        mul_le_mul_of_nonneg_right (hb n) (by positivity)
    _ = C * (((n : ℝ) + 1) ^ k * ‖qq z‖ ^ n) := by ring

theorem summable_qSeries {a : ℕ → ℂ} {C : ℝ} {k : ℕ} (hb : PolyBound a C k) {z : ℂ}
    (hz : ‖qq z‖ < 1) : Summable fun n : ℕ => a n * qq z ^ n :=
  Summable.of_norm (summable_norm_qSeries hb hz)

/-- The tail of a `q`-series from the quadratic term on is `O(q²)`, with an explicit
constant that does not depend on the point. -/
theorem norm_tail_le {a : ℕ → ℂ} {C : ℝ} {k : ℕ} (hb : PolyBound a C k) {z : ℂ}
    (hz : ‖qq z‖ ≤ 1 / 2) :
    ‖∑' n : ℕ, a (n + 2) * qq z ^ (n + 2)‖ ≤ C * tailConst k * ‖qq z‖ ^ 2 := by
  have hC : 0 ≤ C := hb.nonneg
  have hz0 : 0 < ‖qq z‖ := norm_qq_pos z
  set r := ‖qq z‖ with hr
  have hlt : r < 1 := lt_of_le_of_lt hz (by norm_num)
  have hns : Summable fun n : ℕ => ‖a (n + 2) * qq z ^ (n + 2)‖ :=
    (summable_nat_add_iff 2).2 (summable_norm_qSeries hb hlt)
  have hK := summable_tailConst k
  calc ‖∑' n : ℕ, a (n + 2) * qq z ^ (n + 2)‖
      ≤ ∑' n : ℕ, ‖a (n + 2) * qq z ^ (n + 2)‖ := norm_tsum_le_tsum_norm hns
    _ ≤ ∑' n : ℕ, (C * (((n : ℝ) + 3) ^ k * (1 / 2 : ℝ) ^ n)) * r ^ 2 := by
        refine Summable.tsum_le_tsum (fun n => ?_) hns ((hK.mul_left C).mul_right (r ^ 2))
        rw [norm_mul, norm_pow, ← hr]
        have h1 : ‖a (n + 2)‖ ≤ C * (((n : ℝ) + 3) ^ k) := by
          have h := hb (n + 2)
          push_cast at h
          have e : ((n : ℝ) + 2 + 1) = (n : ℝ) + 3 := by ring
          rwa [e] at h
        have h2 : r ^ (n + 2) = r ^ n * r ^ 2 := by ring
        have h3 : r ^ n ≤ (1 / 2 : ℝ) ^ n := pow_le_pow_left₀ hz0.le hz n
        have hCk : (0 : ℝ) ≤ C * (((n : ℝ) + 3) ^ k) := by positivity
        rw [h2]
        calc ‖a (n + 2)‖ * (r ^ n * r ^ 2)
            ≤ (C * (((n : ℝ) + 3) ^ k)) * ((1 / 2 : ℝ) ^ n * r ^ 2) :=
              mul_le_mul h1 (mul_le_mul_of_nonneg_right h3 (by positivity)) (by positivity) hCk
          _ = (C * (((n : ℝ) + 3) ^ k * (1 / 2 : ℝ) ^ n)) * r ^ 2 := by ring
    _ = C * tailConst k * r ^ 2 := by
        rw [tsum_mul_right, tsum_mul_left]; rfl

/-- **The heart of the matter.**  A normalised `q`-series is its leading term `q` up to
`O(q²)`. -/
theorem norm_qSeries_sub_qq {a : ℕ → ℂ} {C : ℝ} {k : ℕ} (ha : Normalized a C k) {z : ℂ}
    (hz : ‖qq z‖ ≤ 1 / 2) : ‖qSeries a z - qq z‖ ≤ C * tailConst k * ‖qq z‖ ^ 2 := by
  have hlt : ‖qq z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
  have hsum := summable_qSeries ha.bound hlt
  have hsplit := hsum.sum_add_tsum_nat_add (k := 2)
  have hhead : (∑ i ∈ Finset.range 2, a i * qq z ^ i) = qq z := by
    simp [Finset.sum_range_succ, ha.zero, ha.one]
  have : qSeries a z - qq z = ∑' n : ℕ, a (n + 2) * qq z ^ (n + 2) := by
    rw [qSeries, ← hsplit, hhead]; ring
  rw [this]
  exact norm_tail_le ha.bound hz

/-- The same estimate for a hauptmodul: away from the pole the regular part is bounded. -/
theorem norm_hauptSeries_sub_inv {c : ℕ → ℂ} {C : ℝ} {k : ℕ} (hb : PolyBound c C k) {z : ℂ}
    (hz : ‖qq z‖ ≤ 1 / 2) : ‖hauptSeries c z - (qq z)⁻¹‖ ≤ C * tailConst k := by
  have hC : 0 ≤ C := hb.nonneg
  have hz0 : 0 < ‖qq z‖ := norm_qq_pos z
  have hlt : ‖qq z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
  have hns := summable_norm_qSeries hb hlt
  have hK := summable_tailConst k
  have hstep : ‖∑' n : ℕ, c n * qq z ^ n‖ ≤ C * tailConst k := by
    calc ‖∑' n : ℕ, c n * qq z ^ n‖ ≤ ∑' n : ℕ, ‖c n * qq z ^ n‖ := norm_tsum_le_tsum_norm hns
      _ ≤ ∑' n : ℕ, C * (((n : ℝ) + 3) ^ k * (1 / 2 : ℝ) ^ n) := by
          refine Summable.tsum_le_tsum (fun n => ?_) hns (hK.mul_left C)
          rw [norm_mul, norm_pow]
          have h1 : ‖c n‖ ≤ C * (((n : ℝ) + 3) ^ k) := by
            refine le_trans (hb n) ?_
            have : ((n : ℝ) + 1) ^ k ≤ ((n : ℝ) + 3) ^ k := by
              refine pow_le_pow_left₀ (by positivity) (by linarith) k
            nlinarith [this]
          have h3 : ‖qq z‖ ^ n ≤ (1 / 2 : ℝ) ^ n := pow_le_pow_left₀ hz0.le hz n
          have hCk : (0 : ℝ) ≤ C * (((n : ℝ) + 3) ^ k) := by positivity
          calc ‖c n‖ * ‖qq z‖ ^ n ≤ (C * (((n : ℝ) + 3) ^ k)) * (1 / 2 : ℝ) ^ n :=
                mul_le_mul h1 h3 (by positivity) hCk
            _ = C * (((n : ℝ) + 3) ^ k * (1 / 2 : ℝ) ^ n) := by ring
      _ = C * tailConst k := by rw [tsum_mul_left]; rfl
  simpa [hauptSeries] using hstep

/-! ### The reading is a function of the height alone -/

theorem qSeries_norm_le {a : ℕ → ℂ} {C : ℝ} {k : ℕ} (ha : Normalized a C k) {z : ℂ}
    (hz : ‖qq z‖ ≤ 1 / 2) :
    ‖qSeries a z‖ ≤ ‖qq z‖ * (1 + C * tailConst k * ‖qq z‖) := by
  have h := norm_qSeries_sub_qq ha hz
  have h2 : ‖qSeries a z‖ ≤ ‖qq z‖ + ‖qSeries a z - qq z‖ := by
    calc ‖qSeries a z‖ = ‖qq z + (qSeries a z - qq z)‖ := by ring_nf
      _ ≤ ‖qq z‖ + ‖qSeries a z - qq z‖ := norm_add_le _ _
  nlinarith [h, h2, sq_nonneg ‖qq z‖]

theorem qSeries_norm_ge {a : ℕ → ℂ} {C : ℝ} {k : ℕ} (ha : Normalized a C k) {z : ℂ}
    (hz : ‖qq z‖ ≤ 1 / 2) :
    ‖qq z‖ * (1 - C * tailConst k * ‖qq z‖) ≤ ‖qSeries a z‖ := by
  have h := norm_qSeries_sub_qq ha hz
  have h2 : ‖qq z‖ - ‖qSeries a z - qq z‖ ≤ ‖qSeries a z‖ := by
    have := norm_sub_norm_le (qq z) (qSeries a z)
    have e : ‖qq z - qSeries a z‖ = ‖qSeries a z - qq z‖ := norm_sub_rev _ _
    linarith [this, e.le, e.ge]
  nlinarith [h, h2]

theorem hauptSeries_norm_le {c : ℕ → ℂ} {C : ℝ} {k : ℕ} (hb : PolyBound c C k) {z : ℂ}
    (hz : ‖qq z‖ ≤ 1 / 2) :
    ‖hauptSeries c z‖ ≤ ‖qq z‖⁻¹ + C * tailConst k := by
  have h := norm_hauptSeries_sub_inv hb hz
  have e : ‖(qq z)⁻¹‖ = ‖qq z‖⁻¹ := by rw [norm_inv]
  calc ‖hauptSeries c z‖ = ‖(qq z)⁻¹ + (hauptSeries c z - (qq z)⁻¹)‖ := by ring_nf
    _ ≤ ‖(qq z)⁻¹‖ + ‖hauptSeries c z - (qq z)⁻¹‖ := norm_add_le _ _
    _ ≤ ‖qq z‖⁻¹ + C * tailConst k := by rw [e]; linarith

theorem hauptSeries_norm_ge {c : ℕ → ℂ} {C : ℝ} {k : ℕ} (hb : PolyBound c C k) {z : ℂ}
    (hz : ‖qq z‖ ≤ 1 / 2) :
    ‖qq z‖⁻¹ - C * tailConst k ≤ ‖hauptSeries c z‖ := by
  have h := norm_hauptSeries_sub_inv hb hz
  have e : ‖(qq z)⁻¹‖ = ‖qq z‖⁻¹ := by rw [norm_inv]
  have h2 := norm_sub_norm_le ((qq z)⁻¹) (hauptSeries c z)
  have e2 : ‖(qq z)⁻¹ - hauptSeries c z‖ = ‖hauptSeries c z - (qq z)⁻¹‖ := norm_sub_rev _ _
  rw [e] at h2
  linarith [h2, e2.le, e2.ge]

/-- The height at which the leading term takes over, for a coefficient bound `C, k` and a
separation `δ`: `qHeight` is chosen so that `e^{-2π·qHeight}` is at most `1/2` and small
enough that the error terms cannot reverse a comparison across a gap of `δ`. -/
noncomputable def qHeight (C : ℝ) (k : ℕ) (δ : ℝ) : ℝ :=
  -(Real.log (min (1 / 2) ((1 - Real.exp (-(2 * Real.pi * δ))) *
      Real.exp (-(2 * Real.pi * δ)) / (2 * (C * tailConst k + 1))))) / (2 * Real.pi)

private theorem exp_le_of_height {C : ℝ} {k : ℕ} {δ : ℝ} {y : ℝ}
    (hy : qHeight C k δ ≤ y) (hδ : 0 < δ) (hC : 0 ≤ C) :
    Real.exp (-(2 * Real.pi * y)) ≤ min (1 / 2) ((1 - Real.exp (-(2 * Real.pi * δ))) *
      Real.exp (-(2 * Real.pi * δ)) / (2 * (C * tailConst k + 1))) := by
  set θ := Real.exp (-(2 * Real.pi * δ)) with hθ
  have hθ0 : 0 < θ := Real.exp_pos _
  have hθ1 : θ < 1 := by
    rw [hθ, Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  set ρ := min (1 / 2) ((1 - θ) * θ / (2 * (C * tailConst k + 1))) with hρ
  have hK : 0 ≤ tailConst k := tailConst_nonneg k
  have hρ0 : 0 < ρ := by
    refine lt_min (by norm_num) ?_
    have : (0:ℝ) < 2 * (C * tailConst k + 1) := by
      have : 0 ≤ C * tailConst k := mul_nonneg hC (tailConst_nonneg k)
      linarith
    exact div_pos (mul_pos (sub_pos.2 hθ1) hθ0) this
  have hle : Real.exp (-(2 * Real.pi * y)) ≤ Real.exp (-(2 * Real.pi * qHeight C k δ)) :=
    Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
  refine le_trans hle (le_of_eq ?_)
  have hlog : -(2 * Real.pi * qHeight C k δ) = Real.log ρ := by
    rw [qHeight, ← hθ, ← hρ]
    field_simp
  rw [hlog, Real.exp_log hρ0]

/-- The arithmetic behind the cusp form comparison: if the smaller nome is at most `θ`
times the larger and the error term `B·r` is below `(1-θ)/(1+θ)`, the comparison of the
leading terms survives the errors. -/
private theorem cusp_arith {B θ rz rw : ℝ} (hB0 : 0 ≤ B) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hrz0 : 0 < rz) (hrw0 : 0 < rw) (hrz_le : rz ≤ θ * rw)
    (hBrw : B * rw < (1 - θ) / (1 + θ)) : rz * (1 + B * rz) < rw * (1 - B * rw) := by
  rw [lt_div_iff₀ (by positivity)] at hBrw
  have hrzw : rz ≤ rw := by nlinarith
  have step1 : rz * (1 + B * rz) ≤ (θ * rw) * (1 + B * rw) :=
    mul_le_mul hrz_le (by nlinarith) (by positivity) (by positivity)
  have hbr : (θ - 1) + B * rw * (1 + θ) < 0 := by linarith
  have step2 := mul_lt_mul_of_pos_left hbr hrw0
  nlinarith [step1, step2]

/-- The same for a hauptmodul, where the pole `1/q` dominates a bounded error. -/
private theorem haupt_arith {B θ rz rw : ℝ} (hB0 : 0 ≤ B) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hrz0 : 0 < rz) (hrw0 : 0 < rw) (hrz_le : rz ≤ θ * rw)
    (hsmall : rw ≤ (1 - θ) * θ / (2 * (B + 1))) : rw⁻¹ + B < rz⁻¹ - B := by
  have h1θ : 0 < 1 - θ := by linarith
  have hinv : (θ * rw)⁻¹ ≤ rz⁻¹ := inv_anti₀ hrz0 hrz_le
  have hexp : (θ * rw)⁻¹ = θ⁻¹ * rw⁻¹ := by rw [mul_inv]
  have hkey : rw * (2 * (B + 1)) ≤ (1 - θ) * θ := by
    rw [le_div_iff₀ (by positivity)] at hsmall; linarith
  have hv : 2 * (B + 1) ≤ (1 - θ) * θ * rw⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hkey (le_of_lt (inv_pos.2 hrw0))
    rw [mul_comm rw (2 * (B + 1)), mul_assoc] at h
    rw [mul_inv_cancel₀ (ne_of_gt hrw0), mul_one] at h
    linarith
  have hθinv : θ⁻¹ - 1 = (1 - θ) / θ := by field_simp
  have hd : (1 - θ) * rw⁻¹ ≥ 2 * (B + 1) / θ := by
    rw [ge_iff_le, div_le_iff₀ hθ0]
    nlinarith [hv]
  have hstep : (1 - θ) / θ * rw⁻¹ ≥ 2 * (B + 1) / θ ^ 2 := by
    rw [ge_iff_le, div_le_iff₀ (by positivity)]
    have e : (1 - θ) / θ * rw⁻¹ * θ ^ 2 = ((1 - θ) * rw⁻¹) * θ := by field_simp
    rw [e]
    nlinarith [hd, hθ0]
  have hsq : θ ^ 2 ≤ 1 := by nlinarith
  have hθsq : 2 * (B + 1) / θ ^ 2 ≥ 2 * (B + 1) := by
    rw [ge_iff_le, le_div_iff₀ (by positivity)]
    nlinarith [hsq, hB0]
  have hfinal : θ⁻¹ * rw⁻¹ - rw⁻¹ ≥ 2 * (B + 1) := by
    have e2 : θ⁻¹ * rw⁻¹ - rw⁻¹ = (θ⁻¹ - 1) * rw⁻¹ := by ring
    rw [e2, hθinv]
    linarith [hstep, hθsq]
  have hlast : θ⁻¹ * rw⁻¹ ≤ rz⁻¹ := by rw [← hexp]; exact hinv
  linarith

/-- The two nomes across a gap of `δ`, and the smallness of the lower one. -/
private theorem nome_facts {C : ℝ} {k : ℕ} {δ : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) {z w : ℂ}
    (hw : qHeight C k δ ≤ w.im) (hzw : w.im + δ ≤ z.im) :
    ‖qq w‖ ≤ 1 / 2 ∧ ‖qq w‖ ≤ (1 - Real.exp (-(2 * Real.pi * δ))) *
        Real.exp (-(2 * Real.pi * δ)) / (2 * (C * tailConst k + 1)) ∧
      ‖qq z‖ ≤ Real.exp (-(2 * Real.pi * δ)) * ‖qq w‖ := by
  have hbound := exp_le_of_height (C := C) (k := k) hw hδ hC
  have hrw_eq : ‖qq w‖ = Real.exp (-(2 * Real.pi * w.im)) := norm_qq w
  have hrz_eq : ‖qq z‖ = Real.exp (-(2 * Real.pi * z.im)) := norm_qq z
  refine ⟨by rw [hrw_eq]; exact le_trans hbound (min_le_left _ _),
    by rw [hrw_eq]; exact le_trans hbound (min_le_right _ _), ?_⟩
  rw [hrz_eq, hrw_eq, ← Real.exp_add]
  exact Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])

/-- **A cusp form reads by height.**  Given a gap `δ > 0`, above the height
`qHeight C k δ` *every* normalised series with the coefficient bound `C, k` is strictly
decreasing in `Im z`: if `z` sits at least `δ` above `w`, its reading is strictly smaller. -/
theorem qSeries_norm_lt_of_height {a : ℕ → ℂ} {C : ℝ} {k : ℕ} (ha : Normalized a C k)
    {δ : ℝ} (hδ : 0 < δ) {z w : ℂ} (hw : qHeight C k δ ≤ w.im) (hzw : w.im + δ ≤ z.im) :
    ‖qSeries a z‖ < ‖qSeries a w‖ := by
  have hC : 0 ≤ C := ha.bound.nonneg
  have hK : 0 ≤ tailConst k := tailConst_nonneg k
  have hB0 : 0 ≤ C * tailConst k := by positivity
  have hθ0 : 0 < Real.exp (-(2 * Real.pi * δ)) := Real.exp_pos _
  have hθ1 : Real.exp (-(2 * Real.pi * δ)) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  obtain ⟨hhalf, hsmall, hratio⟩ := nome_facts (C := C) (k := k) hδ hC hw hzw
  have hrw0 : 0 < ‖qq w‖ := norm_qq_pos w
  have hrz0 : 0 < ‖qq z‖ := norm_qq_pos z
  have hrz_half : ‖qq z‖ ≤ 1 / 2 := by nlinarith
  have hBrw : C * tailConst k * ‖qq w‖ <
      (1 - Real.exp (-(2 * Real.pi * δ))) / (1 + Real.exp (-(2 * Real.pi * δ))) := by
    set θ := Real.exp (-(2 * Real.pi * δ))
    set B := C * tailConst k
    have h3 : B * ‖qq w‖ ≤ B * ((1 - θ) * θ / (2 * (B + 1))) :=
      mul_le_mul_of_nonneg_left hsmall hB0
    have h4 : B * ((1 - θ) * θ / (2 * (B + 1))) < (1 - θ) / (1 + θ) := by
      have e : B * ((1 - θ) * θ / (2 * (B + 1))) = (B * ((1 - θ) * θ)) / (2 * (B + 1)) := by
        ring
      rw [e, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos (sub_pos.2 hθ1) hθ0, sq_nonneg θ, mul_nonneg hB0 (sub_pos.2 hθ1).le]
    linarith
  have hup := qSeries_norm_le ha (z := z) hrz_half
  have hlo := qSeries_norm_ge ha (z := w) hhalf
  have key := cusp_arith hB0 hθ0 hθ1 hrz0 hrw0 hratio hBrw
  linarith

/-- **A hauptmodul reads by height too**, with the order reversed: higher up the reading
is larger, because the pole at the cusp dominates. -/
theorem hauptSeries_norm_lt_of_height {c : ℕ → ℂ} {C : ℝ} {k : ℕ} (hb : PolyBound c C k)
    {δ : ℝ} (hδ : 0 < δ) {z w : ℂ} (hw : qHeight C k δ ≤ w.im) (hzw : w.im + δ ≤ z.im) :
    ‖hauptSeries c w‖ < ‖hauptSeries c z‖ := by
  have hC : 0 ≤ C := hb.nonneg
  have hK : 0 ≤ tailConst k := tailConst_nonneg k
  have hB0 : 0 ≤ C * tailConst k := by positivity
  have hθ0 : 0 < Real.exp (-(2 * Real.pi * δ)) := Real.exp_pos _
  have hθ1 : Real.exp (-(2 * Real.pi * δ)) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  obtain ⟨hhalf, hsmall, hratio⟩ := nome_facts (C := C) (k := k) hδ hC hw hzw
  have hrw0 : 0 < ‖qq w‖ := norm_qq_pos w
  have hrz0 : 0 < ‖qq z‖ := norm_qq_pos z
  have hrz_half : ‖qq z‖ ≤ 1 / 2 := by nlinarith
  have hup := hauptSeries_norm_le hb (z := w) hhalf
  have hlo := hauptSeries_norm_ge hb (z := z) hrz_half
  have key := haupt_arith hB0 hθ0 hθ1 hrz0 hrw0 hratio hsmall
  linarith


/-! ### The palettes -/

theorem paletteRank_congr {f g : ℂ → ℂ} {S : Finset ℂ}
    (h : ∀ u ∈ S, ∀ v ∈ S, (‖f u‖ < ‖f v‖ ↔ ‖g u‖ < ‖g v‖)) {z : ℂ} (hz : z ∈ S) :
    paletteRank f S z = paletteRank g S z := by
  unfold paletteRank
  congr 1
  refine Finset.filter_congr fun w hw => ?_
  simpa using h w hw z hz

/-- **Universality of the palette.**  Above the height `qHeight C k δ`, any two normalised
`q`-series paint any `δ`-separated sample of points with exactly the same ranks: the two
plates are the same picture. -/
theorem paletteRank_eq_of_normalized {a b : ℕ → ℂ} {C : ℝ} {k : ℕ}
    (ha : Normalized a C k) (hbn : Normalized b C k) {δ : ℝ} (hδ : 0 < δ) {S : Finset ℂ}
    (hS : ∀ z ∈ S, qHeight C k δ ≤ z.im)
    (hsep : ∀ z ∈ S, ∀ w ∈ S, z ≠ w → δ ≤ |z.im - w.im|) {z : ℂ} (hz : z ∈ S) :
    paletteRank (qSeries a) S z = paletteRank (qSeries b) S z := by
  refine paletteRank_congr (fun u hu v hv => ?_) hz
  rcases eq_or_ne u v with rfl | hne
  · simp
  · rcases le_or_gt (v.im + δ) u.im with h | h
    · have h1 : ‖qSeries a u‖ < ‖qSeries a v‖ :=
        qSeries_norm_lt_of_height ha hδ (hS v hv) h
      have h2 : ‖qSeries b u‖ < ‖qSeries b v‖ :=
        qSeries_norm_lt_of_height hbn hδ (hS v hv) h
      simp [h1, h2]
    · have hgap := hsep u hu v hv hne
      have h' : u.im + δ ≤ v.im := by
        rcases abs_cases (u.im - v.im) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hgap <;> linarith
      have h1 : ‖qSeries a v‖ < ‖qSeries a u‖ :=
        qSeries_norm_lt_of_height ha hδ (hS u hu) h'
      have h2 : ‖qSeries b v‖ < ‖qSeries b u‖ :=
        qSeries_norm_lt_of_height hbn hδ (hS u hu) h'
      constructor
      · intro hc; exact absurd hc (not_lt.2 h1.le)
      · intro hc; exact absurd hc (not_lt.2 h2.le)

/-- **The `T` series all look the same.**  Any two hauptmodul-shaped series with a common
coefficient bound paint a separated sample with exactly the same ranks. -/
theorem paletteRank_eq_of_haupt {c d : ℕ → ℂ} {C : ℝ} {k : ℕ}
    (hc : PolyBound c C k) (hd : PolyBound d C k) {δ : ℝ} (hδ : 0 < δ) {S : Finset ℂ}
    (hS : ∀ z ∈ S, qHeight C k δ ≤ z.im)
    (hsep : ∀ z ∈ S, ∀ w ∈ S, z ≠ w → δ ≤ |z.im - w.im|) {z : ℂ} (hz : z ∈ S) :
    paletteRank (hauptSeries c) S z = paletteRank (hauptSeries d) S z := by
  refine paletteRank_congr (fun u hu v hv => ?_) hz
  rcases eq_or_ne u v with rfl | hne
  · simp
  · rcases le_or_gt (u.im + δ) v.im with h | h
    · have h1 : ‖hauptSeries c u‖ < ‖hauptSeries c v‖ :=
        hauptSeries_norm_lt_of_height hc hδ (hS u hu) h
      have h2 : ‖hauptSeries d u‖ < ‖hauptSeries d v‖ :=
        hauptSeries_norm_lt_of_height hd hδ (hS u hu) h
      simp [h1, h2]
    · have hgap := hsep u hu v hv hne
      have h' : v.im + δ ≤ u.im := by
        rcases abs_cases (u.im - v.im) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hgap <;> linarith
      have h1 : ‖hauptSeries c v‖ < ‖hauptSeries c u‖ :=
        hauptSeries_norm_lt_of_height hc hδ (hS v hv) h'
      have h2 : ‖hauptSeries d v‖ < ‖hauptSeries d u‖ :=
        hauptSeries_norm_lt_of_height hd hδ (hS v hv) h'
      constructor
      · intro hcc; exact absurd hcc (not_lt.2 h1.le)
      · intro hcc; exact absurd hcc (not_lt.2 h2.le)

/-- **A hauptmodul plate is the negative of a cusp form plate.**  High enough up, across a
gap of `δ`, the two orders are exactly opposite. -/
theorem haupt_order_reverse {a c : ℕ → ℂ} {C : ℝ} {k : ℕ} (ha : Normalized a C k)
    (hc : PolyBound c C k) {δ : ℝ} (hδ : 0 < δ) {z w : ℂ}
    (hz : qHeight C k δ ≤ z.im) (hw : qHeight C k δ ≤ w.im) (hsep : δ ≤ |z.im - w.im|) :
    (‖qSeries a z‖ < ‖qSeries a w‖ ↔ ‖hauptSeries c w‖ < ‖hauptSeries c z‖) := by
  rcases le_or_gt (w.im + δ) z.im with h | h
  · have h1 : ‖qSeries a z‖ < ‖qSeries a w‖ := qSeries_norm_lt_of_height ha hδ hw h
    have h2 : ‖hauptSeries c w‖ < ‖hauptSeries c z‖ :=
      hauptSeries_norm_lt_of_height hc hδ hw h
    simp [h1, h2]
  · have h' : z.im + δ ≤ w.im := by
      rcases abs_cases (z.im - w.im) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hsep <;> linarith
    have h1 : ‖qSeries a w‖ < ‖qSeries a z‖ := qSeries_norm_lt_of_height ha hδ hz h'
    have h2 : ‖hauptSeries c z‖ < ‖hauptSeries c w‖ :=
      hauptSeries_norm_lt_of_height hc hδ hz h'
    constructor
    · intro hcc; exact absurd hcc (not_lt.2 h1.le)
    · intro hcc; exact absurd hcc (not_lt.2 h2.le)

end PaletteUniversality
