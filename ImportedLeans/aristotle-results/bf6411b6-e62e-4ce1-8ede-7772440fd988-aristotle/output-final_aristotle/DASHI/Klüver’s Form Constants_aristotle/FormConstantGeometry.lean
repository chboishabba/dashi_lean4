import Mathlib

/-!
# Klüver form constants — the geometric core

This file formalises the genuine, self-contained *geometric* claims in the
source document about Klüver's visual form constants and the cortical
pattern-formation account (Ermentrout–Cowan / Bressloff, Schwartz log-polar
map, hexagonal "M6" instability).

* **Log-polar spirals.** In the retino-cortical (Schwartz) map `(u, v) = (log r, θ)`
  a cortical plane wave `cos(2π(f·u + m·v))` pulls back to
  `cos(2π(f·log r + m·θ))`. Its phase fronts `f·log r + m·θ = c` are exactly the
  logarithmic spirals `r = exp((c - m·θ)/f)` (`logpolar_spiral`,
  `logpolar_is_log_spiral`).  The pure ring (`m = 0`, lattice/tunnel) and pure
  ray cases are recovered as `logpolar_ring`.

* **Hexagonal "M6" instability.** The marginally unstable Fourier modes of an
  isotropic pattern former lie on a circle `|k| = k₀`; the lowest-energy
  resonant pattern uses six wavevectors `k_j = k₀·(cos(jπ/3), sin(jπ/3))`,
  `j = 0,…,5`.  These all lie on the circle (`hexWave_norm`), come in antipodal
  pairs `k_j + k_{j+3} = 0` (`hexWave_antipodal`), and satisfy the triadic
  resonance condition `k_i + k_j + k_l = 0` (`hexWave_resonance`) that selects
  the hexagonal/honeycomb form constant.
-/

namespace FormConstantGeometry

open Real

/-! ## Log-polar spirals -/

/-
**Log-polar phase fronts are logarithmic spirals.**  With `f ≠ 0` and radius
`r > 0`, the level set of the pulled-back cortical plane wave's phase,
`f·log r + m·θ = c`, is equivalent to `r = exp((c - m·θ)/f)`.
-/
theorem logpolar_spiral (f m c θ r : ℝ) (hf : f ≠ 0) (hr : 0 < r) :
    f * Real.log r + m * θ = c ↔ r = Real.exp ((c - m * θ) / f) := by
      constructor <;> intro h <;> simp_all +decide [ mul_comm f, Real.exp_neg, Real.exp_log hr, sub_eq_iff_eq_add ];
      rw [ ← h, add_sub_cancel_right, mul_div_cancel_right₀ _ hf, Real.exp_log hr ]

/-
Restated as an explicit logarithmic spiral `r = exp(α - β·θ)` with
`α = c/f`, `β = m/f`.
-/
theorem logpolar_is_log_spiral (f m c θ r : ℝ) (hf : f ≠ 0) (hr : 0 < r) :
    f * Real.log r + m * θ = c ↔ r = Real.exp (c / f - (m / f) * θ) := by
      convert logpolar_spiral f m c θ r hf hr using 1 ; ring

/-
**The `m = 0` case is a concentric ring** (lattice/tunnel form constant):
the phase front is the circle `r = exp(c/f)`, independent of the angle `θ`.
-/
theorem logpolar_ring (f c θ r : ℝ) (hf : f ≠ 0) (hr : 0 < r) :
    f * Real.log r + 0 * θ = c ↔ r = Real.exp (c / f) := by
      convert logpolar_spiral f 0 c θ r hf hr using 1;
      norm_num

/-! ## Hexagonal "M6" instability -/

/-- The six marginal wavevectors of the hexagonal instability, on the circle of
radius `k₀`: `k_j = k₀·(cos(jπ/3), sin(jπ/3))`. -/
noncomputable def hexWave (k0 : ℝ) (j : Fin 6) : ℝ × ℝ :=
  (k0 * Real.cos ((j : ℝ) * Real.pi / 3), k0 * Real.sin ((j : ℝ) * Real.pi / 3))

/-
**All six wavevectors lie on the circle `|k| = k₀`.**
-/
theorem hexWave_norm (k0 : ℝ) (j : Fin 6) :
    (hexWave k0 j).1 ^ 2 + (hexWave k0 j).2 ^ 2 = k0 ^ 2 := by
      unfold hexWave; ring_nf; norm_num [ Real.sin_sq, Real.cos_sq ] ; ring;

/-
**Antipodal pairs.** Opposite wavevectors cancel: `k_j + k_{j+3} = 0`.
-/
theorem hexWave_antipodal (k0 : ℝ) :
    (hexWave k0 0).1 + (hexWave k0 3).1 = 0 ∧
    (hexWave k0 0).2 + (hexWave k0 3).2 = 0 ∧
    (hexWave k0 1).1 + (hexWave k0 4).1 = 0 ∧
    (hexWave k0 1).2 + (hexWave k0 4).2 = 0 ∧
    (hexWave k0 2).1 + (hexWave k0 5).1 = 0 ∧
    (hexWave k0 2).2 + (hexWave k0 5).2 = 0 := by
      unfold hexWave; norm_num [ Real.cos_add, Real.sin_add ] ; ring;
      norm_num [ ( by ring : Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 ), ( by ring : Real.pi * ( 4 / 3 ) = Real.pi + Real.pi / 3 ), ( by ring : Real.pi * ( 5 / 3 ) = 2 * Real.pi - Real.pi / 3 ), Real.cos_add, Real.sin_add ] ; ring ;

/-
**Triadic resonance `k_i + k_j + k_l = 0`.** The alternating triple
`k₀ + k₂ + k₄` (mutual angle `2π/3`) sums to zero — the resonance condition that
selects the hexagonal/honeycomb form constant.
-/
theorem hexWave_resonance (k0 : ℝ) :
    (hexWave k0 0).1 + (hexWave k0 2).1 + (hexWave k0 4).1 = 0 ∧
    (hexWave k0 0).2 + (hexWave k0 2).2 + (hexWave k0 4).2 = 0 := by
      unfold hexWave; norm_num [ ( by ring : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 ), ( by ring : 4 * Real.pi / 3 = Real.pi + Real.pi / 3 ), Real.cos_add, Real.sin_add, Real.cos_sub, Real.sin_sub ] ; ring;

end FormConstantGeometry