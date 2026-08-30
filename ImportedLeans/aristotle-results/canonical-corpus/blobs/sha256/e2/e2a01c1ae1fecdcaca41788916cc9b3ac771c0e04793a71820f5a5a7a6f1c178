/-
# From strict `TP₂` to a strict moment cross-product

`HyperbolicTP2.lean` proves that the kernels `sinh (y*u)` and `cosh (y*u)` are
strictly `TP₂` on the positive quadrant.  This module carries that pointwise
order property through a positive, nondegenerate integral, and thereby closes
the *continuum* moment-determinant obligation of the zero-side chain, with a
strict sign rather than mere nonvanishing.

The generic owner is `strict_moment_cross_pos`:

  `strict TP₂ kernel pair` + `nonnegative weight, positive on a subinterval`
  + `strictly increasing score`  ⟹  strict moment cross-product inequality

  `(∫ w·s·k₁) · (∫ w·k₂)  <  (∫ w·k₁) · (∫ w·s·k₂)`.

The proof is the symmetrized double-integral identity

  `2·[(∫ w k₁)(∫ w s k₂) − (∫ w s k₁)(∫ w k₂)]`
    `= ∫∫ w(u) w(v) (s v − s u) (k₁ u k₂ v − k₁ v k₂ u) du dv`,

whose integrand is **pointwise nonnegative** (both factors change sign together
at `u = v`) and **strictly positive** on a rectangle inside the region where the
weight is bounded below.  Strictness therefore comes from
`integral_pos_iff_support_of_nonneg_ae` — no compactness argument and no
quantitative lower bound on the kernel minor is needed.

Two instantiations follow, for the taper moments used by the parity-minor
programme, where `φ` is the (nonnegative, bounded, measurable) taper:

* odd sector, `N k y = ∫₀ᴸ uᵏ φ(u) sinh (y u) du`:
  `oddMomentDeterminant_strictPos` : `N 3 a * N 1 p < N 1 a * N 3 p`, i.e.
  `Δ_odd = N 1 a * N 3 p − N 3 a * N 1 p > 0` for `0 < a < p`;
  `oddMomentDeterminant_strictNegative` is the same fact in the orientation
  `N 3 a * N 1 p − N 1 a * N 3 p < 0`.

* even sector, `M k y = ∫₀ᴸ uᵏ φ(u) cosh (y u) du`:
  `evenMomentDeterminant_strictNegative` : `M 2 a * M 0 p − M 0 a * M 2 p < 0`.

No `sorry`, no `axiom`, no numerical evidence.
-/

import Mathlib
import RiemannAnalytic.HyperbolicTP2

open MeasureTheory Set

namespace RiemannAnalytic
namespace StrictKernelMomentRatio

/-! ## A convenience integrability criterion -/

/-- A measurable function bounded on `(0, L]` is integrable there. -/
theorem integrable_restrict_Ioc_of_bounded {L C : ℝ} {f : ℝ → ℝ} (hf : Measurable f)
    (hb : ∀ u ∈ Ioc (0 : ℝ) L, |f u| ≤ C) :
    Integrable f (volume.restrict (Ioc (0 : ℝ) L)) := by
  have hfin : (volume (Ioc (0 : ℝ) L)) ≠ ⊤ := by simp [Real.volume_Ioc]
  refine Integrable.mono' (g := fun _ => C) ?_ hf.aestronglyMeasurable ?_
  · exact integrableOn_const (μ := volume) (s := Ioc (0 : ℝ) L) hfin (by simp)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    simpa [Real.norm_eq_abs] using hb u hu

/-! ## The generic strict moment cross-product theorem -/

/-- **Strict `TP₂` composition.**  If `k₁, k₂` form a strictly `TP₂` pair on the
positive axis, `s` is strictly increasing there, and the weight `w` is
nonnegative on `(0,L]` and bounded below by `m > 0` on a subinterval `(c,d)`,
then the weighted moment cross-product is strictly ordered. -/
theorem strict_moment_cross_pos {L : ℝ}
    {w s k1 k2 : ℝ → ℝ} {Cw Cs Ck : ℝ}
    (hw : Measurable w) (hsm : Measurable s) (hk1 : Measurable k1) (hk2 : Measurable k2)
    (hwb : ∀ u ∈ Ioc (0 : ℝ) L, |w u| ≤ Cw)
    (hsb : ∀ u ∈ Ioc (0 : ℝ) L, |s u| ≤ Cs)
    (hk1b : ∀ u ∈ Ioc (0 : ℝ) L, |k1 u| ≤ Ck)
    (hk2b : ∀ u ∈ Ioc (0 : ℝ) L, |k2 u| ≤ Ck)
    (hw0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ w u)
    (hsmono : ∀ u v : ℝ, 0 < u → u < v → s u < s v)
    (htp2 : ∀ u v : ℝ, 0 < u → u < v → k1 v * k2 u < k1 u * k2 v)
    {c d m : ℝ} (hc : 0 < c) (hcd : c < d) (hdL : d ≤ L) (hm : 0 < m)
    (hplateau : ∀ u ∈ Ioo c d, m ≤ w u) :
    (∫ u in Ioc (0 : ℝ) L, w u * s u * k1 u) * (∫ u in Ioc (0 : ℝ) L, w u * k2 u)
      < (∫ u in Ioc (0 : ℝ) L, w u * k1 u) * (∫ u in Ioc (0 : ℝ) L, w u * s u * k2 u) := by
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) L) with hν
  have hf1 : Integrable (fun u => w u * k1 u) ν :=
    integrable_restrict_Ioc_of_bounded (hw.mul hk1) (C := |Cw| * |Ck|) (by
      intro u hu
      rw [abs_mul]
      exact mul_le_mul ((hwb u hu).trans (le_abs_self _)) ((hk1b u hu).trans (le_abs_self _))
        (abs_nonneg _) (abs_nonneg _))
  have hg1 : Integrable (fun u => w u * k2 u) ν :=
    integrable_restrict_Ioc_of_bounded (hw.mul hk2) (C := |Cw| * |Ck|) (by
      intro u hu
      rw [abs_mul]
      exact mul_le_mul ((hwb u hu).trans (le_abs_self _)) ((hk2b u hu).trans (le_abs_self _))
        (abs_nonneg _) (abs_nonneg _))
  have hf2 : Integrable (fun u => w u * s u * k1 u) ν :=
    integrable_restrict_Ioc_of_bounded ((hw.mul hsm).mul hk1) (C := |Cw| * |Cs| * |Ck|) (by
      intro u hu
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul ((hwb u hu).trans (le_abs_self _))
        ((hsb u hu).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _))
        ((hk1b u hu).trans (le_abs_self _)) (abs_nonneg _) (by positivity))
  have hg2 : Integrable (fun u => w u * s u * k2 u) ν :=
    integrable_restrict_Ioc_of_bounded ((hw.mul hsm).mul hk2) (C := |Cw| * |Cs| * |Ck|) (by
      intro u hu
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul ((hwb u hu).trans (le_abs_self _))
        ((hsb u hu).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _))
        ((hk2b u hu).trans (le_abs_self _)) (abs_nonneg _) (by positivity))
  set H : ℝ × ℝ → ℝ := fun z =>
    (w z.1 * k1 z.1) * (w z.2 * s z.2 * k2 z.2) - (w z.1 * s z.1 * k1 z.1) * (w z.2 * k2 z.2)
    with hHdef
  have hH : Integrable H (ν.prod ν) := (hf1.mul_prod hg2).sub (hf2.mul_prod hg1)
  have hHswap : Integrable (fun z : ℝ × ℝ => H z.swap) (ν.prod ν) := hH.swap
  have hDH : (∫ u, (w u * k1 u) ∂ν) * (∫ u, (w u * s u * k2 u) ∂ν)
      - (∫ u, (w u * s u * k1 u) ∂ν) * (∫ u, (w u * k2 u) ∂ν) = ∫ z, H z ∂(ν.prod ν) := by
    rw [hHdef, integral_sub (hf1.mul_prod hg2) (hf2.mul_prod hg1),
      integral_prod_mul (μ := ν) (ν := ν) (fun u => w u * k1 u) (fun u => w u * s u * k2 u),
      integral_prod_mul (μ := ν) (ν := ν) (fun u => w u * s u * k1 u) (fun u => w u * k2 u)]
  have hswap : ∫ z, H z.swap ∂(ν.prod ν) = ∫ z, H z ∂(ν.prod ν) := integral_prod_swap H
  set F : ℝ × ℝ → ℝ := fun z => H z + H z.swap with hFdef
  have hFint : Integrable F (ν.prod ν) := hH.add hHswap
  have hFsum : ∫ z, F z ∂(ν.prod ν) = 2 * ∫ z, H z ∂(ν.prod ν) := by
    rw [hFdef, integral_add hH hHswap, hswap]; ring
  have hFeq : ∀ z : ℝ × ℝ, F z
      = w z.1 * w z.2 * (s z.2 - s z.1) * (k1 z.1 * k2 z.2 - k1 z.2 * k2 z.1) := by
    intro z; simp only [hFdef, hHdef, Prod.fst_swap, Prod.snd_swap]; ring
  have hFnn : ∀ u ∈ Ioc (0 : ℝ) L, ∀ v ∈ Ioc (0 : ℝ) L,
      0 ≤ w u * w v * (s v - s u) * (k1 u * k2 v - k1 v * k2 u) := by
    intro u hu v hv
    have hwu := hw0 u hu
    have hwv := hw0 v hv
    have key : w u * w v * (s v - s u) * (k1 u * k2 v - k1 v * k2 u)
        = (w u * w v) * ((s v - s u) * (k1 u * k2 v - k1 v * k2 u)) := by ring
    rw [key]
    rcases lt_trichotomy u v with h | h | h
    · exact mul_nonneg (mul_nonneg hwu hwv)
        (le_of_lt (mul_pos (by linarith [hsmono u v hu.1 h]) (by linarith [htp2 u v hu.1 h])))
    · subst h; simp
    · exact mul_nonneg (mul_nonneg hwu hwv)
        (le_of_lt (mul_pos_of_neg_of_neg (by linarith [hsmono v u hv.1 h])
          (by linarith [htp2 v u hv.1 h])))
  have hae : 0 ≤ᶠ[ae (ν.prod ν)] F := by
    rw [hν, Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with z hz
    rw [hFeq z]
    exact hFnn z.1 hz.1 z.2 hz.2
  have hpos : 0 < ∫ z, F z ∂(ν.prod ν) := by
    rw [integral_pos_iff_support_of_nonneg_ae hae hFint]
    set e : ℝ := (c + d) / 2 with he
    have hce : c < e := by rw [he]; linarith
    have hed : e < d := by rw [he]; linarith
    have hsub : (Ioo c e) ×ˢ (Ioo e d) ⊆ Function.support F := by
      rintro ⟨u, v⟩ ⟨hu, hv⟩
      simp only [Function.mem_support]
      rw [hFeq]
      have hu0 : 0 < u := hc.trans hu.1
      have huv : u < v := hu.2.trans hv.1
      have hwu : m ≤ w u := hplateau u ⟨hu.1, hu.2.trans hed⟩
      have hwv : m ≤ w v := hplateau v ⟨hce.trans hv.1, hv.2⟩
      have h1 : 0 < s v - s u := by linarith [hsmono u v hu0 huv]
      have h2 : 0 < k1 u * k2 v - k1 v * k2 u := by linarith [htp2 u v hu0 huv]
      exact ne_of_gt (mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) h1) h2)
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [Measure.prod_prod, hν, Measure.restrict_apply' measurableSet_Ioc,
      Measure.restrict_apply' measurableSet_Ioc,
      Set.inter_eq_self_of_subset_left
        (show Ioo c e ⊆ Ioc (0 : ℝ) L from fun x hx =>
          ⟨hc.trans hx.1, le_of_lt (lt_of_lt_of_le (hx.2.trans hed) hdL)⟩),
      Set.inter_eq_self_of_subset_left
        (show Ioo e d ⊆ Ioc (0 : ℝ) L from fun x hx =>
          ⟨lt_trans (hc.trans hce) hx.1, le_of_lt (lt_of_lt_of_le hx.2 hdL)⟩),
      Real.volume_Ioo, Real.volume_Ioo]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (by linarith)).ne'
      (ENNReal.ofReal_pos.2 (by linarith)).ne'
  rw [hFsum] at hpos
  linarith [hDH]

/-! ## The taper moments -/

/-- Odd taper moments `N k y = ∫₀ᴸ uᵏ φ(u) sinh (y u) du`. -/
noncomputable def oddMoment (L : ℝ) (φ : ℝ → ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  ∫ u in Ioc (0 : ℝ) L, u ^ k * φ u * Real.sinh (y * u)

/-- Even taper moments `M k y = ∫₀ᴸ uᵏ φ(u) cosh (y u) du`. -/
noncomputable def evenMoment (L : ℝ) (φ : ℝ → ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  ∫ u in Ioc (0 : ℝ) L, u ^ k * φ u * Real.cosh (y * u)

section Taper

variable {L : ℝ} {φ : ℝ → ℝ} {Cφ a p c d m : ℝ}

/-- **Continuum odd moment determinant, strict sign.**  For a nonnegative,
bounded, measurable taper that is bounded below on a subinterval `(c,d) ⊆ (0,L]`
and heights `0 < a < p`, `Δ_odd = N 1 a * N 3 p − N 3 a * N 1 p > 0`. -/
theorem oddMomentDeterminant_strictPos
    (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ)
    (hL : 0 < L) (ha : 0 < a) (hap : a < p)
    (hc : 0 < c) (hcd : c < d) (hdL : d ≤ L) (hm : 0 < m)
    (hplateau : ∀ u ∈ Ioo c d, m ≤ φ u) :
    oddMoment L φ 3 a * oddMoment L φ 1 p < oddMoment L φ 1 a * oddMoment L φ 3 p := by
  have hp : 0 < p := ha.trans hap
  have hsinh_bd : ∀ (y : ℝ), 0 < y → y ≤ p → ∀ u ∈ Ioc (0 : ℝ) L,
      |Real.sinh (y * u)| ≤ Real.sinh (p * L) := by
    intro y hy hyp u hu
    have h1 : 0 < y * u := mul_pos hy hu.1
    have h2 : y * u ≤ p * L :=
      le_trans (mul_le_mul_of_nonneg_left hu.2 hy.le) (mul_le_mul_of_nonneg_right hyp (hL.le))
    rw [abs_of_pos (Real.sinh_pos_iff.2 h1)]
    exact Real.sinh_le_sinh.2 h2
  have key := strict_moment_cross_pos (L := L) (w := fun u => u * φ u) (s := fun u => u ^ 2)
    (k1 := fun u => Real.sinh (a * u)) (k2 := fun u => Real.sinh (p * u))
    (Cw := L * |Cφ|) (Cs := L ^ 2) (Ck := Real.sinh (p * L))
    (measurable_id.mul hφmeas) (measurable_id.pow_const 2)
    (Real.measurable_sinh.comp (measurable_const.mul measurable_id))
    (Real.measurable_sinh.comp (measurable_const.mul measurable_id))
    (by
      intro u hu
      rw [abs_mul, abs_of_pos hu.1]
      exact mul_le_mul hu.2 ((hφb u hu).trans (le_abs_self _)) (abs_nonneg _) hL.le)
    (by
      intro u hu
      rw [abs_of_nonneg (by positivity)]
      nlinarith [hu.1, hu.2])
    (hsinh_bd a ha hap.le) (hsinh_bd p hp le_rfl)
    (fun u hu => mul_nonneg hu.1.le (hφ0 u hu))
    (fun u v hu huv => by nlinarith)
    (fun u v hu huv => by
      have h := HyperbolicTP2.sinh_strictTP2 ha hap hu huv
      calc Real.sinh (a * v) * Real.sinh (p * u)
          = Real.sinh (p * u) * Real.sinh (a * v) := mul_comm _ _
        _ < Real.sinh (p * v) * Real.sinh (a * u) := h
        _ = Real.sinh (a * u) * Real.sinh (p * v) := mul_comm _ _)
    hc hcd hdL (m := c * m)
    (mul_pos hc hm)
    (fun u hu => mul_le_mul (le_of_lt hu.1) (hplateau u hu) hm.le (hc.trans hu.1).le)
  have e1 : (fun u : ℝ => u * φ u * u ^ 2 * Real.sinh (a * u))
      = fun u : ℝ => u ^ 3 * φ u * Real.sinh (a * u) := by funext u; ring
  have e2 : (fun u : ℝ => u * φ u * Real.sinh (p * u))
      = fun u : ℝ => u ^ 1 * φ u * Real.sinh (p * u) := by funext u; ring
  have e3 : (fun u : ℝ => u * φ u * Real.sinh (a * u))
      = fun u : ℝ => u ^ 1 * φ u * Real.sinh (a * u) := by funext u; ring
  have e4 : (fun u : ℝ => u * φ u * u ^ 2 * Real.sinh (p * u))
      = fun u : ℝ => u ^ 3 * φ u * Real.sinh (p * u) := by funext u; ring
  rw [e1, e2, e3, e4] at key
  simp only [oddMoment]
  exact key

/-- The same fact in the orientation used by the parity-minor ledger:
`N 3 a * N 1 p − N 1 a * N 3 p < 0`. -/
theorem oddMomentDeterminant_strictNegative
    (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ)
    (hL : 0 < L) (ha : 0 < a) (hap : a < p)
    (hc : 0 < c) (hcd : c < d) (hdL : d ≤ L) (hm : 0 < m)
    (hplateau : ∀ u ∈ Ioo c d, m ≤ φ u) :
    oddMoment L φ 3 a * oddMoment L φ 1 p - oddMoment L φ 1 a * oddMoment L φ 3 p < 0 := by
  have := oddMomentDeterminant_strictPos hφmeas hφ0 hφb hL ha hap hc hcd hdL hm hplateau
  linarith

/-- **Continuum even moment determinant, strict sign.**
`M 2 a * M 0 p − M 0 a * M 2 p < 0` for `0 < a < p`. -/
theorem evenMomentDeterminant_strictNegative
    (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ)
    (hL : 0 < L) (ha : 0 < a) (hap : a < p)
    (hc : 0 < c) (hcd : c < d) (hdL : d ≤ L) (hm : 0 < m)
    (hplateau : ∀ u ∈ Ioo c d, m ≤ φ u) :
    evenMoment L φ 2 a * evenMoment L φ 0 p - evenMoment L φ 0 a * evenMoment L φ 2 p < 0 := by
  have hp : 0 < p := ha.trans hap
  have hcosh_bd : ∀ (y : ℝ), 0 < y → y ≤ p → ∀ u ∈ Ioc (0 : ℝ) L,
      |Real.cosh (y * u)| ≤ Real.cosh (p * L) := by
    intro y hy hyp u hu
    have h1 : 0 < y * u := mul_pos hy hu.1
    have h2 : y * u ≤ p * L :=
      le_trans (mul_le_mul_of_nonneg_left hu.2 hy.le) (mul_le_mul_of_nonneg_right hyp (hL.le))
    rw [abs_of_pos (Real.cosh_pos _)]
    exact Real.cosh_le_cosh.2 (by rw [abs_of_pos h1, abs_of_pos (by nlinarith)]; exact h2)
  have key := strict_moment_cross_pos (L := L) (w := φ) (s := fun u => u ^ 2)
    (k1 := fun u => Real.cosh (a * u)) (k2 := fun u => Real.cosh (p * u))
    (Cw := Cφ) (Cs := L ^ 2) (Ck := Real.cosh (p * L))
    hφmeas (measurable_id.pow_const 2)
    (Real.measurable_cosh.comp (measurable_const.mul measurable_id))
    (Real.measurable_cosh.comp (measurable_const.mul measurable_id))
    hφb
    (by
      intro u hu
      rw [abs_of_nonneg (by positivity)]
      nlinarith [hu.1, hu.2])
    (hcosh_bd a ha hap.le) (hcosh_bd p hp le_rfl)
    hφ0
    (fun u v hu huv => by nlinarith)
    (fun u v hu huv => by
      have h := HyperbolicTP2.cosh_strictTP2 ha hap hu huv
      calc Real.cosh (a * v) * Real.cosh (p * u)
          = Real.cosh (p * u) * Real.cosh (a * v) := mul_comm _ _
        _ < Real.cosh (p * v) * Real.cosh (a * u) := h
        _ = Real.cosh (a * u) * Real.cosh (p * v) := mul_comm _ _)
    hc hcd hdL hm hplateau
  have e1 : (fun u : ℝ => φ u * u ^ 2 * Real.cosh (a * u))
      = fun u : ℝ => u ^ 2 * φ u * Real.cosh (a * u) := by funext u; ring
  have e2 : (fun u : ℝ => φ u * Real.cosh (p * u))
      = fun u : ℝ => u ^ 0 * φ u * Real.cosh (p * u) := by funext u; ring
  have e3 : (fun u : ℝ => φ u * Real.cosh (a * u))
      = fun u : ℝ => u ^ 0 * φ u * Real.cosh (a * u) := by funext u; ring
  have e4 : (fun u : ℝ => φ u * u ^ 2 * Real.cosh (p * u))
      = fun u : ℝ => u ^ 2 * φ u * Real.cosh (p * u) := by funext u; ring
  rw [e1, e2, e3, e4] at key
  simp only [evenMoment]
  linarith

end Taper

end StrictKernelMomentRatio
end RiemannAnalytic
