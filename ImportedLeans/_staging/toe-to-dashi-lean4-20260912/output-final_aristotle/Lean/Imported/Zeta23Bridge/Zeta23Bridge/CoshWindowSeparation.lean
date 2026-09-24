/-
# Localized-window separation of hyperbolic response ratios

The multi-taper Schur programme needs the following separation statement: two
localized tapers, sitting in *different* modulus windows, must respond to two
different zero heights with *different ratios*.  After the covariance form of the
leading coefficient (`LiteralWeilLeadingCoefficientCovariance`) the whole question
reduces to a statement about the two-parameter family of increments

    coshDiff x u v = cosh (x * v) - cosh (x * u),   0 < u < v,

namely that the ratio

    rho (u, v) = coshDiff b u v / coshDiff a u v      (0 < a < b)

is **strictly increasing in each of `u` and `v`**.  This module proves that, with no
narrowness hypothesis and no numerical input, from the following elementary chain.

* `sinh_lt_mul_cosh` — `sinh t < t cosh t` for `t > 0`.
* `mul_sinh_lt_mul_sinh` — `t ↦ sinh t / t` is strictly increasing.
* `mul_cosh_mul_sinh_lt` — `t ↦ t coth t` is strictly increasing (via the addition
  formulas this is exactly the previous item).
* `sinh_cross_lt` — hence `s ↦ sinh (b s) / sinh (a s)` is strictly increasing.
* `cosh_increment_cross` — hence, by two applications of the Cauchy mean value
  theorem, consecutive increments of `cosh (a ·)` and `cosh (b ·)` cross:
  `AD > BC`.
* `coshDiff_ratio_lt_of_lt_top`, `coshDiff_ratio_lt_of_lt_bot` — the two
  monotonicities of `rho`, obtained from the crossing inequality by pure algebra.
* `coshDiff_cross_of_window_gate` — the packaged window statement: if the four
  window endpoints satisfy the ratio gate, then *every* pair of points drawn from
  the windows satisfies the strict cross inequality.  This is the pointwise input
  that gets integrated against the tapers in
  `LiteralWeilWindowRatioSeparation`.

Everything is stated division-free, so no positivity side conditions leak into the
downstream statements.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Mathlib

noncomputable section

open Real Set

namespace Zeta23Bridge
namespace CoshWindowSeparation

/-! ## Elementary hyperbolic monotonicity -/

/-- `sinh t < t cosh t` for `t > 0`; equivalently `tanh t < t`. -/
theorem sinh_lt_mul_cosh {t : ℝ} (ht : 0 < t) : Real.sinh t < t * Real.cosh t := by
  have key : StrictMonoOn (fun x : ℝ => x * Real.cosh x - Real.sinh x) (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · fun_prop
    · intro x hx
      rw [interior_Ici, mem_Ioi] at hx
      have h : HasDerivAt (fun x : ℝ => x * Real.cosh x - Real.sinh x)
          (1 * Real.cosh x + x * Real.sinh x - Real.cosh x) x :=
        ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub (Real.hasDerivAt_sinh x)
      rw [h.deriv]
      have : 0 < x * Real.sinh x := by positivity
      linarith
  have := key Set.self_mem_Ici (le_of_lt ht : (0:ℝ) ≤ t) ht
  simp at this
  linarith

/-- `t ↦ sinh t / t` is strictly increasing: for `0 < p < q`, `q · sinh p < p · sinh q`. -/
theorem mul_sinh_lt_mul_sinh {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    q * Real.sinh p < p * Real.sinh q := by
  have key : StrictMonoOn (fun x : ℝ => p * Real.sinh x - x * Real.sinh p) (Ici p) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici p)
    · fun_prop
    · intro x hx
      rw [interior_Ici, mem_Ioi] at hx
      have h : HasDerivAt (fun x : ℝ => p * Real.sinh x - x * Real.sinh p)
          (p * Real.cosh x - 1 * Real.sinh p) x :=
        ((Real.hasDerivAt_sinh x).const_mul p).sub ((hasDerivAt_id x).mul_const (Real.sinh p))
      rw [h.deriv]
      have h1 : Real.sinh p < p * Real.cosh p := sinh_lt_mul_cosh hp
      have h2 : Real.cosh p ≤ Real.cosh x := by
        apply Real.cosh_le_cosh.mpr
        rw [abs_of_pos hp, abs_of_pos (hp.trans hx)]
        exact hx.le
      nlinarith
  have := key Set.self_mem_Ici (le_of_lt hpq : p ≤ q) hpq
  simp only at this
  nlinarith

/-- `t ↦ t coth t` is strictly increasing on `(0, ∞)`, in division-free form. -/
theorem mul_cosh_mul_sinh_lt {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    x * Real.cosh x * Real.sinh y < y * Real.cosh y * Real.sinh x := by
  have h := mul_sinh_lt_mul_sinh (p := y - x) (q := x + y) (by linarith) (by linarith)
  rw [Real.sinh_sub, Real.sinh_add] at h
  nlinarith [h]

/-- For `0 < a < b` the function `s ↦ sinh (b s) / sinh (a s)` is strictly increasing. -/
theorem sinh_cross_lt {a b : ℝ} (ha : 0 < a) (hab : a < b) {s s' : ℝ} (hs : 0 < s)
    (hss : s < s') :
    Real.sinh (b * s) * Real.sinh (a * s') < Real.sinh (a * s) * Real.sinh (b * s') := by
  have hb : 0 < b := ha.trans hab
  have key : StrictMonoOn (fun x : ℝ => Real.sinh (b * x) / Real.sinh (a * x)) (Ioi 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    · apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro x hx
      simp only [mem_Ioi] at hx
      have : 0 < Real.sinh (a * x) := Real.sinh_pos_iff.mpr (by positivity)
      linarith
    · intro x hx
      rw [interior_Ioi, mem_Ioi] at hx
      have hax : 0 < a * x := mul_pos ha hx
      have hden : 0 < Real.sinh (a * x) := Real.sinh_pos_iff.mpr hax
      have hnum : HasDerivAt (fun y : ℝ => Real.sinh (b * y)) (Real.cosh (b * x) * b) x := by
        simpa using ((hasDerivAt_id x).const_mul b).sinh
      have hden' : HasDerivAt (fun y : ℝ => Real.sinh (a * y)) (Real.cosh (a * x) * a) x := by
        simpa using ((hasDerivAt_id x).const_mul a).sinh
      have h : HasDerivAt (fun y : ℝ => Real.sinh (b * y) / Real.sinh (a * y))
          ((Real.cosh (b * x) * b * Real.sinh (a * x)
            - Real.sinh (b * x) * (Real.cosh (a * x) * a)) / Real.sinh (a * x) ^ 2) x :=
        hnum.div hden' (ne_of_gt hden)
      rw [h.deriv]
      apply div_pos _ (by positivity)
      have hk := mul_cosh_mul_sinh_lt (x := a * x) (y := b * x) hax (by nlinarith)
      nlinarith [hk, hx]
  have h1 := key (mem_Ioi.mpr hs) (mem_Ioi.mpr (hs.trans hss)) hss
  simp only at h1
  have hd1 : 0 < Real.sinh (a * s) := Real.sinh_pos_iff.mpr (mul_pos ha hs)
  have hd2 : 0 < Real.sinh (a * s') := Real.sinh_pos_iff.mpr (mul_pos ha (hs.trans hss))
  rw [div_lt_div_iff₀ hd1 hd2] at h1
  nlinarith [h1]

/-! ## The increment crossing inequality -/

/-- The increment of `cosh (x * ·)` across `[u, v]`. -/
def coshDiff (x u v : ℝ) : ℝ := Real.cosh (x * v) - Real.cosh (x * u)

theorem coshDiff_pos {x u v : ℝ} (hx : 0 < x) (hu : 0 < u) (huv : u < v) :
    0 < coshDiff x u v := by
  have : Real.cosh (x * u) < Real.cosh (x * v) := by
    apply Real.cosh_lt_cosh.mpr
    rw [abs_of_pos (mul_pos hx hu), abs_of_pos (mul_pos hx (hu.trans huv))]
    exact mul_lt_mul_of_pos_left huv hx
  simpa [coshDiff] using sub_pos.mpr this

theorem coshDiff_add {x u v w : ℝ} : coshDiff x u v + coshDiff x v w = coshDiff x u w := by
  unfold coshDiff; ring

/-- **Consecutive increments cross.**  For `0 < a < b` and `0 < c₀ < c₁ < c₂`, the
increment ratio of the `b`-cosine over the `a`-cosine is strictly larger on the upper
interval `[c₁, c₂]` than on the lower interval `[c₀, c₁]`. -/
theorem cosh_increment_cross {a b c0 c1 c2 : ℝ} (ha : 0 < a) (hab : a < b) (hc0 : 0 < c0)
    (h01 : c0 < c1) (h12 : c1 < c2) :
    coshDiff a c1 c2 * coshDiff b c0 c1 < coshDiff a c0 c1 * coshDiff b c1 c2 := by
  have hb : 0 < b := ha.trans hab
  have mvt : ∀ {lo hi : ℝ}, lo < hi → ∃ c ∈ Ioo lo hi,
      (Real.cosh (b * hi) - Real.cosh (b * lo)) * (a * Real.sinh (a * c))
        = (Real.cosh (a * hi) - Real.cosh (a * lo)) * (b * Real.sinh (b * c)) := by
    intro lo hi hlo
    obtain ⟨c, hc, h⟩ := exists_ratio_hasDerivAt_eq_ratio_slope (fun x : ℝ => Real.cosh (a * x))
      (fun x : ℝ => a * Real.sinh (a * x)) hlo (by fun_prop)
      (fun x _ => by simpa [mul_comm] using ((hasDerivAt_id x).const_mul a).cosh)
      (fun x : ℝ => Real.cosh (b * x)) (fun x : ℝ => b * Real.sinh (b * x)) (by fun_prop)
      (fun x _ => by simpa [mul_comm] using ((hasDerivAt_id x).const_mul b).cosh)
    exact ⟨c, hc, h⟩
  obtain ⟨xi, hxi, hA⟩ := mvt h01
  obtain ⟨eta, heta, hB⟩ := mvt h12
  have hxipos : 0 < xi := hc0.trans hxi.1
  have hetapos : 0 < eta := hxipos.trans (hxi.2.trans heta.1)
  have hk := sinh_cross_lt ha hab hxipos (hxi.2.trans heta.1)
  have hC : 0 < coshDiff b c0 c1 := coshDiff_pos hb hc0 h01
  have hD : 0 < coshDiff b c1 c2 := coshDiff_pos hb (hc0.trans h01) h12
  have hSbxi : 0 < Real.sinh (b * xi) := Real.sinh_pos_iff.mpr (mul_pos hb hxipos)
  have hSbeta : 0 < Real.sinh (b * eta) := Real.sinh_pos_iff.mpr (mul_pos hb hetapos)
  simp only [coshDiff] at hC hD ⊢
  set A := Real.cosh (a * c1) - Real.cosh (a * c0)
  set B := Real.cosh (a * c2) - Real.cosh (a * c1)
  set C := Real.cosh (b * c1) - Real.cosh (b * c0)
  set D := Real.cosh (b * c2) - Real.cosh (b * c1)
  have key : (A * D - B * C) * ((b * Real.sinh (b * xi)) * (b * Real.sinh (b * eta)))
      = a * b * (C * D) * (Real.sinh (a * xi) * Real.sinh (b * eta)
        - Real.sinh (a * eta) * Real.sinh (b * xi)) := by
    linear_combination (D * (b * Real.sinh (b * eta))) * hA.symm
      - (C * (b * Real.sinh (b * xi))) * hB.symm
  have hpos : 0 < a * b * (C * D) * (Real.sinh (a * xi) * Real.sinh (b * eta)
      - Real.sinh (a * eta) * Real.sinh (b * xi)) := by
    apply mul_pos (by positivity)
    nlinarith [hk]
  nlinarith [key, hpos, mul_pos (mul_pos hb hSbxi) (mul_pos hb hSbeta)]

/-! ## The two monotonicities of the increment ratio -/

/-- The increment ratio is strictly increasing in the **upper** endpoint. -/
theorem coshDiff_ratio_lt_of_lt_top {a b u v v' : ℝ} (ha : 0 < a) (hab : a < b) (hu : 0 < u)
    (huv : u < v) (hvv : v < v') :
    coshDiff b u v * coshDiff a u v' < coshDiff b u v' * coshDiff a u v := by
  have h := cosh_increment_cross ha hab hu huv hvv
  have e1 : coshDiff a u v' = coshDiff a u v + coshDiff a v v' := coshDiff_add.symm
  have e2 : coshDiff b u v' = coshDiff b u v + coshDiff b v v' := coshDiff_add.symm
  rw [e1, e2]
  nlinarith [h]

/-- The increment ratio is strictly increasing in the **lower** endpoint. -/
theorem coshDiff_ratio_lt_of_lt_bot {a b u u' v : ℝ} (ha : 0 < a) (hab : a < b) (hu : 0 < u)
    (huu : u < u') (huv : u' < v) :
    coshDiff b u v * coshDiff a u' v < coshDiff b u' v * coshDiff a u v := by
  have h := cosh_increment_cross ha hab hu huu huv
  have e1 : coshDiff a u v = coshDiff a u u' + coshDiff a u' v := coshDiff_add.symm
  have e2 : coshDiff b u v = coshDiff b u u' + coshDiff b u' v := coshDiff_add.symm
  rw [e1, e2]
  nlinarith [h]

/-- Monotonicity of the increment ratio in both endpoints simultaneously (non-strict). -/
theorem coshDiff_ratio_le {a b u u' v v' : ℝ} (ha : 0 < a) (hab : a < b) (hu : 0 < u)
    (huu : u ≤ u') (huv : u < v) (hu'v' : u' < v') (hvv : v ≤ v') :
    coshDiff b u v * coshDiff a u' v' ≤ coshDiff b u' v' * coshDiff a u v := by
  have hb : 0 < b := ha.trans hab
  have hu' : 0 < u' := hu.trans_le huu
  -- step 1: raise the upper endpoint from `v` to `v'`
  have step1 : coshDiff b u v * coshDiff a u v' ≤ coshDiff b u v' * coshDiff a u v := by
    rcases eq_or_lt_of_le hvv with h | h
    · subst h; ring_nf; exact le_refl _
    · exact (coshDiff_ratio_lt_of_lt_top ha hab hu huv h).le
  -- step 2: raise the lower endpoint from `u` to `u'`
  have huv' : u < v' := huv.trans_le hvv
  have step2 : coshDiff b u v' * coshDiff a u' v' ≤ coshDiff b u' v' * coshDiff a u v' := by
    rcases eq_or_lt_of_le huu with h | h
    · subst h; ring_nf; exact le_refl _
    · exact (coshDiff_ratio_lt_of_lt_bot ha hab hu h hu'v').le
  have hav' : 0 < coshDiff a u v' := coshDiff_pos ha hu huv'
  have hbv' : 0 < coshDiff b u v' := coshDiff_pos hb hu huv'
  have hav : 0 < coshDiff a u v := coshDiff_pos ha hu huv
  have ha'v' : 0 < coshDiff a u' v' := coshDiff_pos ha hu' hu'v'
  nlinarith [step1, step2, hav', hbv', hav, ha'v']

/-! ## The window gate -/

/-- The window gate is not vacuous: for degenerate (point) windows `al0 = be0 = c₀`,
`al1 = be1 = c₁`, `al2 = c₂` it is exactly the strict monotonicity of the increment
ratio in the upper endpoint, hence always true.  Widening the windows perturbs both
sides continuously, so the gate is the honest quantitative form of "the windows are
narrow enough". -/
theorem window_gate_of_point_windows {a b c0 c1 c2 : ℝ} (ha : 0 < a) (hab : a < b)
    (hc0 : 0 < c0) (h01 : c0 < c1) (h12 : c1 < c2) :
    coshDiff b c0 c1 * coshDiff a c0 c2 < coshDiff b c0 c2 * coshDiff a c0 c1 :=
  coshDiff_ratio_lt_of_lt_top ha hab hc0 h01 h12

/-- **Window separation.**  Let `[α₀, β₀]`, `[α₁, β₁]`, `[α₂, β₂]` be three ordered
modulus windows and `0 < a < b` two heights.  If the *endpoint gate*

    rho (β₀, β₁) < rho (α₀, α₂)

holds, then every pair of sample points drawn from the windows separates strictly:
the `(a, b)` response ratio at any point of the low/top pair strictly exceeds the
ratio at any point of the low/middle pair.  No narrowness hypothesis is used: the
gate is exactly the condition that the windows are narrow enough, expressed by four
endpoints. -/
theorem coshDiff_cross_of_window_gate {a b al0 be0 al1 be1 al2 be2 : ℝ}
    (ha : 0 < a) (hab : a < b) (hal0 : 0 < al0) (h0 : al0 ≤ be0) (h01 : be0 < al1)
    (h1 : al1 ≤ be1) (h12 : be1 < al2)
    (hgate : coshDiff b be0 be1 * coshDiff a al0 al2 < coshDiff b al0 al2 * coshDiff a be0 be1)
    {u u' v0 v1 : ℝ} (hu : u ∈ Icc al0 be0) (hu' : u' ∈ Icc al0 be0)
    (hv0 : v0 ∈ Icc al1 be1) (hv1 : v1 ∈ Icc al2 be2) :
    coshDiff b u v0 * coshDiff a u' v1 < coshDiff b u' v1 * coshDiff a u v0 := by
  have hb : 0 < b := ha.trans hab
  have hu0 : 0 < u := hal0.trans_le hu.1
  have hu'0 : 0 < u' := hal0.trans_le hu'.1
  have hbe0 : 0 < be0 := hal0.trans_le h0
  have hal2 : 0 < al2 := by linarith
  have huv0 : u < v0 := by have := hu.2; have := hv0.1; linarith
  have hu'v1 : u' < v1 := by have := hu'.2; have := hv1.1; linarith
  have hbe0be1 : be0 < be1 := by linarith
  have hal0al2 : al0 < al2 := by linarith
  -- upper bound for the low/middle ratio
  have hup : coshDiff b u v0 * coshDiff a be0 be1 ≤ coshDiff b be0 be1 * coshDiff a u v0 :=
    coshDiff_ratio_le ha hab hu0 hu.2 huv0 hbe0be1 hv0.2
  -- lower bound for the low/top ratio
  have hlow : coshDiff b al0 al2 * coshDiff a u' v1 ≤ coshDiff b u' v1 * coshDiff a al0 al2 :=
    coshDiff_ratio_le ha hab hal0 hu'.1 hal0al2 hu'v1 hv1.1
  have p1 : 0 < coshDiff a u v0 := coshDiff_pos ha hu0 huv0
  have p2 : 0 < coshDiff a u' v1 := coshDiff_pos ha hu'0 hu'v1
  have p3 : 0 < coshDiff a be0 be1 := coshDiff_pos ha hbe0 hbe0be1
  have p4 : 0 < coshDiff a al0 al2 := coshDiff_pos ha hal0 hal0al2
  -- chain the three ratio comparisons through the quotients
  have c1 : coshDiff b u v0 / coshDiff a u v0 ≤ coshDiff b be0 be1 / coshDiff a be0 be1 := by
    rw [div_le_div_iff₀ p1 p3]; linarith [hup]
  have c2 : coshDiff b be0 be1 / coshDiff a be0 be1 < coshDiff b al0 al2 / coshDiff a al0 al2 := by
    rw [div_lt_div_iff₀ p3 p4]; linarith [hgate]
  have c3 : coshDiff b al0 al2 / coshDiff a al0 al2 ≤ coshDiff b u' v1 / coshDiff a u' v1 := by
    rw [div_le_div_iff₀ p4 p2]; linarith [hlow]
  have : coshDiff b u v0 / coshDiff a u v0 < coshDiff b u' v1 / coshDiff a u' v1 :=
    lt_of_le_of_lt c1 (lt_of_lt_of_le c2 c3)
  rw [div_lt_div_iff₀ p1 p2] at this
  linarith [this]

end CoshWindowSeparation
end Zeta23Bridge
