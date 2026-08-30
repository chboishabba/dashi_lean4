/-
# An adapter, not a replacement: the exterior observable `e₂` from the companion's trace theorem

This module sits in a *separate* Lean project (`Zeta23Bridge/`), on the toolchain
required by the external companion library `Zeta23`
(<https://github.com/anthropics/zeta-23-lean>, pinned in `lakefile.toml`), because that
library is built against a different Lean/Mathlib version than the main
`RiemannAnalytic` library of this repository.  Nothing in `RiemannAnalytic`
depends on it, and no statement of `RiemannAnalytic` is weakened or assumed here.

What it does: it takes the companion's trace theorem
`Zeta23.PrimeSide.thm_traces` — [thm:traces] of the paper, for the prime-side
matrix `G̃`, applied to `Zeta23.paperInputs_zeta`, i.e. to the actual nontrivial
zeros of Mathlib's `riemannZeta` — and transports its two conclusions

    tr G̃  = L·N(T,2T)(1 + O(𝓔_T)),      tr G̃² = mainTr₂(T)(1 + O(𝓔_T))

to the *positive exterior observable*

    e₂ = ½ ((tr G̃)² − tr G̃²) = ∑_{k<l} ‖v_k ∧ v_l‖²,

which is the object the zero-side Gram geometry of `RiemannAnalytic` actually
consumes.  The result, `zeta23_e2_asymptotic`, is an explicit `EvBound`:

    |e₂ − ½((L·N)² − mainTr₂)| ≤ C · 𝓔_T · ((L·N)² + mainTr₂)   for T large.

Since the companion proves `𝓔_T → 0`, this is a genuine asymptotic for `e₂`.

It also answers, negatively, the question whether that budget can close the
transverse tube of `RiemannAnalytic.GramBudgetTransport`: the main term of `e₂`
is of size `T²L²`, whereas the zero-side floor is `L⁶` with `L ≍ log T`.  See
`e2_main_over_L6_tendsto_atTop`: `E(T)/L(T)⁶ → ∞`.  The total exterior area of
the full `d × d` evaluation family is therefore far too coarse a budget, and a
localized (bounded-height) budget is what is needed.
-/
import Zeta23.Final

noncomputable section

open Filter Topology Real

namespace Zeta23Bridge

open Zeta23

/-! ## The exterior observable -/

/-- `e₂ = ½ ((tr G)² − tr G²)`, the second elementary symmetric function of the
eigenvalues written in the first two power traces.  For a Gram matrix it equals
the total squared exterior 2-volume `∑_{i<j} ‖vᵢ ∧ vⱼ‖² ≥ 0`. -/
def e2OfTraces (t₁ t₂ : ℝ) : ℝ := (t₁ ^ 2 - t₂) / 2

theorem e2OfTraces_def (t₁ t₂ : ℝ) : e2OfTraces t₁ t₂ = (t₁ ^ 2 - t₂) / 2 := rfl

/-! ## The generic adapter -/

/-- **The `e₂` adapter** (generic form, over arbitrary trace data).

From `|tr − m₁| ≤ C₁ 𝓔 m₁` and `|tr₂ − m₂| ≤ C₂ 𝓔 m₂`, with `m₁, m₂ ≥ 0` and
`0 ≤ 𝓔 ≤ 1` eventually, one gets

    |e₂(tr, tr₂) − e₂(m₁, m₂)| ≤ ((C₁² + 2C₁ + C₂)/2) · 𝓔 · (m₁² + m₂). -/
theorem evBound_e2_of_traces {tr1 tr2 m1 m2 err : ℝ → ℝ}
    (h1 : EvBound (fun T => tr1 T - m1 T) (fun T => err T * m1 T))
    (h2 : EvBound (fun T => tr2 T - m2 T) (fun T => err T * m2 T))
    (hev : ∀ᶠ T in atTop, 0 ≤ m1 T ∧ 0 ≤ m2 T ∧ 0 ≤ err T ∧ err T ≤ 1) :
    EvBound (fun T => e2OfTraces (tr1 T) (tr2 T) - e2OfTraces (m1 T) (m2 T))
      (fun T => err T * (m1 T ^ 2 + m2 T)) := by
  obtain ⟨C₁, hC₁, T₁, hT₁⟩ := h1
  obtain ⟨C₂, hC₂, T₂, hT₂⟩ := h2
  obtain ⟨T₃, hT₃⟩ := eventually_atTop.mp hev
  refine ⟨(C₁ ^ 2 + 2 * C₁ + C₂) / 2, by positivity, max (max T₁ T₂) T₃, fun T hT => ?_⟩
  have hb1 := hT₁ T (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT)
  have hb2 := hT₂ T (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT)
  obtain ⟨hm1T, hm2T, herr0T, herr1T⟩ := hT₃ T (le_trans (le_max_right _ _) hT)
  simp only at hb1 hb2 ⊢
  set x := tr1 T - m1 T with hx
  set y := tr2 T - m2 T with hy
  set a := m1 T with ha
  set b := m2 T with hb
  set e := err T with he
  have ha0 : 0 ≤ a := hm1T
  have hb0 : 0 ≤ b := hm2T
  have he0 : 0 ≤ e := herr0T
  have he1 : e ≤ 1 := herr1T
  obtain ⟨hx1, hx2⟩ := abs_le.mp hb1
  obtain ⟨hy1, hy2⟩ := abs_le.mp hb2
  have hxsq : x ^ 2 ≤ (C₁ * e * a) ^ 2 := by nlinarith [sq_nonneg x, abs_nonneg x, sq_abs x]
  have hesq : e ^ 2 ≤ e := by nlinarith
  have hkey : x ^ 2 ≤ C₁ ^ 2 * e * a ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg (C₁ * a)]
  have hxa : x * a ≤ C₁ * e * a ^ 2 := by nlinarith
  have hxa' : -(x * a) ≤ C₁ * e * a ^ 2 := by nlinarith
  have hgoal : e2OfTraces (tr1 T) (tr2 T) - e2OfTraces (m1 T) (m2 T)
      = (x ^ 2 + 2 * (x * a) - y) / 2 := by
    rw [e2OfTraces_def, e2OfTraces_def, hx, hy, ha, hb]
    ring
  rw [hgoal]
  refine abs_le.mpr ⟨?_, ?_⟩
  · nlinarith [mul_nonneg he0 (sq_nonneg a), mul_nonneg he0 hb0, sq_nonneg x,
      mul_nonneg (mul_nonneg hC₂.le he0) hb0, mul_nonneg (mul_nonneg hC₁.le he0) (sq_nonneg a),
      mul_nonneg (mul_nonneg (sq_nonneg C₁) he0) (sq_nonneg a)]
  · nlinarith [mul_nonneg he0 (sq_nonneg a), mul_nonneg he0 hb0, sq_nonneg x,
      mul_nonneg (mul_nonneg hC₂.le he0) hb0, mul_nonneg (mul_nonneg hC₁.le he0) (sq_nonneg a),
      mul_nonneg (mul_nonneg (sq_nonneg C₁) he0) (sq_nonneg a)]

/-! ## The companion's trace theorem for ζ -/

/-- The parameter record of the source taper at aperture `λ`. -/
def Pof (lam : ℝ) : Params := paramsOf stdProfile lam

/-- `N(T, 2T)` for the actual nontrivial zeros of Mathlib's `riemannZeta`,
counted with multiplicity, as a real number. -/
def Nz (T : ℝ) : ℝ := (zetaZeroConfig.N T (2 * T) : ℝ)

/-- **The companion's [thm:traces], instantiated at ζ.**  Unconditional: the
only inputs are `0 < λ ≤ 1` and the companion's own `paperInputs_zeta`. -/
theorem tracesBounds_zeta {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    TracesBounds (Pof lam) (Pof lam).a (Pof lam).trGtilde (Pof lam).trGtildeSq Nz :=
  PrimeSide.thm_traces (paramsOf_valid taperProfile_stdProfile h0 h1) paperInputs_zeta

/-! ## Eventual positivity of the scales -/

theorem l_nonneg_eventually : ∀ᶠ T : ℝ in atTop, 0 ≤ l T := by
  filter_upwards [eventually_ge_atTop (2 * Real.pi)] with T hT
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have : (1 : ℝ) ≤ T / (2 * Real.pi) := (one_le_div hpi).mpr hT
  exact Real.log_nonneg this

theorem L_nonneg_eventually {lam : ℝ} (h0 : 0 < lam) :
    ∀ᶠ T : ℝ in atTop, 0 ≤ (Pof lam).L T := by
  filter_upwards [l_nonneg_eventually] with T hT
  have hlam : (Pof lam).lam = lam := rfl
  simp only [Params.L, hlam]
  positivity

theorem mainTr2_nonneg_eventually {lam : ℝ} (h0 : 0 < lam) :
    ∀ᶠ T : ℝ in atTop, 0 ≤ (Pof lam).mainTr2 T := by
  filter_upwards [L_nonneg_eventually h0, eventually_ge_atTop (0 : ℝ)] with T hL hT
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 : 0 ≤ T * (Pof lam).L T / (2 * Real.pi) := by positivity
  have h2 : 0 ≤ ell1 T ^ 2 + (Pof lam).L T ^ 2 / 3 := by positivity
  simpa [Params.mainTr2] using mul_nonneg h1 h2

theorem LN_nonneg_eventually {lam : ℝ} (h0 : 0 < lam) :
    ∀ᶠ T : ℝ in atTop, 0 ≤ (Pof lam).L T * Nz T := by
  filter_upwards [L_nonneg_eventually h0] with T hL
  exact mul_nonneg hL (Nat.cast_nonneg _)

theorem calE_eventually {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    ∀ᶠ T : ℝ in atTop, 0 ≤ (Pof lam).calE T ∧ (Pof lam).calE T ≤ 1 := by
  have hw : (0 : ℝ) ≤ (Pof lam).w := by norm_num [Pof, paramsOf]
  have hlam : 0 < (Pof lam).lam := h0
  have hlam1 : (Pof lam).lam ≤ 1 := h1
  have hz := PaperParams.calE_tendsto_zero (P := Pof lam) hlam hlam1 hw
  have hlt : ∀ᶠ T : ℝ in atTop, (Pof lam).calE T < 1 :=
    hz.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [PaperParams.calE_nonneg_eventually (P := Pof lam) hlam hw, hlt] with T h h'
  exact ⟨h, h'.le⟩

/-! ## The asymptotic for `e₂` -/

/-- **`zeta23_e2_asymptotic`.**  For the actual nontrivial zeros of Mathlib's
`riemannZeta`, and the source taper at any aperture `0 < λ ≤ 1`, the exterior
observable of the prime-side matrix `G̃` obeys

    |e₂(tr G̃, tr G̃²) − ½((L·N(T,2T))² − mainTr₂(T))|
        ≤ C · 𝓔_T · ((L·N(T,2T))² + mainTr₂(T))

for all large `T`, with `𝓔_T → 0` (`Zeta23.PaperParams.calE_tendsto_zero`).

This is the transport of the companion's [thm:traces] to the positive exterior
observable; no new analytic input is used, and the two trace bounds are the
companion's theorems, not hypotheses of this file. -/
theorem zeta23_e2_asymptotic {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    EvBound
      (fun T => e2OfTraces ((Pof lam).trGtilde T) ((Pof lam).trGtildeSq T)
        - e2OfTraces ((Pof lam).L T * Nz T) ((Pof lam).mainTr2 T))
      (fun T => (Pof lam).calE T * (((Pof lam).L T * Nz T) ^ 2 + (Pof lam).mainTr2 T)) := by
  have hTr := tracesBounds_zeta h0 h1
  refine evBound_e2_of_traces hTr.tr1' hTr.tr2 ?_
  filter_upwards [LN_nonneg_eventually h0, mainTr2_nonneg_eventually h0, calE_eventually h0 h1]
    with T hLN hM ⟨he0, he1⟩
  exact ⟨hLN, hM, he0, he1⟩


/-! ## Q5: does this budget close the transverse tube?  No.

The zero-side tube theorem of `RiemannAnalytic.GramBudgetTransport` closes only
when the budget satisfies `E(T)/L(T)⁶ → 0`.  The budget supplied by the total
exterior area of the prime-side matrix is far larger than that: its main term is
of order `T²L²`, while `L ≍ log T`.  The following theorems prove this, from the
companion's own Riemann–von Mangoldt input and the `e₂` asymptotic above. -/

/-- For any constant `c`, eventually `c log T ≤ T`. -/
theorem eventually_const_mul_log_le (c : ℝ) : ∀ᶠ T : ℝ in atTop, c * Real.log T ≤ T := by
  set d : ℝ := |c| + 1 with hd
  have hdpos : 0 < d := by positivity
  have hlim : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hev : ∀ᶠ T : ℝ in atTop, Real.log T / T < 1 / d :=
    hlim.eventually (eventually_lt_nhds (by positivity))
  filter_upwards [hev, eventually_ge_atTop (1 : ℝ)] with T hT hT1
  have hTpos : (0 : ℝ) < T := by linarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have h1 : Real.log T < T / d := by
    rw [div_lt_div_iff₀ hTpos hdpos] at hT
    rw [lt_div_iff₀ hdpos]
    linarith
  have h2 : c * Real.log T ≤ d * Real.log T := by
    have : c ≤ d := by
      have := le_abs_self c
      linarith
    exact mul_le_mul_of_nonneg_right this hlog0
  have h3 : d * Real.log T < T := by
    rw [lt_div_iff₀ hdpos] at h1
    linarith
  linarith

/-- `l T ≥ M` eventually, for any `M`. -/
theorem eventually_l_ge (M : ℝ) : ∀ᶠ T : ℝ in atTop, M ≤ l T := by
  filter_upwards [eventually_ge_atTop (2 * Real.pi * Real.exp M)] with T hT
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hexp : Real.exp M ≤ T / (2 * Real.pi) := by
    rw [le_div_iff₀ hpi]
    linarith [hT]
  have hpos : (0 : ℝ) < T / (2 * Real.pi) := lt_of_lt_of_le (Real.exp_pos M) hexp
  have := (Real.le_log_iff_exp_le hpos).2 hexp
  simpa [l] using this

/-- **The zero count dominates `T`.**  From the companion's Riemann–von Mangoldt
input, `N(T,2T) ≥ T` for all large `T`. -/
theorem Nz_ge_self_eventually : ∀ᶠ T : ℝ in atTop, T ≤ Nz T := by
  obtain ⟨C, T₀, hC⟩ := riemannVonMangoldt_zeta.main
  filter_upwards [eventually_ge_atTop T₀, eventually_l_ge (4 * Real.pi + 3),
    eventually_const_mul_log_le C, eventually_ge_atTop (0 : ℝ)] with T hT₀ hl hCl hT0
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hb := hC T hT₀
  have hlow : T / (2 * Real.pi) * ell1 T - C * Real.log T ≤ Nz T := by
    have := (abs_le.mp hb).1
    simp only [Nz] at this ⊢
    linarith
  have hell : 4 * Real.pi + 2 ≤ ell1 T := by
    have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    simp only [ell1]
    linarith
  have hfac : (0 : ℝ) ≤ T / (2 * Real.pi) := by positivity
  have hstep : T / (2 * Real.pi) * (4 * Real.pi + 2) ≤ T / (2 * Real.pi) * ell1 T :=
    mul_le_mul_of_nonneg_left hell hfac
  have hval : T / (2 * Real.pi) * (4 * Real.pi + 2) ≥ 2 * T := by
    rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [hpi, hT0]
  linarith

/-- The second-trace main term is dominated by half of the squared first-trace
main term: `mainTr₂ ≤ (L·N)²/2` eventually. -/
theorem mainTr2_le_half_LN_sq {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    ∀ᶠ T : ℝ in atTop, (Pof lam).mainTr2 T ≤ ((Pof lam).L T * Nz T) ^ 2 / 2 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  filter_upwards [eventually_l_ge 1, Nz_ge_self_eventually, eventually_ge_atTop (1 : ℝ),
    eventually_const_mul_log_le (5 / (Real.pi * lam))] with T hl hN hT1 hlog
  have hlam : (Pof lam).lam = lam := rfl
  have hL : (Pof lam).L T = lam * l T := rfl
  have hLpos : 0 < (Pof lam).L T := by rw [hL]; positivity
  have hlogle : l T ≤ Real.log T := by
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    have : Real.log (T / (2 * Real.pi)) = Real.log T - Real.log (2 * Real.pi) := by
      rw [Real.log_div (by linarith) (by positivity)]
    have hpos : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    simp only [l, this]
    linarith
  -- `5 l ≤ π λ T`
  have h5 : 5 * l T ≤ Real.pi * lam * T := by
    have hcoef : 5 / (Real.pi * lam) * Real.log T ≤ T := hlog
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hcoef
    nlinarith [hlogle, hl, mul_pos hpi h0]
  -- `ell1² + L²/3 ≤ π L T`
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hell : ell1 T ≤ 2 * l T := by
    simp only [ell1]
    linarith
  have hell0 : 0 ≤ ell1 T := by
    simp only [ell1]
    have : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  have hLl : (Pof lam).L T ≤ l T := by
    rw [hL]
    nlinarith [hl]
  have hkey : ell1 T ^ 2 + (Pof lam).L T ^ 2 / 3 ≤ Real.pi * (Pof lam).L T * T := by
    have hsq : ell1 T ^ 2 ≤ 4 * l T ^ 2 := by nlinarith [hell, hell0, hl]
    have hL2 : (Pof lam).L T ^ 2 / 3 ≤ l T ^ 2 := by nlinarith [hLl, hLpos.le, hl]
    have hrhs : 5 * l T ^ 2 ≤ Real.pi * (Pof lam).L T * T := by
      rw [hL]
      nlinarith [h5, hl, mul_pos hpi h0]
    linarith
  -- assemble
  have hfac : (0 : ℝ) ≤ T * (Pof lam).L T / (2 * Real.pi) := by positivity
  have hmain : (Pof lam).mainTr2 T
      ≤ T * (Pof lam).L T / (2 * Real.pi) * (Real.pi * (Pof lam).L T * T) := by
    simpa [Params.mainTr2] using mul_le_mul_of_nonneg_left hkey hfac
  have hval : T * (Pof lam).L T / (2 * Real.pi) * (Real.pi * (Pof lam).L T * T)
      = ((Pof lam).L T * T) ^ 2 / 2 := by
    field_simp
  have hmono : ((Pof lam).L T * T) ^ 2 / 2 ≤ ((Pof lam).L T * Nz T) ^ 2 / 2 := by
    have h1' : (Pof lam).L T * T ≤ (Pof lam).L T * Nz T :=
      mul_le_mul_of_nonneg_left hN hLpos.le
    have h2' : 0 ≤ (Pof lam).L T * T := by positivity
    nlinarith
  rw [hval] at hmain
  linarith

/-- **The exterior area of the prime-side matrix is at least `(L T)²/8`.** -/
theorem zeta23_e2_ge_eventually {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    ∀ᶠ T : ℝ in atTop,
      ((Pof lam).L T * T) ^ 2 / 8
        ≤ e2OfTraces ((Pof lam).trGtilde T) ((Pof lam).trGtildeSq T) := by
  obtain ⟨C, hCpos, T₀, hb⟩ := zeta23_e2_asymptotic h0 h1
  have hw : (0 : ℝ) ≤ (Pof lam).w := by norm_num [Pof, paramsOf]
  have hz := PaperParams.calE_tendsto_zero (P := Pof lam) h0 h1 hw
  have hsmall : ∀ᶠ T : ℝ in atTop, (Pof lam).calE T < 1 / (12 * C) :=
    hz.eventually (eventually_lt_nhds (by positivity))
  filter_upwards [eventually_ge_atTop T₀, hsmall, mainTr2_le_half_LN_sq h0 h1,
    mainTr2_nonneg_eventually h0, Nz_ge_self_eventually, L_nonneg_eventually h0,
    PaperParams.calE_nonneg_eventually (P := Pof lam) h0 hw, eventually_ge_atTop (1 : ℝ)]
    with T hT hE hM hM0 hN hL hE0 hT1
  have hbT := hb T hT
  simp only at hbT
  set A : ℝ := (Pof lam).L T * Nz T with hA
  set M2 : ℝ := (Pof lam).mainTr2 T with hM2
  set e : ℝ := (Pof lam).calE T with he
  set X : ℝ := e2OfTraces ((Pof lam).trGtilde T) ((Pof lam).trGtildeSq T) with hX
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg hL (Nat.cast_nonneg _)
  have hlow : X ≥ e2OfTraces A M2 - C * (e * (A ^ 2 + M2)) := by
    have := (abs_le.mp hbT).1
    linarith
  have hmain : e2OfTraces A M2 ≥ A ^ 2 / 4 := by
    rw [e2OfTraces_def]
    linarith
  have hsum : A ^ 2 + M2 ≤ 3 / 2 * A ^ 2 := by linarith
  have hbound : C * (e * (A ^ 2 + M2)) ≤ A ^ 2 / 8 := by
    have h1' : e * (A ^ 2 + M2) ≤ e * (3 / 2 * A ^ 2) :=
      mul_le_mul_of_nonneg_left hsum hE0
    have h2' : C * (e * (3 / 2 * A ^ 2)) ≤ A ^ 2 / 8 := by
      have heC : C * e ≤ 1 / 12 := by
        have hlt := mul_lt_mul_of_pos_left hE hCpos
        have hval : C * (1 / (12 * C)) = 1 / 12 := by field_simp
        rw [hval] at hlt
        linarith
      nlinarith [sq_nonneg A, hE0, hCpos]
    nlinarith [hCpos.le, sq_nonneg A]
  have hLT : ((Pof lam).L T * T) ^ 2 ≤ A ^ 2 := by
    have h1' : (Pof lam).L T * T ≤ A := by
      rw [hA]
      exact mul_le_mul_of_nonneg_left hN hL
    have h2' : 0 ≤ (Pof lam).L T * T := by positivity
    nlinarith
  linarith

/-- `T / (log T)⁴ → ∞`. -/
theorem tendsto_id_div_log_pow_four :
    Tendsto (fun T : ℝ => T / Real.log T ^ 4) atTop atTop := by
  have h : Tendsto (fun T : ℝ => Real.log T ^ 4 / T) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨by simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 4 one_ne_zero, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hl : 0 < Real.log T := Real.log_pos hT
    simp only [Set.mem_Ioi]
    positivity
  have h2 := tendsto_inv_nhdsGT_zero.comp h
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  have hl : 0 < Real.log T := Real.log_pos hT
  simp [Function.comp, inv_div]

/-- **Q5, answered negatively.**  The exterior-area budget delivered by the
companion's trace theorem, normalized by the sixth power of the taper scale,
*diverges*:

    e₂(T) / L(T)⁶ → ∞.

So the tube criterion `E(T)/L(T)⁶ → 0` of
`RiemannAnalytic.GramBudgetTransport.tendsto_zero_of_budget_ratio` is not met by
the total exterior area of the full `d × d` prime-side family, by a margin of a
power of `T`.  A budget localized to a bounded number of zeros — not the total
area — is what the zero-side geometry needs. -/
theorem zeta23_e2_over_L6_tendsto_atTop {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    Tendsto (fun T => e2OfTraces ((Pof lam).trGtilde T) ((Pof lam).trGtildeSq T)
      / (Pof lam).L T ^ 6) atTop atTop := by
  have hbase : Tendsto (fun T : ℝ => 1 / (8 * lam ^ 4) * (T / Real.log T ^ 4)) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity) tendsto_id_div_log_pow_four
  refine tendsto_atTop_mono' atTop ?_ hbase
  filter_upwards [zeta23_e2_ge_eventually h0 h1, eventually_l_ge 1, eventually_ge_atTop (1 : ℝ),
    eventually_gt_atTop (1 : ℝ)] with T hE hl hT1 hT
  have hlogpos : 0 < Real.log T := Real.log_pos hT
  have hL : (Pof lam).L T = lam * l T := rfl
  have hLpos : 0 < (Pof lam).L T := by rw [hL]; positivity
  have hlogle : l T ≤ Real.log T := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have hlogdiv : Real.log (T / (2 * Real.pi)) = Real.log T - Real.log (2 * Real.pi) := by
      rw [Real.log_div (by linarith) (by positivity)]
    have hpos : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    simp only [l, hlogdiv]
    linarith
  have hL4 : (Pof lam).L T ^ 4 ≤ lam ^ 4 * Real.log T ^ 4 := by
    have hle : (Pof lam).L T ≤ lam * Real.log T := by
      rw [hL]
      nlinarith [hlogle, h0]
    have h0' : 0 ≤ (Pof lam).L T := hLpos.le
    have h4 : (Pof lam).L T ^ 4 ≤ (lam * Real.log T) ^ 4 := by gcongr
    calc (Pof lam).L T ^ 4 ≤ (lam * Real.log T) ^ 4 := h4
      _ = lam ^ 4 * Real.log T ^ 4 := by ring
  have hL6 : (0 : ℝ) < (Pof lam).L T ^ 6 := by positivity
  have hstep : 1 / (8 * lam ^ 4) * (T / Real.log T ^ 4)
      ≤ ((Pof lam).L T * T) ^ 2 / 8 / (Pof lam).L T ^ 6 := by
    have hDL : (0 : ℝ) < 8 * (Pof lam).L T ^ 4 := by positivity
    have hDlam : (0 : ℝ) < 8 * lam ^ 4 * Real.log T ^ 4 := by positivity
    have hRHS : ((Pof lam).L T * T) ^ 2 / 8 / (Pof lam).L T ^ 6
        = T ^ 2 / (8 * (Pof lam).L T ^ 4) := by
      field_simp
    have hLHS : 1 / (8 * lam ^ 4) * (T / Real.log T ^ 4)
        = T / (8 * lam ^ 4 * Real.log T ^ 4) := by
      field_simp
    rw [hRHS, hLHS, div_le_div_iff₀ hDlam hDL]
    have hT2 : T ≤ T ^ 2 := by nlinarith
    have hDle : 8 * (Pof lam).L T ^ 4 ≤ 8 * lam ^ 4 * Real.log T ^ 4 := by linarith [hL4]
    have hT0 : (0 : ℝ) < T := by linarith
    nlinarith [hDle, hT2, hDL, hDlam, hT0]
  have hmono : ((Pof lam).L T * T) ^ 2 / 8 / (Pof lam).L T ^ 6
      ≤ e2OfTraces ((Pof lam).trGtilde T) ((Pof lam).trGtildeSq T) / (Pof lam).L T ^ 6 :=
    (div_le_div_iff_of_pos_right hL6).mpr hE
  linarith

end Zeta23Bridge
