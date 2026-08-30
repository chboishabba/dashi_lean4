/-
# The translated-source no-go for the global Gaussian Leray estimate

This file settles, negatively, the proposed *global Gaussian
Calderón–Zygmund estimate for the Leray projector*

  `‖ℙ∇·(V⊗V)‖_{L²(ρ_{2ν})} ≤ C ‖V‖_∞ ‖∇V‖_{L²(ρ_ν)}`,          (G-CZ)

with `ρ_ν(y) = e^{−‖y‖²/(4ν)}`, on the record-normalised class `‖V‖_∞ ≤ 1`.

The obstruction is exactly the one predicted by the near/far analysis: the
Gaussian weight is *exponentially* localised at the origin while the Leray
pressure is *nonlocal* with only polynomial decay.  Translating one fixed
divergence-free profile a distance `R` away therefore makes the right-hand
side decay like `e^{−cR²}` while the left-hand side, measured near the
origin, still sees a pressure gradient of size `R^{-2}`.

The construction is the explicit pair `(noGoV R, noGoP R)` of
`GaussianLerayCounterexampleField` and `GaussianLerayCounterexamplePressure`:
a crossed shear pair with `‖V‖_∞ ≤ 1`, `div V = 0`, whose nonlinear source is
one radial Gaussian centred at `c_R = (R,R,0)`, and whose exact Leray pressure
is `P(y) = Φ(‖y−c_R‖²)`.

The final statement `ClayNS.gaussian_leray_global_no_go` is a genuine
non-existence result: no finite constant works, even after imposing
smoothness, incompressibility, the record normalisation `‖V‖_∞ ≤ 1`, the
Leray relation `div((V·∇)V + ∇P) = 0` and the pressure gauge
`‖∇P‖ → 0 at infinity`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.GaussianLerayCounterexamplePressure

open MeasureTheory Set intervalIntegral
open scoped BigOperators

noncomputable section

namespace ClayNS

set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

/-! ## Elementary analytic helpers -/

/-- `e^{−t} ≤ 256/t⁴` for `t > 0`, from `1 + x ≤ e^x`. -/
lemma exp_neg_le_inv_pow4 {t : ℝ} (ht : 0 < t) : Real.exp (-t) ≤ 256 / t ^ 4 := by
  have h1 : t / 4 ≤ Real.exp (t / 4) := by
    have := Real.add_one_le_exp (t / 4); linarith
  have h2 : (t / 4) ^ 4 ≤ (Real.exp (t / 4)) ^ 4 := pow_le_pow_left₀ (by positivity) h1 4
  have h3 : (Real.exp (t / 4)) ^ 4 = Real.exp t := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h3] at h2
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos t), div_mul_eq_mul_div,
    le_div_iff₀ (by positivity : (0:ℝ) < t ^ 4)]
  nlinarith [Real.exp_pos t]

lemma half_le_exp_neg_half : (1 : ℝ) / 2 ≤ Real.exp (-(1/2)) := by
  have h1 : Real.exp (1/2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h2 : Real.exp 1 < 4 := by
    have := Real.exp_one_lt_d9; linarith
  have h3 : Real.exp (1/2) < 2 := by nlinarith [Real.exp_pos (1/2 : ℝ)]
  rw [Real.exp_neg]
  rw [le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
  · linarith
/-- The quadratic completion `(t−R)² + a t² ≥ aR²/(1+a)`. -/
lemma quad_split {a t R : ℝ} (ha : 0 < a) : a * R ^ 2 / (1 + a) ≤ (t - R) ^ 2 + a * t ^ 2 := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith [sq_nonneg ((1 + a) * t - R)]

/-! ## The kernel `ψ₀` -/

lemma psiN_zero_eq (u : ℝ) : psiN 0 u = ∫ s in (0:ℝ)..1, s ^ 2 * Real.exp (-u * s ^ 2 / 2) := by
  rw [psiN]

lemma cont_ps (u : ℝ) : Continuous (fun s : ℝ => s ^ 2 * Real.exp (-u * s ^ 2 / 2)) := by fun_prop

lemma psiN0_pos (u : ℝ) : 0 < psiN 0 u := by
  rw [psiN_zero_eq]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on ((cont_ps u).intervalIntegrable _ _)
  · intro s hs; exact mul_pos (pow_pos hs.1 2) (Real.exp_pos _)
  · norm_num

lemma psiN0_le_third {u : ℝ} (hu : 0 ≤ u) : psiN 0 u ≤ 1 / 3 := by
  rw [psiN_zero_eq]
  have h : (∫ s in (0:ℝ)..1, s ^ 2 * Real.exp (-u * s ^ 2 / 2)) ≤ ∫ s in (0:ℝ)..1, s ^ 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((cont_ps u).intervalIntegrable _ _) ((continuous_pow 2).intervalIntegrable _ _)
    intro s _
    have h1 : Real.exp (-u * s ^ 2 / 2) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr; nlinarith [sq_nonneg s]
    nlinarith [sq_nonneg s, Real.exp_pos (-u * s ^ 2 / 2)]
  calc (∫ s in (0:ℝ)..1, s ^ 2 * Real.exp (-u * s ^ 2 / 2)) ≤ ∫ s in (0:ℝ)..1, s ^ 2 := h
    _ = 1 / 3 := by rw [integral_pow]; norm_num

lemma psiN0_le_two_div {u : ℝ} (hu : 0 < u) : psiN 0 u ≤ 2 / u := by
  rw [psiN_zero_eq]
  have h : (∫ s in (0:ℝ)..1, s ^ 2 * Real.exp (-u * s ^ 2 / 2))
      ≤ ∫ _s in (0:ℝ)..1, 2 / u := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((cont_ps u).intervalIntegrable _ _) (_root_.intervalIntegrable_const)
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [← h0]; simp; positivity
    · have h1 : u * s ^ 2 / 2 ≤ Real.exp (u * s ^ 2 / 2) := by
        have := Real.add_one_le_exp (u * s ^ 2 / 2); linarith
      have h2 : Real.exp (-u * s ^ 2 / 2) = (Real.exp (u * s ^ 2 / 2))⁻¹ := by
        rw [← Real.exp_neg]; congr 1; ring
      rw [h2, mul_inv_le_iff₀ (Real.exp_pos _)]
      calc s ^ 2 = (2 / u) * (u * s ^ 2 / 2) := by field_simp
        _ ≤ (2 / u) * Real.exp (u * s ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
  calc (∫ s in (0:ℝ)..1, s ^ 2 * Real.exp (-u * s ^ 2 / 2)) ≤ ∫ _s in (0:ℝ)..1, 2 / u := h
    _ = 2 / u := by simp

/-- For `u ≥ 1`, `ψ₀(u) ≥ e^{−1/2}/(3u√u)`. -/
lemma psiN0_lower {u : ℝ} (hu : 1 ≤ u) :
    Real.exp (-(1/2)) / (3 * u * Real.sqrt u) ≤ psiN 0 u := by
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
  set c : ℝ := 1 / Real.sqrt u with hc
  have hcpos : 0 < c := by positivity
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one hsu]
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt u := Real.sqrt_le_sqrt hu
  have step1 : (∫ s in (0:ℝ)..c, s ^ 2 * Real.exp (-u * s ^ 2 / 2))
      ≤ ∫ s in (0:ℝ)..1, s ^ 2 * Real.exp (-u * s ^ 2 / 2) := by
    apply intervalIntegral.integral_mono_interval (le_refl 0) hcpos.le hc1
    · filter_upwards with s using by positivity
    · exact (cont_ps u).intervalIntegrable _ _
  have step2 : (∫ s in (0:ℝ)..c, s ^ 2 * Real.exp (-(1/2)))
      ≤ ∫ s in (0:ℝ)..c, s ^ 2 * Real.exp (-u * s ^ 2 / 2) := by
    apply intervalIntegral.integral_mono_on hcpos.le
      ((by fun_prop : Continuous (fun s : ℝ => s ^ 2 * Real.exp (-(1/2)))).intervalIntegrable _ _)
      ((cont_ps u).intervalIntegrable _ _)
    intro s hs
    have hsq : s ^ 2 ≤ c ^ 2 := by nlinarith [hs.1, hs.2]
    have hc2 : u * c ^ 2 = 1 := by
      rw [hc]; field_simp; rw [Real.sq_sqrt hu0.le]
    have hle : -(1/2 : ℝ) ≤ -u * s ^ 2 / 2 := by nlinarith [hs.1]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (sq_nonneg s)
  have hval : (∫ s in (0:ℝ)..c, s ^ 2 * Real.exp (-(1/2))) = Real.exp (-(1/2)) * (c ^ 3 / 3) := by
    rw [intervalIntegral.integral_mul_const, integral_pow]; ring
  have hc3 : c ^ 3 / 3 = 1 / (3 * u * Real.sqrt u) := by
    have hs3 : Real.sqrt u ^ 3 = u * Real.sqrt u := by rw [pow_succ, Real.sq_sqrt hu0.le]
    rw [hc, div_pow, one_pow, hs3]; field_simp
  rw [psiN_zero_eq]
  calc Real.exp (-(1/2)) / (3 * u * Real.sqrt u)
      = Real.exp (-(1/2)) * (c ^ 3 / 3) := by rw [hc3]; ring
    _ = ∫ s in (0:ℝ)..c, s ^ 2 * Real.exp (-(1/2)) := hval.symm
    _ ≤ ∫ s in (0:ℝ)..c, s ^ 2 * Real.exp (-u * s ^ 2 / 2) := step2
    _ ≤ ∫ s in (0:ℝ)..1, s ^ 2 * Real.exp (-u * s ^ 2 / 2) := step1

/-! ## Norms of the two pieces of the Leray nonlinearity -/

lemma noGoQ_nonneg (R : ℝ) (y : E3) : 0 ≤ noGoQ R y := by
  rw [noGoQ]; positivity

lemma sqrt_noGoQ (R : ℝ) (y : E3) : Real.sqrt (noGoQ R y) = ‖y - noGoC R‖ := by
  rw [noGoQ, Real.sqrt_sq (norm_nonneg _)]

lemma noGoW_norm (R : ℝ) (y : E3) :
    ‖noGoW R y‖ = 2 * kap ^ 2 * psiN 0 (noGoQ R y) * Real.sqrt (noGoQ R y) := by
  rw [noGoW, norm_smul, Real.norm_eq_abs, sqrt_noGoQ, nsPsi]
  have hpos : 0 < kap ^ 2 * psiN 0 (noGoQ R y) := by
    have := psiN0_pos (noGoQ R y); have := kap_pos; positivity
  have habs : |2 * (-(kap ^ 2) * psiN 0 (noGoQ R y))| = 2 * kap ^ 2 * psiN 0 (noGoQ R y) := by
    rw [abs_of_nonpos (by nlinarith)]
    ring
  rw [habs]

lemma noGoW_norm_le (R : ℝ) (y : E3) : ‖noGoW R y‖ ≤ 4 * kap ^ 2 := by
  rw [noGoW_norm]
  have hq := noGoQ_nonneg R y
  have hk : 0 < kap ^ 2 := by have := kap_pos; positivity
  have hp := psiN0_pos (noGoQ R y)
  have hsn : 0 ≤ Real.sqrt (noGoQ R y) := Real.sqrt_nonneg _
  have hkey : psiN 0 (noGoQ R y) * Real.sqrt (noGoQ R y) ≤ 2 := by
    rcases le_total (noGoQ R y) 1 with h | h
    · have h1 : psiN 0 (noGoQ R y) ≤ 1 / 3 := psiN0_le_third hq
      have h2 : Real.sqrt (noGoQ R y) ≤ 1 := by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt h
      nlinarith
    · have hq1 : 0 < noGoQ R y := lt_of_lt_of_le one_pos h
      have h1 : psiN 0 (noGoQ R y) ≤ 2 / (noGoQ R y) := psiN0_le_two_div hq1
      have hpq : psiN 0 (noGoQ R y) * noGoQ R y ≤ 2 := (le_div_iff₀ hq1).mp h1
      have hs : Real.sqrt (noGoQ R y) * Real.sqrt (noGoQ R y) = noGoQ R y :=
        Real.mul_self_sqrt hq
      have hs1 : 1 ≤ Real.sqrt (noGoQ R y) := by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt h
      nlinarith [mul_nonneg (mul_nonneg hp.le hsn) (by linarith : (0:ℝ) ≤ Real.sqrt (noGoQ R y) - 1)]
  nlinarith [hkey, hk]

lemma noGoAdv_norm_sq (R : ℝ) (y : E3) :
    ‖noGoAdv R y‖ ^ 2 = (noGoN0 R y) ^ 2 + (noGoN1 R y) ^ 2 := by
  rw [noGoAdv, norm_sq_pair]


lemma nsKink_sq_le (R t : ℝ) : (nsKink R t) ^ 2 ≤ 2 * Real.pi := by
  have h := nsKink_abs_le R t
  have h0 : (0:ℝ) ≤ 2 * Real.pi := by positivity
  have hs := Real.sq_sqrt h0
  nlinarith [abs_nonneg (nsKink R t), Real.sqrt_nonneg (2 * Real.pi), sq_abs (nsKink R t)]

lemma nsAl_sq_le_one (t : ℝ) : (nsAl t) ^ 2 ≤ 1 := by
  nlinarith [nsAl_le_one t, (nsAl_pos t).le]

lemma noGoC_norm_sq (R : ℝ) : ‖noGoC R‖ ^ 2 = 2 * R ^ 2 := by
  rw [noGoC, norm_sq_pair]; ring

lemma noGoC_norm_bounds {R : ℝ} (hR : 0 ≤ R) : R ≤ ‖noGoC R‖ ∧ ‖noGoC R‖ ≤ 2 * R := by
  have h := noGoC_norm_sq R
  have hn := norm_nonneg (noGoC R)
  constructor <;> nlinarith

/-- **Near the origin the Leray pressure gradient is only polynomially small.** -/
lemma noGoW_norm_lower_near {R : ℝ} (hR : 2 ≤ R) {y : E3} (hy : ‖y‖ ≤ 1) :
    2 * kap ^ 2 * Real.exp (-(1/2)) / (27 * R ^ 2) ≤ ‖noGoW R y‖ := by
  have hR0 : (0:ℝ) < R := by linarith
  obtain ⟨hc1, hc2⟩ := noGoC_norm_bounds hR0.le
  have hd1 : R - 1 ≤ ‖y - noGoC R‖ := by
    have := norm_sub_norm_le (noGoC R) y
    have h2 : ‖y - noGoC R‖ = ‖noGoC R - y‖ := (norm_sub_rev _ _).symm
    rw [h2]; linarith
  have hd2 : ‖y - noGoC R‖ ≤ 3 * R := by
    have := norm_sub_le y (noGoC R)
    linarith
  have hu1 : 1 ≤ noGoQ R y := by
    rw [noGoQ]; nlinarith [norm_nonneg (y - noGoC R)]
  have hu2 : noGoQ R y ≤ 9 * R ^ 2 := by
    rw [noGoQ]; nlinarith [norm_nonneg (y - noGoC R)]
  have hu0 : (0:ℝ) < noGoQ R y := lt_of_lt_of_le one_pos hu1
  set u := noGoQ R y with hudef
  set s := Real.sqrt u with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hu0
  have hss : s * s = u := Real.mul_self_sqrt hu0.le
  have hlow := psiN0_lower hu1
  have hE : (0:ℝ) < Real.exp (-(1/2)) := Real.exp_pos _
  have hk : (0:ℝ) < kap ^ 2 := by have := kap_pos; positivity
  rw [noGoW_norm, ← hudef, ← hsdef]
  have hstep : Real.exp (-(1/2)) / (3 * u * s) * s = Real.exp (-(1/2)) / (3 * u) := by
    field_simp
  have h1 : 2 * kap ^ 2 * (Real.exp (-(1/2)) / (3 * u)) ≤ 2 * kap ^ 2 * psiN 0 u * s := by
    have hmul : Real.exp (-(1/2)) / (3 * u * s) * s ≤ psiN 0 u * s :=
      mul_le_mul_of_nonneg_right hlow hs0.le
    rw [hstep] at hmul
    nlinarith [hmul]
  have hcmp : 2 * kap ^ 2 * Real.exp (-(1/2)) / (27 * R ^ 2)
      ≤ 2 * kap ^ 2 * (Real.exp (-(1/2)) / (3 * u)) := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 27 * R ^ 2)]
    have hexp : 2 * kap ^ 2 * (Real.exp (-(1/2)) / (3 * u)) * (27 * R ^ 2)
        = (2 * kap ^ 2 * Real.exp (-(1/2))) * (9 * R ^ 2 / u) := by
      field_simp; ring
    rw [hexp]
    have h9 : 1 ≤ 9 * R ^ 2 / u := (one_le_div hu0).mpr (by linarith)
    exact le_mul_of_one_le_right (by positivity) h9
  linarith [hcmp, h1]

/-- Near the origin the advective term is exponentially small. -/
lemma noGoAdv_norm_le_near {R : ℝ} (hR : 2 ≤ R) {y : E3} (hy : ‖y‖ ≤ 1) :
    ‖noGoAdv R y‖ ≤ 4 * kap ^ 2 * Real.exp (-(R - 1) ^ 2 / 2) := by
  have hR0 : (0:ℝ) < R := by linarith
  have hcoord : ∀ i : Fin 3, |y i| ≤ 1 := fun i => le_trans (abs_coord_le_norm y i) hy
  have hg : ∀ i : Fin 3, nsGauss R (y i) ≤ Real.exp (-(R - 1) ^ 2 / 2) := by
    intro i
    rw [nsGauss, Real.exp_le_exp]
    have h := hcoord i
    rw [abs_le] at h
    nlinarith [h.1, h.2]
  have hgpos : ∀ i : Fin 3, 0 < nsGauss R (y i) := fun i => nsGauss_pos R (y i)
  have hE : (0:ℝ) < Real.exp (-(R - 1) ^ 2 / 2) := Real.exp_pos _
  have hk : (0:ℝ) < kap ^ 2 := by have := kap_pos; positivity
  have hbound : ∀ (a b : ℝ), (nsAl (y 2)) ^ 2 ≤ 1 → (nsKink R a) ^ 2 ≤ 2 * Real.pi →
      nsGauss R b ≤ Real.exp (-(R - 1) ^ 2 / 2) → 0 < nsGauss R b →
      (kap ^ 2 * ((nsAl (y 2)) ^ 2 * (nsKink R a * nsGauss R b))) ^ 2
        ≤ kap ^ 4 * (2 * Real.pi) * (Real.exp (-(R - 1) ^ 2 / 2)) ^ 2 := by
    intro a b h1 h2 h3 h4
    have hal : (0:ℝ) ≤ (nsAl (y 2)) ^ 2 := sq_nonneg _
    have hsq : (kap ^ 2 * ((nsAl (y 2)) ^ 2 * (nsKink R a * nsGauss R b))) ^ 2
        = kap ^ 4 * ((nsAl (y 2)) ^ 2) ^ 2 * ((nsKink R a) ^ 2 * (nsGauss R b) ^ 2) := by
      ring
    rw [hsq]
    have hgb : (nsGauss R b) ^ 2 ≤ (Real.exp (-(R - 1) ^ 2 / 2)) ^ 2 := by nlinarith
    have hal2 : ((nsAl (y 2)) ^ 2) ^ 2 ≤ 1 := by nlinarith
    have hA : ((nsAl (y 2)) ^ 2) ^ 2 * ((nsKink R a) ^ 2 * (nsGauss R b) ^ 2)
        ≤ 1 * ((2 * Real.pi) * (Real.exp (-(R - 1) ^ 2 / 2)) ^ 2) := by
      refine mul_le_mul hal2 ?_ (by positivity) (by norm_num)
      exact mul_le_mul h2 hgb (by positivity) (by positivity)
    have hk4 : (0:ℝ) ≤ kap ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hA hk4]
  have h0 := hbound (y 0) (y 1) (nsAl_sq_le_one (y 2)) (nsKink_sq_le R (y 0)) (hg 1) (hgpos 1)
  have h1 := hbound (y 1) (y 0) (nsAl_sq_le_one (y 2)) (nsKink_sq_le R (y 1)) (hg 0) (hgpos 0)
  have hsum : ‖noGoAdv R y‖ ^ 2 ≤ (4 * kap ^ 2 * Real.exp (-(R - 1) ^ 2 / 2)) ^ 2 := by
    rw [noGoAdv_norm_sq, noGoN0, noGoN1]
    have hpi : Real.pi ≤ 4 := Real.pi_le_four
    have hpos : (0:ℝ) ≤ kap ^ 4 * (Real.exp (-(R - 1) ^ 2 / 2)) ^ 2 := by positivity
    nlinarith [h0, h1, hpi, hpos]
  have hb : (0:ℝ) ≤ 4 * kap ^ 2 * Real.exp (-(R - 1) ^ 2 / 2) := by positivity
  have hsq := Real.sqrt_le_sqrt hsum
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hb] at hsq


/-- **The full Leray nonlinearity is polynomially large near the origin.** -/
lemma noGoN_norm_lower_near {R : ℝ} (hR : 30 ≤ R) {y : E3} (hy : ‖y‖ ≤ 1) :
    kap ^ 2 * Real.exp (-(1/2)) / (27 * R ^ 2)
      ≤ ‖noGoAdv R y + noGoW R y‖ := by
  have hR0 : (0:ℝ) < R := by linarith
  have hk : (0:ℝ) < kap ^ 2 := by have := kap_pos; positivity
  have hW := noGoW_norm_lower_near (by linarith : (2:ℝ) ≤ R) hy
  have hA := noGoAdv_norm_le_near (by linarith : (2:ℝ) ≤ R) hy
  have htri : ‖noGoW R y‖ ≤ ‖noGoAdv R y + noGoW R y‖ + ‖noGoAdv R y‖ := by
    calc ‖noGoW R y‖ = ‖(noGoAdv R y + noGoW R y) - noGoAdv R y‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖noGoAdv R y + noGoW R y‖ + ‖noGoAdv R y‖ := norm_sub_le _ _
  -- the advective remainder is beyond all polynomial orders
  have hpoly : (884736 : ℝ) * R ^ 2 ≤ (R - 1) ^ 8 := by
    have h1 : R / 2 ≤ R - 1 := by linarith
    have h2 : (R / 2) ^ 8 ≤ (R - 1) ^ 8 := pow_le_pow_left₀ (by positivity) h1 8
    have h3 : ((30:ℝ)) ^ 6 ≤ R ^ 6 := pow_le_pow_left₀ (by norm_num) hR 6
    have h4 : R ^ 8 = R ^ 6 * R ^ 2 := by ring
    have h5 : (R / 2) ^ 8 = R ^ 8 / 256 := by ring
    rw [h5] at h2
    nlinarith [sq_nonneg R, h3, h4]
  have hexp : Real.exp (-(R - 1) ^ 2 / 2) ≤ 4096 / (R - 1) ^ 8 := by
    have hpos : (0:ℝ) < (R - 1) ^ 2 / 2 := by nlinarith
    have := exp_neg_le_inv_pow4 hpos
    have heq : -((R - 1) ^ 2 / 2) = -(R - 1) ^ 2 / 2 := by ring
    rw [heq] at this
    refine le_trans this ?_
    have h8 : ((R - 1) ^ 2 / 2) ^ 4 = (R - 1) ^ 8 / 16 := by ring
    rw [h8]
    have hRm : (0:ℝ) < R - 1 := by linarith
    rw [div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity : (0:ℝ) < (R-1)^8)]
    ring_nf
    nlinarith [pow_pos (by linarith : (0:ℝ) < R - 1) 8]
  have hEhalf : (1:ℝ) / 2 ≤ Real.exp (-(1/2)) := half_le_exp_neg_half
  have hsmall : 4 * kap ^ 2 * Real.exp (-(R - 1) ^ 2 / 2)
      ≤ kap ^ 2 * Real.exp (-(1/2)) / (27 * R ^ 2) := by
    have hden : (0:ℝ) < 27 * R ^ 2 := by positivity
    rw [le_div_iff₀ hden]
    have hstep : 4 * kap ^ 2 * Real.exp (-(R - 1) ^ 2 / 2) * (27 * R ^ 2)
        ≤ 4 * kap ^ 2 * (4096 / (R - 1) ^ 8) * (27 * R ^ 2) := by
      have := mul_le_mul_of_nonneg_left hexp (by positivity : (0:ℝ) ≤ 4 * kap ^ 2)
      nlinarith [sq_nonneg R, hk]
    refine le_trans hstep ?_
    have hRm : (0:ℝ) < R - 1 := by linarith
    have hr8 : (0:ℝ) < (R - 1) ^ 8 := by positivity
    have hval : 4 * kap ^ 2 * (4096 / (R - 1) ^ 8) * (27 * R ^ 2)
        = kap ^ 2 * (442368 * R ^ 2 / (R - 1) ^ 8) := by
      field_simp; ring
    rw [hval]
    have hfrac : 442368 * R ^ 2 / (R - 1) ^ 8 ≤ 1 / 2 := by
      rw [div_le_iff₀ hr8]
      linarith [hpoly]
    calc kap ^ 2 * (442368 * R ^ 2 / (R - 1) ^ 8) ≤ kap ^ 2 * (1 / 2) :=
          mul_le_mul_of_nonneg_left hfrac hk.le
      _ ≤ kap ^ 2 * Real.exp (-(1/2)) := mul_le_mul_of_nonneg_left hEhalf hk.le
  have hhalf : kap ^ 2 * Real.exp (-(1/2)) / (27 * R ^ 2)
      = 2 * kap ^ 2 * Real.exp (-(1/2)) / (27 * R ^ 2)
        - kap ^ 2 * Real.exp (-(1/2)) / (27 * R ^ 2) := by ring
  rw [hhalf]
  linarith [hW, hA, htri, hsmall]

/-! ## The Gaussian-weighted Dirichlet energy of the translated field -/

/-- The decay exponent of the translated field's Dirichlet bill. -/
def lamNu (nu : ℝ) : ℝ := min (1/4) (min (1/(32*nu)) (1/(1+8*nu)))

lemma lamNu_pos {nu : ℝ} (hnu : 0 < nu) : 0 < lamNu nu := by
  rw [lamNu]
  refine lt_min (by norm_num) (lt_min (by positivity) (by positivity))

lemma lamNu_le_quarter (nu : ℝ) : lamNu nu ≤ 1/4 := min_le_left _ _

lemma lamNu_le_a (nu : ℝ) : lamNu nu ≤ 1/(32*nu) :=
  le_trans (min_le_right _ _) (min_le_left _ _)

lemma lamNu_le_b (nu : ℝ) : lamNu nu ≤ 1/(1+8*nu) :=
  le_trans (min_le_right _ _) (min_le_right _ _)

/-- The total Dirichlet bill of the translated field. -/
def bigB (nu R : ℝ) : ℝ := kap ^ 2 * (2 + R ^ 2 / 4 + 2 * Real.pi) * Real.exp (-(lamNu nu) * R ^ 2)

lemma gaussWeight_ratio {nu : ℝ} (hnu : 0 < nu) (y : E3) :
    gaussWeight nu y = gaussWeight (2*nu) y * Real.exp (-‖y‖ ^ 2 / (8*nu)) := by
  rw [gaussWeight, gaussWeight, ← Real.exp_add]
  congr 1
  field_simp
  ring

lemma nsGauss_sq (R t : ℝ) : (nsGauss R t) ^ 2 = Real.exp (-(t - R) ^ 2) := by
  rw [nsGauss, sq, ← Real.exp_add]
  congr 1
  ring

lemma coord_sq_le (y : E3) (i : Fin 3) : (y i) ^ 2 ≤ ‖y‖ ^ 2 := by
  have h := abs_coord_le_norm y i
  nlinarith [abs_nonneg (y i), norm_nonneg y, sq_abs (y i)]


/-- The shear part of the Dirichlet density is exponentially small in `R`. -/
lemma gauss_term_bound {nu R : ℝ} (hnu : 0 < nu) (y : E3) (i : Fin 3) :
    (kap * (nsAl (y 2) * nsGauss R (y i))) ^ 2 * Real.exp (-‖y‖ ^ 2 / (8*nu))
      ≤ kap ^ 2 * Real.exp (-(lamNu nu) * R ^ 2) := by
  have hk : (0:ℝ) < kap ^ 2 := by have := kap_pos; positivity
  have hE1 : Real.exp (-‖y‖ ^ 2 / (8*nu)) ≤ Real.exp (-(y i) ^ 2 / (8*nu)) := by
    apply Real.exp_le_exp.mpr
    have h := coord_sq_le y i
    rw [div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < 8*nu)]
    linarith
  have hquad : Real.exp (-((y i - R) ^ 2 + (y i) ^ 2 / (8*nu)))
      ≤ Real.exp (-(lamNu nu) * R ^ 2) := by
    apply Real.exp_le_exp.mpr
    have ha : (0:ℝ) < 1/(8*nu) := by positivity
    have hq := quad_split (a := 1/(8*nu)) (t := y i) (R := R) ha
    have heq : (1/(8*nu)) * R ^ 2 / (1 + 1/(8*nu)) = R ^ 2 / (1 + 8*nu) := by
      field_simp; ring
    rw [heq] at hq
    have hq2 : (1/(8*nu)) * (y i) ^ 2 = (y i) ^ 2 / (8*nu) := by ring
    rw [hq2] at hq
    have hlam : lamNu nu * R ^ 2 ≤ R ^ 2 / (1 + 8*nu) := by
      have := lamNu_le_b nu
      have hd : R ^ 2 / (1 + 8*nu) = (1/(1+8*nu)) * R ^ 2 := by ring
      rw [hd]
      exact mul_le_mul_of_nonneg_right this (sq_nonneg R)
    linarith
  calc (kap * (nsAl (y 2) * nsGauss R (y i))) ^ 2 * Real.exp (-‖y‖ ^ 2 / (8*nu))
      = kap ^ 2 * (nsAl (y 2)) ^ 2 * ((nsGauss R (y i)) ^ 2
          * Real.exp (-‖y‖ ^ 2 / (8*nu))) := by ring
    _ ≤ kap ^ 2 * 1 * ((nsGauss R (y i)) ^ 2 * Real.exp (-‖y‖ ^ 2 / (8*nu))) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        nlinarith [nsAl_sq_le_one (y 2), hk]
    _ = kap ^ 2 * (Real.exp (-(y i - R) ^ 2) * Real.exp (-‖y‖ ^ 2 / (8*nu))) := by
        rw [nsGauss_sq]; ring
    _ ≤ kap ^ 2 * (Real.exp (-(y i - R) ^ 2) * Real.exp (-(y i) ^ 2 / (8*nu))) := by
        refine mul_le_mul_of_nonneg_left ?_ hk.le
        exact mul_le_mul_of_nonneg_left hE1 (Real.exp_pos _).le
    _ = kap ^ 2 * Real.exp (-((y i - R) ^ 2 + (y i) ^ 2 / (8*nu))) := by
        rw [← Real.exp_add]; congr 2; ring
    _ ≤ kap ^ 2 * Real.exp (-(lamNu nu) * R ^ 2) := mul_le_mul_of_nonneg_left hquad hk.le

/-- The kink part of the Dirichlet density is small in `R` too: near the origin
the shear profile has not yet switched on, and far from the origin the Gaussian
weight has already died. -/
lemma kink_term_bound {nu R : ℝ} (hnu : 0 < nu) (hR : 0 < R) (y : E3) (i : Fin 3) :
    (kap * (nsKink R (y i) * (-(y 2 / 2) * nsAl (y 2)))) ^ 2 * Real.exp (-‖y‖ ^ 2 / (8*nu))
      ≤ kap ^ 2 * (R ^ 2 / 8 + Real.pi) * Real.exp (-(lamNu nu) * R ^ 2) := by
  have hk : (0:ℝ) < kap ^ 2 := by have := kap_pos; positivity
  have hX : (0:ℝ) < Real.exp (-(lamNu nu) * R ^ 2) := Real.exp_pos _
  have hEpos : (0:ℝ) < Real.exp (-‖y‖ ^ 2 / (8*nu)) := Real.exp_pos _
  have hE1 : Real.exp (-‖y‖ ^ 2 / (8*nu)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : (0:ℝ) ≤ ‖y‖ ^ 2 := sq_nonneg _
    have h8 : (0:ℝ) < 8*nu := by positivity
    rw [div_nonpos_iff]
    right
    constructor <;> [linarith; linarith]
  have hd := nsAl_deriv_sq_le (y 2)
  have hfac : (kap * (nsKink R (y i) * (-(y 2 / 2) * nsAl (y 2)))) ^ 2
      * Real.exp (-‖y‖ ^ 2 / (8*nu))
      = kap ^ 2 * ((nsKink R (y i)) ^ 2 * ((-(y 2 / 2) * nsAl (y 2)) ^ 2
          * Real.exp (-‖y‖ ^ 2 / (8*nu)))) := by ring
  rcases le_total |y i| (R / 2) with hcase | hcase
  · have hnear := nsKink_abs_le_near hR hcase
    have hsq : (nsKink R (y i)) ^ 2 ≤ (R ^ 2 / 4) * Real.exp (-R ^ 2 / 4) := by
      have h2 : ((R / 2) * Real.exp (-R ^ 2 / 8)) ^ 2 = (R ^ 2 / 4) * Real.exp (-R ^ 2 / 4) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        · ring
        · push_cast; ring
      nlinarith [abs_nonneg (nsKink R (y i)), sq_abs (nsKink R (y i)),
        mul_nonneg (by positivity : (0:ℝ) ≤ R/2) (Real.exp_pos (-R^2/8)).le]
    have hdecay : Real.exp (-R ^ 2 / 4) ≤ Real.exp (-(lamNu nu) * R ^ 2) := by
      apply Real.exp_le_exp.mpr
      have := lamNu_le_quarter nu
      nlinarith [sq_nonneg R]
    rw [hfac]
    have hinner : (nsKink R (y i)) ^ 2 * ((-(y 2 / 2) * nsAl (y 2)) ^ 2
        * Real.exp (-‖y‖ ^ 2 / (8*nu)))
        ≤ ((R ^ 2 / 4) * Real.exp (-(lamNu nu) * R ^ 2)) * (1/2 * 1) := by
      refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
      · exact le_trans hsq (by nlinarith [hdecay, sq_nonneg R])
      · exact mul_le_mul hd hE1 hEpos.le (by norm_num)
    have : kap ^ 2 * ((nsKink R (y i)) ^ 2 * ((-(y 2 / 2) * nsAl (y 2)) ^ 2
        * Real.exp (-‖y‖ ^ 2 / (8*nu))))
        ≤ kap ^ 2 * (((R ^ 2 / 4) * Real.exp (-(lamNu nu) * R ^ 2)) * (1/2 * 1)) :=
      mul_le_mul_of_nonneg_left hinner hk.le
    refine le_trans this ?_
    nlinarith [mul_nonneg (mul_nonneg hk.le hX.le) Real.pi_pos.le]
  · have hsq := nsKink_sq_le R (y i)
    have hEfar : Real.exp (-‖y‖ ^ 2 / (8*nu)) ≤ Real.exp (-(lamNu nu) * R ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hy2 : (R / 2) ^ 2 ≤ (y i) ^ 2 := by
        nlinarith [abs_nonneg (y i), sq_abs (y i)]
      have hyn : (y i) ^ 2 ≤ ‖y‖ ^ 2 := coord_sq_le y i
      have hla := lamNu_le_a nu
      have h8 : (0:ℝ) < 8*nu := by positivity
      have hstep : lamNu nu * R ^ 2 ≤ ‖y‖ ^ 2 / (8*nu) := by
        have h1 : lamNu nu * R ^ 2 ≤ (1/(32*nu)) * R ^ 2 :=
          mul_le_mul_of_nonneg_right hla (sq_nonneg R)
        have h2 : (1/(32*nu)) * R ^ 2 = (R/2) ^ 2 / (8*nu) := by
          field_simp; ring
        have h3 : (R/2) ^ 2 / (8*nu) ≤ ‖y‖ ^ 2 / (8*nu) := by
          exact div_le_div_of_nonneg_right (hy2.trans hyn) h8.le
        rw [h2] at h1
        linarith
      have hneg : -‖y‖ ^ 2 / (8*nu) = -(‖y‖ ^ 2 / (8*nu)) := by ring
      rw [hneg]
      linarith
    rw [hfac]
    have hinner : (nsKink R (y i)) ^ 2 * ((-(y 2 / 2) * nsAl (y 2)) ^ 2
        * Real.exp (-‖y‖ ^ 2 / (8*nu)))
        ≤ (2 * Real.pi) * (1/2 * Real.exp (-(lamNu nu) * R ^ 2)) := by
      refine mul_le_mul hsq ?_ (by positivity) (by positivity)
      exact mul_le_mul hd hEfar hEpos.le (by positivity)
    have := mul_le_mul_of_nonneg_left hinner hk.le
    refine le_trans this ?_
    nlinarith [mul_nonneg (mul_nonneg hk.le (sq_nonneg R)) hX.le]

/-- **The Dirichlet bill of the translated field is exponentially small.** -/
lemma noGo_gradSq_bound {nu R : ℝ} (hnu : 0 < nu) (hR : 0 < R) (y : E3) :
    gaussWeight nu y * gradSqSpace (noGoV R) y ≤ bigB nu R * gaussWeight (2*nu) y := by
  have hw : (0:ℝ) < gaussWeight (2*nu) y := Real.exp_pos _
  have h1 := gauss_term_bound (R := R) hnu y 0
  have h2 := gauss_term_bound (R := R) hnu y 1
  have h3 := kink_term_bound hnu hR y 1
  have h4 := kink_term_bound hnu hR y 0
  have hsum : gradSqSpace (noGoV R) y * Real.exp (-‖y‖ ^ 2 / (8*nu)) ≤ bigB nu R := by
    rw [noGoV_gradSq, bigB, add_mul, add_mul, add_mul]
    have := Real.exp_pos (-(lamNu nu) * R ^ 2)
    nlinarith [h1, h2, h3, h4]
  rw [gaussWeight_ratio hnu y]
  have : gaussWeight (2*nu) y * Real.exp (-‖y‖ ^ 2 / (8*nu)) * gradSqSpace (noGoV R) y
      = gaussWeight (2*nu) y * (gradSqSpace (noGoV R) y * Real.exp (-‖y‖ ^ 2 / (8*nu))) := by
    ring
  rw [this, mul_comm (bigB nu R)]
  exact mul_le_mul_of_nonneg_left hsum hw.le


/-! ## Integrability and the two integral estimates -/

/-- The Gaussian weight is integrable on `E3` for every positive parameter. -/
lemma integrable_gaussWeight {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : E3 => gaussWeight c y) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace
    (b := ((1/(4*c) : ℝ) : ℂ)) (ι := Fin 3) (by simpa using (by positivity : (0:ℝ) < 1/(4*c))) 0 0
  refine h.re.congr ?_
  filter_upwards with y
  simp [gaussWeight, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_neg,
    Complex.exp_ofReal_re]
  ring_nf

/-- The total Gaussian mass `∫ ρ_{2ν}`. -/
def gaussMass (nu : ℝ) : ℝ := ∫ y : E3, gaussWeight (2*nu) y

lemma gaussMass_pos {nu : ℝ} (hnu : 0 < nu) : 0 < gaussMass nu := by
  have hint := integrable_gaussWeight (c := 2*nu) (by positivity)
  refine (integral_pos_iff_support_of_nonneg ?_ hint).mpr ?_
  · intro y; exact (Real.exp_pos _).le
  · have hsupp : Function.support (fun y : E3 => gaussWeight (2*nu) y) = Set.univ := by
      ext y; simp [gaussWeight, Function.support, Real.exp_ne_zero]
    rw [hsupp]; simp

/-- Volume of the unit ball of `E3`. -/
def nsBallVol : ℝ := (volume : Measure E3).real (Metric.ball (0:E3) 1)

lemma nsBallVol_pos : 0 < nsBallVol := by
  rw [nsBallVol, Measure.real, ENNReal.toReal_pos_iff]
  exact ⟨Metric.measure_ball_pos _ _ one_pos, measure_ball_lt_top⟩

lemma continuous_noGoAdv (R : ℝ) : Continuous (noGoAdv R) := by
  have hA : Continuous nsAl := contDiff_nsAl.continuous
  have hK : Continuous (nsKink R) := (contDiff_nsKink R).continuous
  have hG : Continuous (nsGauss R) := (contDiff_nsGauss R).continuous
  unfold noGoAdv noGoN0 noGoN1
  fun_prop

lemma continuous_noGoW (R : ℝ) : Continuous (noGoW R) := by
  have hP : Continuous nsPsi := continuous_nsPsi
  have hQ : Continuous (noGoQ R) := (contDiff_noGoQ R).continuous
  unfold noGoW
  fun_prop

lemma continuous_noGoGradSq (R : ℝ) : Continuous (gradSqSpace (noGoV R)) := by
  have hA : Continuous nsAl := contDiff_nsAl.continuous
  have hK : Continuous (nsKink R) := (contDiff_nsKink R).continuous
  have hG : Continuous (nsGauss R) := (contDiff_nsGauss R).continuous
  simp only [funext (noGoV_gradSq R)]
  fun_prop

lemma continuous_gaussWeight (c : ℝ) : Continuous (gaussWeight c) := by
  unfold gaussWeight; fun_prop

/-- A crude global bound on the advective part of the source. -/
lemma noGoAdv_norm_le (R : ℝ) (y : E3) : ‖noGoAdv R y‖ ≤ 6 * kap ^ 2 := by
  have hk : (0:ℝ) < kap := kap_pos
  have hsq : ‖noGoAdv R y‖ ^ 2 ≤ (6 * kap ^ 2) ^ 2 := by
    rw [noGoAdv_norm_sq]
    have b : ∀ a b : ℝ, (kap ^ 2 * ((nsAl (y 2)) ^ 2 * (nsKink R a * nsGauss R b))) ^ 2
        ≤ kap ^ 4 * (2 * Real.pi) := by
      intro a b
      have h1 := nsAl_sq_le_one (y 2)
      have h2 := nsKink_sq_le R a
      have h3 : (nsGauss R b) ^ 2 ≤ 1 := by
        nlinarith [nsGauss_le_one R b, (nsGauss_pos R b).le]
      have hexp : (kap ^ 2 * ((nsAl (y 2)) ^ 2 * (nsKink R a * nsGauss R b))) ^ 2
          = kap ^ 4 * (((nsAl (y 2)) ^ 2) ^ 2 * ((nsKink R a) ^ 2 * (nsGauss R b) ^ 2)) := by
        ring
      rw [hexp]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hA : ((nsAl (y 2)) ^ 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (nsAl (y 2))]
      have hB : (nsKink R a) ^ 2 * (nsGauss R b) ^ 2 ≤ 2 * Real.pi := by
        nlinarith [sq_nonneg (nsKink R a), sq_nonneg (nsGauss R b)]
      nlinarith [sq_nonneg ((nsAl (y 2)) ^ 2),
        mul_nonneg (sq_nonneg (nsKink R a)) (sq_nonneg (nsGauss R b)), Real.pi_pos]
    have hb0 := b (y 0) (y 1)
    have hb1 := b (y 1) (y 0)
    unfold noGoN0 noGoN1
    have hpi : Real.pi ≤ 4 := Real.pi_le_four
    nlinarith [hb0, hb1, sq_nonneg kap, pow_pos hk 4]
  nlinarith [norm_nonneg (noGoAdv R y), hsq, sq_nonneg kap]

/-- A crude global bound on the full Leray source. -/
lemma noGoN_norm_le (R : ℝ) (y : E3) : ‖noGoAdv R y + noGoW R y‖ ≤ 10 * kap ^ 2 := by
  have h1 := noGoAdv_norm_le R y
  have h2 := noGoW_norm_le R y
  have h3 := norm_add_le (noGoAdv R y) (noGoW R y)
  linarith

lemma integrable_noGo_source {nu R : ℝ} (hnu : 0 < nu) :
    Integrable (fun y : E3 => gaussWeight (2*nu) y * ‖noGoAdv R y + noGoW R y‖ ^ 2) := by
  have hg := integrable_gaussWeight (c := 2*nu) (by positivity)
  refine Integrable.mono' (hg.const_mul ((10 * kap ^ 2) ^ 2)) ?_ (Filter.Eventually.of_forall ?_)
  · exact ((continuous_gaussWeight (2*nu)).mul
      (((continuous_noGoAdv R).add (continuous_noGoW R)).norm.pow 2)).aestronglyMeasurable
  · intro y
    have hw : (0:ℝ) < gaussWeight (2*nu) y := Real.exp_pos _
    have hn := noGoN_norm_le R y
    have hn0 := norm_nonneg (noGoAdv R y + noGoW R y)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hsq : ‖noGoAdv R y + noGoW R y‖ ^ 2 ≤ (10 * kap ^ 2) ^ 2 :=
      pow_le_pow_left₀ hn0 hn 2
    exact (mul_le_mul_of_nonneg_left hsq hw.le).trans_eq (by ring)

/-- **RHS.** The Gaussian Dirichlet energy of the translated field is exponentially small. -/
lemma noGo_dirichlet_integral_bound {nu R : ℝ} (hnu : 0 < nu) (hR : 0 < R) :
    (∫ y : E3, gaussWeight nu y * gradSqSpace (noGoV R) y) ≤ bigB nu R * gaussMass nu := by
  have hg := integrable_gaussWeight (c := 2*nu) (by positivity)
  have hgB : Integrable (fun y : E3 => bigB nu R * gaussWeight (2*nu) y) := hg.const_mul _
  have hmeas : AEStronglyMeasurable (fun y : E3 => gaussWeight nu y * gradSqSpace (noGoV R) y)
      volume :=
    ((continuous_gaussWeight nu).mul (continuous_noGoGradSq R)).aestronglyMeasurable
  have hbd : ∀ y : E3, ‖gaussWeight nu y * gradSqSpace (noGoV R) y‖
      ≤ bigB nu R * gaussWeight (2*nu) y := by
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      have hp : (0:ℝ) < gaussWeight nu y := Real.exp_pos _
      exact mul_nonneg hp.le (gradSqSpace_nonneg (noGoV R) y))]
    exact noGo_gradSq_bound hnu hR y
  have hint : Integrable (fun y : E3 => gaussWeight nu y * gradSqSpace (noGoV R) y) :=
    Integrable.mono' hgB hmeas (Filter.Eventually.of_forall hbd)
  calc (∫ y : E3, gaussWeight nu y * gradSqSpace (noGoV R) y)
      ≤ ∫ y : E3, bigB nu R * gaussWeight (2*nu) y :=
        integral_mono hint hgB (fun y => le_trans (le_abs_self _) (by
          simpa [Real.norm_eq_abs] using hbd y))
    _ = bigB nu R * gaussMass nu := by
        rw [MeasureTheory.integral_const_mul, gaussMass]

/-- **LHS.** The Leray source is polynomially large inside the Gaussian core. -/
lemma noGo_source_integral_lower {nu R : ℝ} (hnu : 0 < nu) (hR : 30 ≤ R) :
    Real.exp (-(1/(8*nu))) * (kap ^ 2 * Real.exp (-(1/2)) / 27) ^ 2 * nsBallVol / R ^ 4
      ≤ ∫ y : E3, gaussWeight (2*nu) y * ‖noGoAdv R y + noGoW R y‖ ^ 2 := by
  have hR0 : (0:ℝ) < R := by linarith
  set m : ℝ := Real.exp (-(1/(8*nu))) * (kap ^ 2 * Real.exp (-(1/2)) / (27 * R ^ 2)) ^ 2 with hm
  have hind : Integrable (Set.indicator (Metric.ball (0:E3) 1) (fun _ => m)) :=
    (integrable_indicator_iff measurableSet_ball).mpr
      (integrableOn_const (by exact measure_ball_lt_top.ne))
  have hsrc := integrable_noGo_source (nu := nu) (R := R) hnu
  have hpt : ∀ y : E3, Set.indicator (Metric.ball (0:E3) 1) (fun _ => m) y
      ≤ gaussWeight (2*nu) y * ‖noGoAdv R y + noGoW R y‖ ^ 2 := by
    intro y
    by_cases hy : y ∈ Metric.ball (0:E3) 1
    · rw [Set.indicator_of_mem hy]
      have hyn : ‖y‖ ≤ 1 := by
        have := mem_ball_zero_iff.mp hy; linarith
      have hwl : Real.exp (-(1/(8*nu))) ≤ gaussWeight (2*nu) y := by
        rw [gaussWeight]
        apply Real.exp_le_exp.mpr
        have hs : ‖y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y]
        have hle : ‖y‖ ^ 2 / (4*(2*nu)) ≤ 1 / (8*nu) := by
          have h4 : (4:ℝ)*(2*nu) = 8*nu := by ring
          rw [h4]
          exact div_le_div_of_nonneg_right hs (by positivity)
        have heq : -(‖y‖ ^ 2) / (4*(2*nu)) = -(‖y‖ ^ 2 / (4*(2*nu))) := by ring
        rw [heq]; linarith
      have hlow := noGoN_norm_lower_near hR hyn
      have hlow0 : (0:ℝ) ≤ kap ^ 2 * Real.exp (-(1/2)) / (27 * R ^ 2) := by
        have := kap_pos; positivity
      have hsq : (kap ^ 2 * Real.exp (-(1/2)) / (27 * R ^ 2)) ^ 2
          ≤ ‖noGoAdv R y + noGoW R y‖ ^ 2 := pow_le_pow_left₀ hlow0 hlow 2
      rw [hm]
      exact mul_le_mul hwl hsq (by positivity) (le_trans (Real.exp_pos _).le hwl)
    · rw [Set.indicator_of_notMem hy]
      exact mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hmono := integral_mono hind hsrc hpt
  refine le_trans ?_ hmono
  rw [integral_indicator_const _ measurableSet_ball, nsBallVol, smul_eq_mul, hm]
  apply le_of_eq
  field_simp

/-! ## The pressure gauge -/

lemma noGoP_gradSpace_eq (R : ℝ) (y : E3) : gradSpace (noGoP R) y = noGoW R y :=
  (noGoP_gradSpace R y).trans (by rw [noGoW])

/-- The counterexample pressure is normalised: its gradient vanishes at infinity, so `P` is the
genuine Leray pressure and not an arbitrary harmonic modification. -/
lemma noGoP_gradient_tendsto_zero (R : ℝ) :
    Filter.Tendsto (fun y : E3 => ‖gradSpace (noGoP R) y‖) (Filter.cocompact E3) (nhds 0) := by
  have hk : (0:ℝ) < kap ^ 2 := by have := kap_pos; positivity
  have hnorm : Filter.Tendsto (fun y : E3 => ‖y‖) (Filter.cocompact E3) Filter.atTop :=
    tendsto_norm_cocompact_atTop
  have hshift : Filter.Tendsto (fun y : E3 => ‖y‖ - ‖noGoC R‖) (Filter.cocompact E3)
      Filter.atTop :=
    (Filter.tendsto_atTop_add_const_right _ (-‖noGoC R‖) hnorm).congr (fun y => by ring)
  have hlim : Filter.Tendsto (fun y : E3 => 4 * kap ^ 2 / (‖y‖ - ‖noGoC R‖))
      (Filter.cocompact E3) (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hshift
  refine squeeze_zero' (Filter.Eventually.of_forall fun y => norm_nonneg _) ?_ hlim
  filter_upwards [hshift.eventually_gt_atTop 0] with y hy
  have hdist : ‖y‖ - ‖noGoC R‖ ≤ ‖y - noGoC R‖ := norm_sub_norm_le _ _
  have hd0 : (0:ℝ) < ‖y - noGoC R‖ := lt_of_lt_of_le hy hdist
  have hq : (0:ℝ) < noGoQ R y := by rw [noGoQ]; positivity
  rw [noGoP_gradSpace_eq, noGoW_norm, sqrt_noGoQ]
  have hpsi : psiN 0 (noGoQ R y) ≤ 2 / (noGoQ R y) := psiN0_le_two_div hq
  have hqe : noGoQ R y = ‖y - noGoC R‖ ^ 2 := rfl
  have hstep : 2 * kap ^ 2 * psiN 0 (noGoQ R y) * ‖y - noGoC R‖
      ≤ 4 * kap ^ 2 / ‖y - noGoC R‖ := by
    rw [hqe] at hpsi
    have h1 : 2 * kap ^ 2 * psiN 0 (noGoQ R y) * ‖y - noGoC R‖
        ≤ 2 * kap ^ 2 * (2 / ‖y - noGoC R‖ ^ 2) * ‖y - noGoC R‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpsi (by positivity)) hd0.le
    refine h1.trans (le_of_eq ?_)
    field_simp; ring
  exact hstep.trans (div_le_div_of_nonneg_left (by positivity) hy hdist)

/-! ## The no-go theorem -/

/-- **The global Gaussian Leray estimate is false.**

There is no finite constant `C` for which

  `‖ℙ∇·(V⊗V)‖_{L²(ρ_{2ν})} ≤ C ‖V‖_∞ ‖∇V‖_{L²(ρ_ν)}`

holds for all smooth, divergence-free, record-normalised (`‖V‖_∞ ≤ 1`) fields `V` with their
Leray pressure `P` (normalised by `∇P → 0` at infinity).

The witnesses are the translated crossed shears `noGoV R`: the Gaussian Dirichlet bill on the
right decays like `e^{−λ_ν R²}`, while the nonlocal Leray pressure still contributes
`≳ R^{-2}` at the Gaussian centre, so the ratio blows up as `R → ∞`. -/
theorem gaussian_leray_global_no_go {nu : ℝ} (hnu : 0 < nu) :
    ¬ ∃ C : ℝ, ∀ (V : E3 → E3) (P : E3 → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) V → ContDiff ℝ (⊤ : ℕ∞) P →
        (∀ y, divSpace V y = 0) → (∀ y, ‖V y‖ ≤ 1) →
        (∀ y, divSpace (fun x => advSpace V x + gradSpace P x) y = 0) →
        Filter.Tendsto (fun y : E3 => ‖gradSpace P y‖) (Filter.cocompact E3) (nhds 0) →
        (∫ y : E3, gaussWeight (2*nu) y * ‖advSpace V y + gradSpace P y‖ ^ 2)
          ≤ C ^ 2 * ∫ y : E3, gaussWeight nu y * gradSqSpace V y := by
  rintro ⟨C, hC⟩
  have hk : (0:ℝ) < kap ^ 2 := by have := kap_pos; positivity
  set A : ℝ := Real.exp (-(1/(8*nu))) * (kap ^ 2 * Real.exp (-(1/2)) / 27) ^ 2 * nsBallVol
    with hAdef
  have hA : 0 < A := by
    rw [hAdef]; have := nsBallVol_pos; positivity
  set G : ℝ := gaussMass nu with hGdef
  have hG : 0 < G := gaussMass_pos hnu
  set lam : ℝ := lamNu nu with hlamdef
  have hlam : 0 < lam := lamNu_pos hnu
  set D : ℝ := 256 * C ^ 2 * kap ^ 2 * G / lam ^ 4 with hDdef
  have hD : 0 ≤ D := by rw [hDdef]; positivity
  have key : ∀ R : ℝ, 30 ≤ R → A * R ^ 2 ≤ D := by
    intro R hR
    have hR0 : (0:ℝ) < R := by linarith
    have h1 := noGo_source_integral_lower (nu := nu) (R := R) hnu hR
    have h2 := hC (noGoV R) (noGoP R) (noGoV_contDiff R) (noGoP_contDiff R)
      (noGoV_divSpace R) (noGoV_norm_le_one R) (noGo_pressure_poisson R)
      (noGoP_gradient_tendsto_zero R)
    simp only [noGoV_advSpace, noGoP_gradSpace_eq] at h2
    have h3 := noGo_dirichlet_integral_bound (nu := nu) (R := R) hnu hR0
    have hC2 : (0:ℝ) ≤ C ^ 2 := sq_nonneg C
    have h4 : (∫ y : E3, gaussWeight (2*nu) y * ‖noGoAdv R y + noGoW R y‖ ^ 2)
        ≤ C ^ 2 * (bigB nu R * G) :=
      h2.trans (mul_le_mul_of_nonneg_left h3 hC2)
    -- the exponential Dirichlet bill beats every polynomial
    have hbig : bigB nu R ≤ 256 * kap ^ 2 / (lam ^ 4 * R ^ 6) := by
      have hpoly : 2 + R ^ 2 / 4 + 2 * Real.pi ≤ R ^ 2 := by
        have hpi : Real.pi ≤ 4 := Real.pi_le_four
        nlinarith [hR]
      have ht : (0:ℝ) < lam * R ^ 2 := by positivity
      have hexp : Real.exp (-(lam * R ^ 2)) ≤ 256 / (lam * R ^ 2) ^ 4 := exp_neg_le_inv_pow4 ht
      have hexp' : Real.exp (-lam * R ^ 2) ≤ 256 / (lam ^ 4 * R ^ 8) := by
        have heq1 : -lam * R ^ 2 = -(lam * R ^ 2) := by ring
        have heq2 : (lam * R ^ 2) ^ 4 = lam ^ 4 * R ^ 8 := by ring
        rw [heq1, ← heq2]; exact hexp
      have hE : (0:ℝ) < Real.exp (-lam * R ^ 2) := Real.exp_pos _
      calc bigB nu R = kap ^ 2 * (2 + R ^ 2 / 4 + 2 * Real.pi) * Real.exp (-lam * R ^ 2) := by
            rw [bigB, hlamdef]
        _ ≤ kap ^ 2 * R ^ 2 * Real.exp (-lam * R ^ 2) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpoly hk.le) hE.le
        _ ≤ kap ^ 2 * R ^ 2 * (256 / (lam ^ 4 * R ^ 8)) :=
            mul_le_mul_of_nonneg_left hexp' (by positivity)
        _ = 256 * kap ^ 2 / (lam ^ 4 * R ^ 6) := by
            field_simp
    have h5 : C ^ 2 * (bigB nu R * G) ≤ D / R ^ 6 := by
      have := mul_le_mul_of_nonneg_right hbig hG.le
      have h6 : C ^ 2 * (bigB nu R * G) ≤ C ^ 2 * (256 * kap ^ 2 / (lam ^ 4 * R ^ 6) * G) :=
        mul_le_mul_of_nonneg_left this hC2
      refine h6.trans (le_of_eq ?_)
      rw [hDdef]; field_simp
    have h7 : A / R ^ 4 ≤ D / R ^ 6 := by
      rw [hAdef]
      exact h1.trans (h4.trans h5)
    have h8 : A * R ^ 6 ≤ D * R ^ 4 :=
      (div_le_div_iff₀ (by positivity) (by positivity)).mp h7
    nlinarith [pow_pos hR0 4, pow_pos hR0 2, h8]
  -- contradiction: `A R² ≤ D` cannot hold for all large `R`
  set R : ℝ := max 30 (Real.sqrt (D / A) + 1) with hRdef
  have hR30 : 30 ≤ R := le_max_left _ _
  have hRs : Real.sqrt (D / A) + 1 ≤ R := le_max_right _ _
  have hDA : 0 ≤ D / A := div_nonneg hD hA.le
  have hsq : Real.sqrt (D / A) ^ 2 = D / A := Real.sq_sqrt hDA
  have hlt : D / A < R ^ 2 := by
    have h1 : 0 ≤ Real.sqrt (D / A) := Real.sqrt_nonneg _
    nlinarith [hsq, hRs, h1]
  have := key R hR30
  rw [div_lt_iff₀ hA] at hlt
  nlinarith [this, hlt]

end ClayNS
