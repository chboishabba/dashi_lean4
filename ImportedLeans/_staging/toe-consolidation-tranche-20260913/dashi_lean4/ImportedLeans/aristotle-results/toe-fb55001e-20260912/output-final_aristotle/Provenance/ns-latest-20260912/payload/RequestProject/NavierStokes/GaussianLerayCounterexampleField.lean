/-
# An exact record-normalised velocity/pressure pair with a far source

This file constructs the field used to test the proposed *global Gaussian
Calderón–Zygmund estimate*

  `‖ℙ∇·(V⊗V)‖_{L²(ρ_{2ν})} ≤ C‖V‖_∞‖∇V‖_{L²(ρ_ν)}`.               (G-CZ)

The construction is completely explicit.  With `R` the translation distance,
`g_R(t) = e^{-(t−R)²/2}`, `a_R(t) = ∫₀^t g_R`, `α(t) = e^{−t²/4}` and
`κ = 1/4`, the velocity is the crossed shear pair

  `V(y) = κ a_R(y₂)α(y₃) e₁ + κ a_R(y₁)α(y₃) e₂`,

which is divergence free by inspection (each component is independent of its
own coordinate) and satisfies `‖V‖_∞ ≤ 1`, i.e. it lies in the
record-normalised class.  Its nonlinear source is a *single radial Gaussian*
centred far away at `c_R = (R,R,0)`:

  `∑_{i,j} ∂_i∂_j(V_iV_j) = div((V·∇)V) = 2κ² e^{−‖y−c_R‖²/2}`,

and therefore the pressure can be written in closed form as `P(y) = φ(‖y−c_R‖²)`
with `φ' = ψ`, `ψ(u) = −κ²∫₀¹ s²e^{−us²/2}ds`; the identity `4uψ'(u)+6ψ(u) =
−2κ²e^{−u/2}` is an integration by parts on `[0,1]`.

## Results

* `ClayNS.noGoV`, `ClayNS.noGoP` — the velocity and pressure;
* `ClayNS.noGoV_contDiff`, `ClayNS.noGoP_contDiff` — both are `C^∞`;
* `ClayNS.noGoV_divSpace` — `div V = 0`;
* `ClayNS.noGoV_norm_le_one` — `‖V‖_∞ ≤ 1` (record normalisation);
* `ClayNS.noGoV_advSpace` — the closed form of `(V·∇)V`;
* `ClayNS.noGoP_gradSpace` — the closed form of `∇P`;
* `ClayNS.noGo_pressure_poisson` — `div((V·∇)V + ∇P) = 0`, i.e. `P` is a
  genuine pressure for `V`: `−ΔP = ∑_{i,j}∂_i∂_j(V_iV_j)`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.StationarySimilarityRigidity

open MeasureTheory Set intervalIntegral
open scoped BigOperators

noncomputable section

namespace ClayNS

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

/-! ## One-dimensional building blocks -/

/-- The amplitude normalisation constant. -/
def kap : ℝ := 1 / 4

lemma kap_pos : 0 < kap := by norm_num [kap]

/-- `g_R(t) = e^{−(t−R)²/2}`, the shear profile derivative. -/
def nsGauss (R t : ℝ) : ℝ := Real.exp (-(t - R) ^ 2 / 2)

/-- `a_R(t) = ∫₀^t g_R`, a bounded kink profile with Gaussian derivative. -/
def nsKink (R y : ℝ) : ℝ := ∫ t in (0 : ℝ)..y, nsGauss R t

/-- `α(t) = e^{−t²/4}`; note `α² = e^{−t²/2}`. -/
def nsAl (t : ℝ) : ℝ := Real.exp (-t ^ 2 / 4)

lemma nsGauss_pos (R t : ℝ) : 0 < nsGauss R t := Real.exp_pos _

lemma nsGauss_le_one (R t : ℝ) : nsGauss R t ≤ 1 := by
  rw [nsGauss, Real.exp_le_one_iff]
  have : 0 ≤ (t - R) ^ 2 := sq_nonneg _
  linarith

lemma continuous_nsGauss (R : ℝ) : Continuous (nsGauss R) := by
  unfold nsGauss; fun_prop

lemma contDiff_nsGauss (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (nsGauss R) := by
  unfold nsGauss
  exact (Real.contDiff_exp.comp (((contDiff_id.sub contDiff_const).pow 2).neg.div_const 2))

lemma nsAl_pos (t : ℝ) : 0 < nsAl t := Real.exp_pos _

lemma nsAl_le_one (t : ℝ) : nsAl t ≤ 1 := by
  rw [nsAl, Real.exp_le_one_iff]
  have : 0 ≤ t ^ 2 := sq_nonneg _
  linarith

lemma contDiff_nsAl : ContDiff ℝ (⊤ : ℕ∞) nsAl := by
  unfold nsAl
  exact Real.contDiff_exp.comp ((contDiff_id.pow 2).neg.div_const 4)

lemma hasDerivAt_nsAl (t : ℝ) : HasDerivAt nsAl (-(t / 2) * nsAl t) t := by
  have h1 : HasDerivAt (fun s : ℝ => -s ^ 2 / 4) (-(2 * t) / 4) t := by
    simpa using (((hasDerivAt_pow 2 t).neg).div_const 4)
  have h2 := (Real.hasDerivAt_exp (-t ^ 2 / 4)).comp t h1
  refine h2.congr_deriv ?_
  rw [nsAl]
  ring

/-- `α'(t)² ≤ 1/2` — the shear cutoff has bounded gradient. -/
lemma nsAl_deriv_sq_le (t : ℝ) : (-(t / 2) * nsAl t) ^ 2 ≤ 1 / 2 := by
  have he : (Real.exp (-t ^ 2 / 4)) ^ 2 = Real.exp (-(t ^ 2 / 2)) := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hsq : (-(t / 2) * nsAl t) ^ 2 = (t ^ 2 / 4) * Real.exp (-(t ^ 2 / 2)) := by
    rw [nsAl, mul_pow, he]; ring
  have hexp : t ^ 2 / 2 ≤ Real.exp (t ^ 2 / 2) := by
    have := Real.add_one_le_exp (t ^ 2 / 2); linarith
  have hpos : (0 : ℝ) < Real.exp (t ^ 2 / 2) := Real.exp_pos _
  rw [hsq, Real.exp_neg]
  have key : t ^ 2 / 4 ≤ 1 / 2 * Real.exp (t ^ 2 / 2) := by linarith
  calc t ^ 2 / 4 * (Real.exp (t ^ 2 / 2))⁻¹
      ≤ (1 / 2 * Real.exp (t ^ 2 / 2)) * (Real.exp (t ^ 2 / 2))⁻¹ :=
        mul_le_mul_of_nonneg_right key (by positivity)
    _ = 1 / 2 := by field_simp

/-! ### The kink profile -/

lemma hasDerivAt_nsKink (R y : ℝ) : HasDerivAt (nsKink R) (nsGauss R y) y := by
  have hcont : Continuous (nsGauss R) := continuous_nsGauss R
  simpa [nsKink] using
    (intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable _ _) (hcont.stronglyMeasurableAtFilter _ _)
      hcont.continuousAt)

lemma differentiable_nsKink (R : ℝ) : Differentiable ℝ (nsKink R) :=
  fun y => (hasDerivAt_nsKink R y).differentiableAt

lemma contDiff_nsKink (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (nsKink R) := by
  have hnat : ∀ (k : ℕ), ContDiff ℝ (k : ℕ) (nsKink R) := by
    intro k
    induction k with
    | zero =>
        have : ContDiff ℝ (0 : ℕ) (nsKink R) := by
          rw [show ((0 : ℕ) : WithTop ℕ∞) = 0 from rfl, contDiff_zero]
          exact (differentiable_nsKink R).continuous
        exact this
    | succ k _ =>
        have hderiv : deriv (nsKink R) = nsGauss R :=
          funext fun y => (hasDerivAt_nsKink R y).deriv
        have : ContDiff ℝ ((k : WithTop ℕ∞) + 1) (nsKink R) := by
          rw [contDiff_succ_iff_deriv]
          refine ⟨differentiable_nsKink R, by simp, ?_⟩
          rw [hderiv]
          exact (contDiff_nsGauss R).of_le (by exact_mod_cast le_top)
        simpa using this
  exact contDiff_infty.mpr hnat

/-- The total Gaussian mass, `∫_ℝ e^{−(t−R)²/2} dt = √(2π)`. -/
lemma integral_nsGauss (R : ℝ) : (∫ t : ℝ, nsGauss R t) = Real.sqrt (2 * Real.pi) := by
  have hshift : (∫ t : ℝ, nsGauss R t) = ∫ t : ℝ, Real.exp (-(1/2) * t ^ 2) := by
    rw [show (fun t : ℝ => nsGauss R t) = fun t : ℝ => Real.exp (-(1/2) * (t - R) ^ 2) by
      funext t; rw [nsGauss]; ring_nf]
    exact integral_sub_right_eq_self (fun t : ℝ => Real.exp (-(1/2) * t ^ 2)) R
  rw [hshift, integral_gaussian]
  norm_num [mul_comm]

lemma integrable_nsGauss (R : ℝ) : Integrable (nsGauss R) := by
  have : Integrable (fun t : ℝ => Real.exp (-(1/2) * (t - R) ^ 2)) := by
    have h := (integrable_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num))
    exact (h.comp_sub_right R)
  exact this.congr (by filter_upwards with t; rw [nsGauss]; ring_nf)

/-- `|a_R| ≤ √(2π)`: the kink profile is uniformly bounded. -/
lemma nsKink_abs_le (R y : ℝ) : |nsKink R y| ≤ Real.sqrt (2 * Real.pi) := by
  have hmass : (∫ t : ℝ, nsGauss R t) = Real.sqrt (2 * Real.pi) := integral_nsGauss R
  have hint : Integrable (nsGauss R) := integrable_nsGauss R
  have hnn : ∀ t, 0 ≤ nsGauss R t := fun t => (nsGauss_pos R t).le
  rcases le_total 0 y with hy | hy
  · have h1 : nsKink R y = ∫ t in Ioc (0:ℝ) y, nsGauss R t := by
      rw [nsKink, intervalIntegral.integral_of_le hy]
    have h2 : (∫ t in Ioc (0:ℝ) y, nsGauss R t) ≤ ∫ t : ℝ, nsGauss R t :=
      setIntegral_le_integral hint (Filter.Eventually.of_forall hnn)
    have h3 : 0 ≤ ∫ t in Ioc (0:ℝ) y, nsGauss R t :=
      setIntegral_nonneg measurableSet_Ioc (fun t _ => hnn t)
    rw [h1, abs_of_nonneg h3, ← hmass]
    exact h2
  · have h1 : nsKink R y = -∫ t in Ioc y (0:ℝ), nsGauss R t := by
      rw [nsKink, intervalIntegral.integral_symm, intervalIntegral.integral_of_le hy]
    have h2 : (∫ t in Ioc y (0:ℝ), nsGauss R t) ≤ ∫ t : ℝ, nsGauss R t :=
      setIntegral_le_integral hint (Filter.Eventually.of_forall hnn)
    have h3 : 0 ≤ ∫ t in Ioc y (0:ℝ), nsGauss R t :=
      setIntegral_nonneg measurableSet_Ioc (fun t _ => hnn t)
    rw [h1, abs_neg, abs_of_nonneg h3, ← hmass]
    exact h2

/-- Near the origin the kink profile is exponentially small: for `|t| ≤ R/2`,
`|a_R(t)| ≤ (R/2)e^{−R²/8}`. -/
lemma nsKink_abs_le_near {R t : ℝ} (hR : 0 < R) (ht : |t| ≤ R / 2) :
    |nsKink R t| ≤ (R / 2) * Real.exp (-R ^ 2 / 8) := by
  have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) t, ‖nsGauss R s‖ ≤ Real.exp (-R ^ 2 / 8) := by
    intro s hs
    have hs' : |s| ≤ R / 2 := by
      rcases Set.mem_uIoc.mp hs with h | h
      · have := h.1; have := h.2
        rw [abs_le] at ht ⊢
        constructor <;> linarith [ht.1, ht.2]
      · have := h.1; have := h.2
        rw [abs_le] at ht ⊢
        constructor <;> linarith [ht.1, ht.2]
    have hsr : (s - R) ^ 2 ≥ R ^ 2 / 4 := by
      have h1 : s ≤ R / 2 := (abs_le.mp hs').2
      nlinarith [sq_nonneg (s - R), sq_nonneg s]
    rw [Real.norm_eq_abs, nsGauss, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    linarith
  have := intervalIntegral.norm_integral_le_of_norm_le_const (C := Real.exp (-R ^ 2 / 8)) hbound
  rw [nsKink, Real.norm_eq_abs] at *
  calc |∫ s in (0:ℝ)..t, nsGauss R s| ≤ Real.exp (-R ^ 2 / 8) * |t - 0| := this
    _ ≤ Real.exp (-R ^ 2 / 8) * (R / 2) := by
        have : |t - 0| ≤ R / 2 := by simpa using ht
        exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
    _ = (R / 2) * Real.exp (-R ^ 2 / 8) := by ring


/-- The derivative of the shear profile `g_R`. -/
lemma hasDerivAt_nsGauss (R t : ℝ) : HasDerivAt (nsGauss R) (-(t - R) * nsGauss R t) t := by
  have h1 : HasDerivAt (fun s : ℝ => -(s - R) ^ 2 / 2) (-(2 * (t - R)) / 2) t := by
    simpa using ((((hasDerivAt_id t).sub_const R).pow 2).neg.div_const 2)
  have h2 := (Real.hasDerivAt_exp (-(t - R) ^ 2 / 2)).comp t h1
  have he : -(t - R) * nsGauss R t = Real.exp (-(t - R) ^ 2 / 2) * (-(2 * (t - R)) / 2) := by
    rw [nsGauss]; ring
  have h3 : (Real.exp ∘ fun s : ℝ => -(s - R) ^ 2 / 2) = nsGauss R := by
    funext s; simp [nsGauss, Function.comp]
  rw [h3] at h2
  rw [he]
  exact h2

/-! ## The three-dimensional velocity field

`V(y) = κ a_R(y₂)α(y₃) e₁ + κ a_R(y₁)α(y₃) e₂` (0-indexed: `y 1`, `y 0`, `y 2`).
-/

/-- Coordinate projection of `E3` as a continuous linear functional. -/
abbrev prj (i : Fin 3) : E3 →L[ℝ] ℝ := EuclideanSpace.proj i

lemma prj_ee (i j : Fin 3) : prj i (ee j) = if i = j then (1 : ℝ) else 0 := by
  simp [ee, EuclideanSpace.single_apply]

/-- First velocity component `κ a_R(y₁)α(y₂)`. -/
def noGoF0 (R : ℝ) (y : E3) : ℝ := kap * (nsKink R (y 1) * nsAl (y 2))

/-- Second velocity component `κ a_R(y₀)α(y₂)`. -/
def noGoF1 (R : ℝ) (y : E3) : ℝ := kap * (nsKink R (y 0) * nsAl (y 2))

/-- The counterexample velocity field. -/
def noGoV (R : ℝ) (y : E3) : E3 := noGoF0 R y • ee 0 + noGoF1 R y • ee 1

/-- Differential of `noGoF0`. -/
def noGoD0 (R : ℝ) (y : E3) : E3 →L[ℝ] ℝ :=
  kap • (nsKink R (y 1) • ((-(y 2 / 2) * nsAl (y 2)) • prj 2)
        + nsAl (y 2) • (nsGauss R (y 1) • prj 1))

/-- Differential of `noGoF1`. -/
def noGoD1 (R : ℝ) (y : E3) : E3 →L[ℝ] ℝ :=
  kap • (nsKink R (y 0) • ((-(y 2 / 2) * nsAl (y 2)) • prj 2)
        + nsAl (y 2) • (nsGauss R (y 0) • prj 0))

lemma hasFDerivAt_noGoF0 (R : ℝ) (y : E3) : HasFDerivAt (noGoF0 R) (noGoD0 R y) y := by
  have ha : HasFDerivAt (fun w : E3 => nsKink R (w 1)) (nsGauss R (y 1) • prj 1) y := by
    simpa [Function.comp] using
      (hasDerivAt_nsKink R (y 1)).comp_hasFDerivAt y ((prj 1).hasFDerivAt)
  have hb : HasFDerivAt (fun w : E3 => nsAl (w 2)) ((-(y 2 / 2) * nsAl (y 2)) • prj 2) y := by
    simpa [Function.comp] using
      (hasDerivAt_nsAl (y 2)).comp_hasFDerivAt y ((prj 2).hasFDerivAt)
  exact (ha.mul hb).const_mul kap

lemma hasFDerivAt_noGoF1 (R : ℝ) (y : E3) : HasFDerivAt (noGoF1 R) (noGoD1 R y) y := by
  have ha : HasFDerivAt (fun w : E3 => nsKink R (w 0)) (nsGauss R (y 0) • prj 0) y := by
    simpa [Function.comp] using
      (hasDerivAt_nsKink R (y 0)).comp_hasFDerivAt y ((prj 0).hasFDerivAt)
  have hb : HasFDerivAt (fun w : E3 => nsAl (w 2)) ((-(y 2 / 2) * nsAl (y 2)) • prj 2) y := by
    simpa [Function.comp] using
      (hasDerivAt_nsAl (y 2)).comp_hasFDerivAt y ((prj 2).hasFDerivAt)
  exact (ha.mul hb).const_mul kap

lemma noGoD0_apply (R : ℝ) (y v : E3) :
    noGoD0 R y v = kap * (nsKink R (y 1) * (-(y 2 / 2) * nsAl (y 2)) * v 2
      + nsAl (y 2) * nsGauss R (y 1) * v 1) := by
  simp [noGoD0, prj]; ring

lemma noGoD1_apply (R : ℝ) (y v : E3) :
    noGoD1 R y v = kap * (nsKink R (y 0) * (-(y 2 / 2) * nsAl (y 2)) * v 2
      + nsAl (y 2) * nsGauss R (y 0) * v 0) := by
  simp [noGoD1, prj]; ring

lemma hasFDerivAt_noGoV (R : ℝ) (y : E3) :
    HasFDerivAt (noGoV R) ((noGoD0 R y).smulRight (ee 0) + (noGoD1 R y).smulRight (ee 1)) y :=
  ((hasFDerivAt_noGoF0 R y).smul_const (ee 0)).add ((hasFDerivAt_noGoF1 R y).smul_const (ee 1))

lemma noGoV_fderiv_apply (R : ℝ) (y v : E3) :
    fderiv ℝ (noGoV R) y v = (noGoD0 R y v) • ee 0 + (noGoD1 R y v) • ee 1 := by
  rw [(hasFDerivAt_noGoV R y).fderiv]; simp

lemma noGoF0_contDiff (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (noGoF0 R) :=
  contDiff_const.mul
    (((contDiff_nsKink R).comp (prj 1).contDiff).mul (contDiff_nsAl.comp (prj 2).contDiff))

lemma noGoF1_contDiff (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (noGoF1 R) :=
  contDiff_const.mul
    (((contDiff_nsKink R).comp (prj 0).contDiff).mul (contDiff_nsAl.comp (prj 2).contDiff))

lemma noGoV_contDiff (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (noGoV R) :=
  ((noGoF0_contDiff R).smul contDiff_const).add ((noGoF1_contDiff R).smul contDiff_const)

/-- Sum of two coordinate directions: the exact Euclidean norm. -/
lemma norm_sq_pair (a b : ℝ) : ‖a • (ee 0 : E3) + b • (ee 1 : E3)‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [ee, EuclideanSpace.single_apply, Fin.sum_univ_three]

lemma pair_apply (a b : ℝ) (i : Fin 3) :
    (a • (ee 0 : E3) + b • (ee 1 : E3)) i = if i = 0 then a else if i = 1 then b else 0 := by
  fin_cases i <;> simp [ee, EuclideanSpace.single_apply]

/-- `div V = 0`: each component is independent of its own coordinate. -/
lemma noGoV_divSpace (R : ℝ) (y : E3) : divSpace (noGoV R) y = 0 := by
  rw [divSpace]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [noGoV_fderiv_apply, pair_apply, noGoD0_apply, noGoD1_apply]
  fin_cases i <;> simp [ee, EuclideanSpace.single_apply]

/-- The field is record normalised: `‖V‖_∞ ≤ 1`. -/
lemma noGoV_norm_le_one (R : ℝ) (y : E3) : ‖noGoV R y‖ ≤ 1 := by
  have hk : ∀ t : ℝ, (nsKink R t) ^ 2 ≤ 2 * Real.pi := by
    intro t
    have h := nsKink_abs_le R t
    have h0 : (0:ℝ) ≤ 2 * Real.pi := by positivity
    have hs := Real.sq_sqrt h0
    nlinarith [abs_nonneg (nsKink R t), Real.sqrt_nonneg (2 * Real.pi),
      sq_abs (nsKink R t)]
  have ha : ∀ t : ℝ, (nsAl t) ^ 2 ≤ 1 := by
    intro t
    have h1 := nsAl_le_one t
    have h2 := (nsAl_pos t).le
    nlinarith
  have hbound : ∀ t s : ℝ, (kap * (nsKink R t * nsAl s)) ^ 2 ≤ Real.pi / 8 := by
    intro t s
    have h1 := hk t
    have h2 := ha s
    have h3 : (0:ℝ) ≤ (nsKink R t) ^ 2 := sq_nonneg _
    have : (kap * (nsKink R t * nsAl s)) ^ 2 = kap ^ 2 * ((nsKink R t) ^ 2 * (nsAl s) ^ 2) := by
      ring
    rw [this, kap]
    nlinarith [Real.pi_pos]
  have hsq : ‖noGoV R y‖ ^ 2 ≤ 1 := by
    rw [noGoV, norm_sq_pair, noGoF0, noGoF1]
    have h1 := hbound (y 1) (y 2)
    have h2 := hbound (y 0) (y 2)
    have hpi : Real.pi ≤ 4 := Real.pi_le_four
    linarith
  nlinarith [norm_nonneg (noGoV R y)]


/-! ## The nonlinear term and its divergence -/

/-- First component of `(V·∇)V`. -/
def noGoN0 (R : ℝ) (y : E3) : ℝ :=
  kap ^ 2 * ((nsAl (y 2)) ^ 2 * (nsKink R (y 0) * nsGauss R (y 1)))

/-- Second component of `(V·∇)V`. -/
def noGoN1 (R : ℝ) (y : E3) : ℝ :=
  kap ^ 2 * ((nsAl (y 2)) ^ 2 * (nsKink R (y 1) * nsGauss R (y 0)))

/-- The closed form of `(V·∇)V`. -/
def noGoAdv (R : ℝ) (y : E3) : E3 := noGoN0 R y • ee 0 + noGoN1 R y • ee 1

lemma noGoV_apply0 (R : ℝ) (y : E3) : (noGoV R y) 0 = noGoF0 R y := by
  rw [noGoV, pair_apply]; simp

lemma noGoV_apply1 (R : ℝ) (y : E3) : (noGoV R y) 1 = noGoF1 R y := by
  rw [noGoV, pair_apply]; simp

lemma noGoV_apply2 (R : ℝ) (y : E3) : (noGoV R y) 2 = 0 := by
  rw [noGoV, pair_apply]; simp

lemma noGoV_fderiv_ee0 (R : ℝ) (y : E3) :
    fderiv ℝ (noGoV R) y (ee 0) = (kap * (nsAl (y 2) * nsGauss R (y 0))) • (ee 1 : E3) := by
  rw [noGoV_fderiv_apply, noGoD0_apply, noGoD1_apply]
  simp [ee, EuclideanSpace.single_apply]

lemma noGoV_fderiv_ee1 (R : ℝ) (y : E3) :
    fderiv ℝ (noGoV R) y (ee 1) = (kap * (nsAl (y 2) * nsGauss R (y 1))) • (ee 0 : E3) := by
  rw [noGoV_fderiv_apply, noGoD0_apply, noGoD1_apply]
  simp [ee, EuclideanSpace.single_apply]

lemma noGoV_fderiv_ee2 (R : ℝ) (y : E3) :
    fderiv ℝ (noGoV R) y (ee 2)
      = (kap * (nsKink R (y 1) * (-(y 2 / 2) * nsAl (y 2)))) • (ee 0 : E3)
        + (kap * (nsKink R (y 0) * (-(y 2 / 2) * nsAl (y 2)))) • (ee 1 : E3) := by
  rw [noGoV_fderiv_apply, noGoD0_apply, noGoD1_apply]
  simp [ee, EuclideanSpace.single_apply]

/-- Closed form of the advective term. -/
lemma noGoV_advSpace (R : ℝ) (y : E3) : advSpace (noGoV R) y = noGoAdv R y := by
  rw [advSpace, Fin.sum_univ_three, noGoV_apply0, noGoV_apply1, noGoV_apply2,
    noGoV_fderiv_ee0, noGoV_fderiv_ee1, noGoAdv, noGoN0, noGoN1, noGoF0, noGoF1,
    smul_smul, smul_smul, zero_smul, add_zero]
  rw [add_comm]
  congr 1 <;> [skip; skip] <;> congr 1 <;> ring

/-- The pointwise squared gradient of the counterexample velocity. -/
lemma noGoV_gradSq (R : ℝ) (y : E3) :
    gradSqSpace (noGoV R) y
      = (kap * (nsAl (y 2) * nsGauss R (y 0))) ^ 2
        + (kap * (nsAl (y 2) * nsGauss R (y 1))) ^ 2
        + ((kap * (nsKink R (y 1) * (-(y 2 / 2) * nsAl (y 2)))) ^ 2
           + (kap * (nsKink R (y 0) * (-(y 2 / 2) * nsAl (y 2)))) ^ 2) := by
  rw [gradSqSpace, Fin.sum_univ_three, noGoV_fderiv_ee0, noGoV_fderiv_ee1, noGoV_fderiv_ee2]
  have h1 : ‖(kap * (nsAl (y 2) * nsGauss R (y 0))) • (ee 1 : E3)‖ ^ 2
      = (kap * (nsAl (y 2) * nsGauss R (y 0))) ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    simp [ee, EuclideanSpace.norm_single]
  have h2 : ‖(kap * (nsAl (y 2) * nsGauss R (y 1))) • (ee 0 : E3)‖ ^ 2
      = (kap * (nsAl (y 2) * nsGauss R (y 1))) ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    simp [ee, EuclideanSpace.norm_single]
  rw [h1, h2, norm_sq_pair]

/-! ### The source term -/

/-- The source `div((V·∇)V)`. -/
def noGoS (R : ℝ) (y : E3) : ℝ :=
  2 * kap ^ 2 * ((nsAl (y 2)) ^ 2 * (nsGauss R (y 0) * nsGauss R (y 1)))

/-- Differential of `noGoN0`. -/
def noGoDN0 (R : ℝ) (y : E3) : E3 →L[ℝ] ℝ :=
  (kap ^ 2) • ((nsAl (y 2)) ^ 2 • (nsKink R (y 0) • ((-(y 1 - R) * nsGauss R (y 1)) • prj 1)
        + nsGauss R (y 1) • (nsGauss R (y 0) • prj 0))
    + (nsKink R (y 0) * nsGauss R (y 1))
        • ((2 * nsAl (y 2) * (-(y 2 / 2) * nsAl (y 2))) • prj 2))

/-- Differential of `noGoN1`. -/
def noGoDN1 (R : ℝ) (y : E3) : E3 →L[ℝ] ℝ :=
  (kap ^ 2) • ((nsAl (y 2)) ^ 2 • (nsKink R (y 1) • ((-(y 0 - R) * nsGauss R (y 0)) • prj 0)
        + nsGauss R (y 0) • (nsGauss R (y 1) • prj 1))
    + (nsKink R (y 1) * nsGauss R (y 0))
        • ((2 * nsAl (y 2) * (-(y 2 / 2) * nsAl (y 2))) • prj 2))

private lemma hasFDerivAt_alSq (y : E3) :
    HasFDerivAt (fun w : E3 => (nsAl (w 2)) ^ 2)
      ((2 * nsAl (y 2) * (-(y 2 / 2) * nsAl (y 2))) • prj 2) y := by
  have hb : HasFDerivAt (fun w : E3 => nsAl (w 2)) ((-(y 2 / 2) * nsAl (y 2)) • prj 2) y := by
    simpa [Function.comp] using
      (hasDerivAt_nsAl (y 2)).comp_hasFDerivAt y ((prj 2).hasFDerivAt)
  have := hb.pow 2
  simpa [mul_comm, mul_assoc, mul_left_comm, smul_smul] using this

lemma hasFDerivAt_noGoN0 (R : ℝ) (y : E3) : HasFDerivAt (noGoN0 R) (noGoDN0 R y) y := by
  have ha : HasFDerivAt (fun w : E3 => nsKink R (w 0)) (nsGauss R (y 0) • prj 0) y := by
    simpa [Function.comp] using
      (hasDerivAt_nsKink R (y 0)).comp_hasFDerivAt y ((prj 0).hasFDerivAt)
  have hg : HasFDerivAt (fun w : E3 => nsGauss R (w 1))
      ((-(y 1 - R) * nsGauss R (y 1)) • prj 1) y := by
    simpa [Function.comp] using
      (hasDerivAt_nsGauss R (y 1)).comp_hasFDerivAt y ((prj 1).hasFDerivAt)
  exact (((hasFDerivAt_alSq y).mul (ha.mul hg)).const_mul (kap ^ 2))

lemma hasFDerivAt_noGoN1 (R : ℝ) (y : E3) : HasFDerivAt (noGoN1 R) (noGoDN1 R y) y := by
  have ha : HasFDerivAt (fun w : E3 => nsKink R (w 1)) (nsGauss R (y 1) • prj 1) y := by
    simpa [Function.comp] using
      (hasDerivAt_nsKink R (y 1)).comp_hasFDerivAt y ((prj 1).hasFDerivAt)
  have hg : HasFDerivAt (fun w : E3 => nsGauss R (w 0))
      ((-(y 0 - R) * nsGauss R (y 0)) • prj 0) y := by
    simpa [Function.comp] using
      (hasDerivAt_nsGauss R (y 0)).comp_hasFDerivAt y ((prj 0).hasFDerivAt)
  exact (((hasFDerivAt_alSq y).mul (ha.mul hg)).const_mul (kap ^ 2))

lemma hasFDerivAt_noGoAdv (R : ℝ) (y : E3) :
    HasFDerivAt (noGoAdv R)
      ((noGoDN0 R y).smulRight (ee 0) + (noGoDN1 R y).smulRight (ee 1)) y :=
  ((hasFDerivAt_noGoN0 R y).smul_const (ee 0)).add ((hasFDerivAt_noGoN1 R y).smul_const (ee 1))

lemma noGoAdv_fderiv_apply (R : ℝ) (y v : E3) :
    fderiv ℝ (noGoAdv R) y v = (noGoDN0 R y v) • ee 0 + (noGoDN1 R y v) • ee 1 := by
  rw [(hasFDerivAt_noGoAdv R y).fderiv]; simp

lemma noGoDN0_apply (R : ℝ) (y v : E3) :
    noGoDN0 R y v = kap ^ 2 * ((nsAl (y 2)) ^ 2 * (nsKink R (y 0) * (-(y 1 - R)
        * nsGauss R (y 1)) * v 1 + nsGauss R (y 1) * nsGauss R (y 0) * v 0)
      + nsKink R (y 0) * nsGauss R (y 1)
          * (2 * nsAl (y 2) * (-(y 2 / 2) * nsAl (y 2))) * v 2) := by
  simp [noGoDN0, prj]; ring

lemma noGoDN1_apply (R : ℝ) (y v : E3) :
    noGoDN1 R y v = kap ^ 2 * ((nsAl (y 2)) ^ 2 * (nsKink R (y 1) * (-(y 0 - R)
        * nsGauss R (y 0)) * v 0 + nsGauss R (y 0) * nsGauss R (y 1) * v 1)
      + nsKink R (y 1) * nsGauss R (y 0)
          * (2 * nsAl (y 2) * (-(y 2 / 2) * nsAl (y 2))) * v 2) := by
  simp [noGoDN1, prj]; ring

/-- `div((V·∇)V) = S`, a single Gaussian bump centred at `(R,R,0)`. -/
lemma noGoAdv_divSpace (R : ℝ) (y : E3) : divSpace (noGoAdv R) y = noGoS R y := by
  rw [divSpace, Fin.sum_univ_three]
  have e : ∀ (a b : ℝ) (i : Fin 3),
      (a • (ee 0 : E3) + b • (ee 1 : E3)) i = if i = 0 then a else if i = 1 then b else 0 :=
    fun a b i => pair_apply a b i
  rw [noGoAdv_fderiv_apply, noGoAdv_fderiv_apply, noGoAdv_fderiv_apply, e, e, e]
  simp only [reduceIte]
  rw [noGoDN0_apply, noGoDN1_apply, noGoS]
  simp [ee, EuclideanSpace.single_apply]
  ring


/-- The centre `(R,R,0)` of the far source. -/
def noGoC (R : ℝ) : E3 := R • ee 0 + R • ee 1

lemma noGoC_apply (R : ℝ) (i : Fin 3) :
    (noGoC R) i = if i = 0 then R else if i = 1 then R else 0 := pair_apply R R i

lemma noGo_dist_sq (R : ℝ) (y : E3) :
    ‖y - noGoC R‖ ^ 2 = (y 0 - R) ^ 2 + (y 1 - R) ^ 2 + (y 2) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_three, noGoC_apply]

/-- **The source is a single radial Gaussian centred far away.** -/
lemma noGoS_radial (R : ℝ) (y : E3) :
    noGoS R y = 2 * kap ^ 2 * Real.exp (-‖y - noGoC R‖ ^ 2 / 2) := by
  rw [noGoS, nsAl, nsGauss, nsGauss, noGo_dist_sq]
  rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

lemma noGoS_nonneg (R : ℝ) (y : E3) : 0 ≤ noGoS R y := by
  rw [noGoS_radial]
  positivity

end ClayNS
