/-
# The exact Leray pressure of the far-source counterexample field

The velocity `noGoV R` built in `GaussianLerayCounterexampleField` has
nonlinear source

  `div((V·∇)V) = S(y) = 2κ² e^{−‖y−c_R‖²/2}`,      `c_R = (R,R,0)`,

a single radial Gaussian centred far from the origin.  Its Leray pressure is
therefore radial about `c_R` and can be written in closed form:

  `P(y) = Φ(‖y−c_R‖²)`,   `Φ' = ψ`,   `ψ(u) = −κ² ∫₀¹ s² e^{−us²/2} ds`.

The only identity needed is the integration by parts

  `u ∫₀¹ s⁴e^{−us²/2}ds = 3∫₀¹s²e^{−us²/2}ds − e^{−u/2}`,

which is the fundamental theorem of calculus applied to `s ↦ s³e^{−us²/2}`
on `[0,1]`; it turns the radial Laplacian `4uψ'(u)+6ψ(u)` into exactly `−S`.

## Results

* `ClayNS.psiN`, `ClayNS.psiN_ibp` — the one-dimensional kernel and the exact
  integration-by-parts identity;
* `ClayNS.noGoP` — the pressure, `ClayNS.noGoP_contDiff` — it is `C^∞`;
* `ClayNS.noGoP_gradSpace` — `∇P(y) = 2ψ(‖y−c‖²)(y−c)`;
* `ClayNS.noGoP_lap` — `ΔP = −S`;
* `ClayNS.noGo_pressure_poisson` — `div((V·∇)V + ∇P) = 0`, i.e. the pair
  `(V,P)` realises the Leray projection `ℙ∇·(V⊗V) = (V·∇)V + ∇P`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.GaussianLerayCounterexampleField

open MeasureTheory Set intervalIntegral
open scoped BigOperators

noncomputable section

namespace ClayNS

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

/-! ## The radial kernel -/

/-- `ψ_n(u) = ∫₀¹ s^{2n+2} e^{−us²/2} ds`. -/
def psiN (n : ℕ) (u : ℝ) : ℝ := ∫ s in (0:ℝ)..1, s ^ (2 * n + 2) * Real.exp (-u * s ^ 2 / 2)

lemma continuous_psiIntegrand (n : ℕ) (u : ℝ) :
    Continuous (fun s : ℝ => s ^ (2 * n + 2) * Real.exp (-u * s ^ 2 / 2)) :=
  (continuous_pow _).mul (Real.continuous_exp.comp (by continuity))

lemma hasDerivAt_psiN (n : ℕ) (u : ℝ) :
    HasDerivAt (psiN n) (-(1/2) * psiN (n+1) u) u := by
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (x : ℝ) (s : ℝ) => s ^ (2 * n + 2) * Real.exp (-x * s ^ 2 / 2))
    (F' := fun (x : ℝ) (s : ℝ) => -(1/2) * (s ^ (2 * (n+1) + 2) * Real.exp (-x * s ^ 2 / 2)))
    (x₀ := u) (a := 0) (b := 1) (bound := fun _ => Real.exp (|u| + 1))
    (s := Metric.ball u 1) (μ := volume) (Metric.ball_mem_nhds u one_pos)
    (Filter.Eventually.of_forall (fun x => (continuous_psiIntegrand n x).aestronglyMeasurable))
    ((continuous_psiIntegrand n u).intervalIntegrable _ _)
    ((continuous_const.mul (continuous_psiIntegrand (n+1) u)).aestronglyMeasurable)
    ?_ (_root_.intervalIntegrable_const) ?_
  · have h2 := key.2
    have hval : (∫ s in (0:ℝ)..1, -(1/2 : ℝ) * (s ^ (2 * (n+1) + 2) * Real.exp (-u * s ^ 2 / 2)))
        = -(1/2) * psiN (n+1) u := by
      rw [psiN, ← intervalIntegral.integral_const_mul]
    rw [hval] at h2
    exact h2
  · filter_upwards with s hs x hx
    have hs1 : |s| ≤ 1 := by
      rcases Set.mem_uIoc.mp hs with h | h
      · rw [abs_le]; constructor <;> linarith [h.1, h.2]
      · rw [abs_le]; constructor <;> linarith [h.1, h.2]
    have hxb : |x - u| < 1 := by simpa [Real.dist_eq] using Metric.mem_ball.mp hx
    have hsq : s ^ 2 ≤ 1 := by nlinarith [abs_nonneg s, sq_abs s]
    have hxa : |x| ≤ |u| + 1 := by
      have := abs_sub_abs_le_abs_sub x u
      linarith
    have hpow : |s ^ (2 * (n+1) + 2)| ≤ 1 := by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg s) hs1
    have hexp : Real.exp (-x * s ^ 2 / 2) ≤ Real.exp (|u| + 1) := by
      apply Real.exp_le_exp.mpr
      nlinarith [abs_nonneg s, neg_abs_le x, le_abs_self x, sq_nonneg s, sq_abs s, abs_nonneg u]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos (-x * s ^ 2 / 2))]
    have h1 : |(-(1/2) : ℝ)| = 1/2 := by norm_num
    rw [h1]
    nlinarith [Real.exp_pos (|u| + 1), Real.exp_pos (-x * s ^ 2 / 2),
      abs_nonneg (s ^ (2 * (n+1) + 2))]
  · filter_upwards with s _ x _
    have h1 : HasDerivAt (fun x : ℝ => -x * s ^ 2 / 2) (-(s^2)/2) x := by
      simpa using ((hasDerivAt_id x).neg.mul_const (s^2)).div_const 2
    have h2 := (Real.hasDerivAt_exp (-x * s ^ 2 / 2)).comp x h1
    have h3 := h2.const_mul (s ^ (2 * n + 2))
    convert h3 using 1
    have hs : (2 * (n+1) + 2) = (2 * n + 2) + 2 := by ring
    rw [hs, pow_add]
    simp
    ring

lemma differentiable_psiN (n : ℕ) : Differentiable ℝ (psiN n) :=
  fun u => (hasDerivAt_psiN n u).differentiableAt

lemma contDiff_psiN_nat : ∀ (k : ℕ) (n : ℕ), ContDiff ℝ (k : ℕ) (psiN n) := by
  intro k
  induction k with
  | zero =>
      intro n
      have : ContDiff ℝ (0 : ℕ) (psiN n) := by
        rw [show ((0 : ℕ) : WithTop ℕ∞) = 0 from rfl, contDiff_zero]
        exact (differentiable_psiN n).continuous
      exact this
  | succ k ih =>
      intro n
      have hderiv : deriv (psiN n) = fun u => -(1/2) * psiN (n+1) u :=
        funext fun u => (hasDerivAt_psiN n u).deriv
      have : ContDiff ℝ ((k : WithTop ℕ∞) + 1) (psiN n) := by
        rw [contDiff_succ_iff_deriv]
        refine ⟨differentiable_psiN n, by simp, ?_⟩
        rw [hderiv]
        exact contDiff_const.mul (ih (n+1))
      simpa using this

lemma contDiff_psiN (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (psiN n) :=
  contDiff_infty.mpr (fun k => contDiff_psiN_nat k n)

/-- **The integration-by-parts identity.** `u ψ₁(u) = 3ψ₀(u) − e^{−u/2}`. -/
lemma psiN_ibp (u : ℝ) : u * psiN 1 u = 3 * psiN 0 u - Real.exp (-u / 2) := by
  have hderiv : ∀ s ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => t ^ 3 * Real.exp (-u * t ^ 2 / 2))
        (3 * (s ^ 2 * Real.exp (-u * s ^ 2 / 2)) - u * (s ^ 4 * Real.exp (-u * s ^ 2 / 2))) s := by
    intro s _
    have h1 : HasDerivAt (fun t : ℝ => -u * t ^ 2 / 2) (-u * (2 * s) / 2) s := by
      simpa using (((hasDerivAt_pow 2 s).const_mul (-u)).div_const 2)
    have h2 := (Real.hasDerivAt_exp (-u * s ^ 2 / 2)).comp s h1
    have h3 := (hasDerivAt_pow 3 s).mul h2
    convert h3 using 1
    simp [Function.comp]
    ring
  have hcont : IntervalIntegrable
      (fun s : ℝ => 3 * (s ^ 2 * Real.exp (-u * s ^ 2 / 2))
        - u * (s ^ 4 * Real.exp (-u * s ^ 2 / 2))) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at key
  have e0 : (∫ s in (0:ℝ)..1, s ^ 2 * Real.exp (-u * s ^ 2 / 2)) = psiN 0 u := by
    rw [psiN]
  have e1 : (∫ s in (0:ℝ)..1, s ^ 4 * Real.exp (-u * s ^ 2 / 2)) = psiN 1 u := by
    rw [psiN]
  rw [e0, e1] at key
  have hrhs : (1:ℝ) ^ 3 * Real.exp (-u * 1 ^ 2 / 2) - (0:ℝ) ^ 3 * Real.exp (-u * 0 ^ 2 / 2)
      = Real.exp (-u / 2) := by norm_num
  rw [hrhs] at key
  linarith

/-! ## The radial pressure profile -/

/-- `ψ(u) = −κ²ψ₀(u)`, the radial derivative profile of the pressure. -/
def nsPsi (u : ℝ) : ℝ := -(kap ^ 2) * psiN 0 u

lemma hasDerivAt_nsPsi (u : ℝ) : HasDerivAt nsPsi ((kap ^ 2 / 2) * psiN 1 u) u := by
  have h := (hasDerivAt_psiN 0 u).const_mul (-(kap ^ 2))
  have he : -(kap ^ 2) * (-(1/2) * psiN 1 u) = (kap ^ 2 / 2) * psiN 1 u := by ring
  rw [he] at h
  exact h

lemma differentiable_nsPsi : Differentiable ℝ nsPsi :=
  fun u => (hasDerivAt_nsPsi u).differentiableAt

lemma continuous_nsPsi : Continuous nsPsi := differentiable_nsPsi.continuous

lemma contDiff_nsPsi : ContDiff ℝ (⊤ : ℕ∞) nsPsi :=
  contDiff_const.mul (contDiff_psiN 0)

/-- The radial primitive `Φ` with `Φ' = ψ`. -/
def nsPhi (u : ℝ) : ℝ := ∫ v in (0:ℝ)..u, nsPsi v

lemma hasDerivAt_nsPhi (u : ℝ) : HasDerivAt nsPhi (nsPsi u) u := by
  simpa [nsPhi] using
    (intervalIntegral.integral_hasDerivAt_right
      (continuous_nsPsi.intervalIntegrable 0 u)
      (continuous_nsPsi.stronglyMeasurableAtFilter _ _)
      continuous_nsPsi.continuousAt)

lemma differentiable_nsPhi : Differentiable ℝ nsPhi :=
  fun u => (hasDerivAt_nsPhi u).differentiableAt

lemma contDiff_nsPhi : ContDiff ℝ (⊤ : ℕ∞) nsPhi := by
  have hnat : ∀ (k : ℕ), ContDiff ℝ (k : ℕ) nsPhi := by
    intro k
    induction k with
    | zero =>
        have : ContDiff ℝ (0 : ℕ) nsPhi := by
          rw [show ((0 : ℕ) : WithTop ℕ∞) = 0 from rfl, contDiff_zero]
          exact differentiable_nsPhi.continuous
        exact this
    | succ k _ =>
        have hderiv : deriv nsPhi = nsPsi := funext fun u => (hasDerivAt_nsPhi u).deriv
        have : ContDiff ℝ ((k : WithTop ℕ∞) + 1) nsPhi := by
          rw [contDiff_succ_iff_deriv]
          refine ⟨differentiable_nsPhi, by simp, ?_⟩
          rw [hderiv]
          exact contDiff_nsPsi.of_le (by exact_mod_cast le_top)
        simpa using this
  exact contDiff_infty.mpr hnat

/-- **The radial Laplacian identity** `4uψ'(u) + 6ψ(u) = −2κ²e^{−u/2}`. -/
lemma nsPsi_radial_laplace (u : ℝ) :
    4 * u * ((kap ^ 2 / 2) * psiN 1 u) + 6 * nsPsi u = -(2 * kap ^ 2 * Real.exp (-u / 2)) := by
  have h := psiN_ibp u
  rw [nsPsi]
  nlinarith [h]

/-! ## The pressure on `E3` -/

/-- `q(y) = ‖y − c_R‖²`. -/
def noGoQ (R : ℝ) (y : E3) : ℝ := ‖y - noGoC R‖ ^ 2

lemma noGoQ_coord (R : ℝ) (y : E3) :
    noGoQ R y = (y 0 - R) ^ 2 + (y 1 - R) ^ 2 + (y 2) ^ 2 := noGo_dist_sq R y

lemma sub_center_apply (R : ℝ) (y : E3) (i : Fin 3) :
    (y - noGoC R) i = if i = 0 then y 0 - R else if i = 1 then y 1 - R else y 2 := by
  fin_cases i <;> simp [noGoC_apply]

/-- Differential of `q`. -/
def noGoDQ (R : ℝ) (y : E3) : E3 →L[ℝ] ℝ :=
  (2 * (y 0 - R)) • prj 0 + (2 * (y 1 - R)) • prj 1 + (2 * (y 2)) • prj 2

lemma noGoDQ_apply (R : ℝ) (y v : E3) :
    noGoDQ R y v = 2 * (y 0 - R) * v 0 + 2 * (y 1 - R) * v 1 + 2 * (y 2) * v 2 := by
  simp [noGoDQ, prj]

lemma hasFDerivAt_noGoQ (R : ℝ) (y : E3) : HasFDerivAt (noGoQ R) (noGoDQ R y) y := by
  have hq : noGoQ R = fun w : E3 => (w 0 - R) ^ 2 + (w 1 - R) ^ 2 + (w 2) ^ 2 := by
    funext w; exact noGoQ_coord R w
  rw [hq]
  have h0 : HasFDerivAt (fun w : E3 => (w 0 - R) ^ 2) ((2 * (y 0 - R)) • prj 0) y := by
    have := (((prj 0).hasFDerivAt (x := y)).sub_const R).pow 2
    simpa [mul_comm, smul_smul] using this
  have h1 : HasFDerivAt (fun w : E3 => (w 1 - R) ^ 2) ((2 * (y 1 - R)) • prj 1) y := by
    have := (((prj 1).hasFDerivAt (x := y)).sub_const R).pow 2
    simpa [mul_comm, smul_smul] using this
  have h2 : HasFDerivAt (fun w : E3 => (w 2) ^ 2) ((2 * (y 2)) • prj 2) y := by
    have := ((prj 2).hasFDerivAt (x := y)).pow 2
    simpa [mul_comm, smul_smul] using this
  exact ((h0.add h1).add h2)

lemma contDiff_noGoQ (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (noGoQ R) := by
  have hq : noGoQ R = fun w : E3 => (w 0 - R) ^ 2 + (w 1 - R) ^ 2 + (w 2) ^ 2 := by
    funext w; exact noGoQ_coord R w
  rw [hq]
  exact ((((prj 0).contDiff.sub contDiff_const).pow 2).add
    (((prj 1).contDiff.sub contDiff_const).pow 2)).add ((prj 2).contDiff.pow 2)

/-- The pressure. -/
def noGoP (R : ℝ) (y : E3) : ℝ := nsPhi (noGoQ R y)

lemma hasFDerivAt_noGoP (R : ℝ) (y : E3) :
    HasFDerivAt (noGoP R) ((nsPsi (noGoQ R y)) • noGoDQ R y) y := by
  simpa [noGoP, Function.comp] using
    (hasDerivAt_nsPhi (noGoQ R y)).comp_hasFDerivAt y (hasFDerivAt_noGoQ R y)

lemma noGoP_contDiff (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (noGoP R) :=
  contDiff_nsPhi.comp (contDiff_noGoQ R)

/-- Any vector of `E3` is the sum of its coordinate components. -/
lemma sum_coord (x : E3) : ∑ i, (x i) • ee i = x := by
  ext j
  rw [Fin.sum_univ_three]
  fin_cases j <;> simp [ee, EuclideanSpace.single_apply]

/-- `∇P(y) = 2ψ(‖y−c‖²)(y−c)`. -/
lemma noGoP_gradSpace (R : ℝ) (y : E3) :
    gradSpace (noGoP R) y = (2 * nsPsi (noGoQ R y)) • (y - noGoC R) := by
  rw [gradSpace]
  have hstep : ∀ i : Fin 3, fderiv ℝ (noGoP R) y (ee i)
      = (2 * nsPsi (noGoQ R y)) * ((y - noGoC R) i) := by
    intro i
    rw [(hasFDerivAt_noGoP R y).fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, noGoDQ_apply]
    rw [sub_center_apply]
    fin_cases i <;> simp [ee, EuclideanSpace.single_apply] <;> ring
  have hsm : ∀ i : Fin 3, (2 * nsPsi (noGoQ R y) * ((y - noGoC R) i)) • (ee i : E3)
      = (2 * nsPsi (noGoQ R y)) • (((y - noGoC R) i) • ee i) := fun i => mul_smul _ _ _
  simp only [hstep, hsm]
  rw [← Finset.smul_sum, sum_coord]

/-- The Leray velocity field `W = ∇P`. -/
def noGoW (R : ℝ) (y : E3) : E3 := (2 * nsPsi (noGoQ R y)) • (y - noGoC R)

lemma hasFDerivAt_noGoW (R : ℝ) (y : E3) :
    HasFDerivAt (noGoW R)
      ((2 * nsPsi (noGoQ R y)) • (ContinuousLinearMap.id ℝ E3)
        + (((2 * ((kap ^ 2 / 2) * psiN 1 (noGoQ R y))) • noGoDQ R y).smulRight
            (y - noGoC R))) y := by
  have hf : HasFDerivAt (fun w : E3 => 2 * nsPsi (noGoQ R w))
      ((2 * ((kap ^ 2 / 2) * psiN 1 (noGoQ R y))) • noGoDQ R y) y := by
    have h1 : HasFDerivAt (fun w : E3 => nsPsi (noGoQ R w))
        (((kap ^ 2 / 2) * psiN 1 (noGoQ R y)) • noGoDQ R y) y := by
      simpa [Function.comp] using
        (hasDerivAt_nsPsi (noGoQ R y)).comp_hasFDerivAt y (hasFDerivAt_noGoQ R y)
    have := h1.const_mul (2 : ℝ)
    simpa [smul_smul, mul_assoc] using this
  have hg : HasFDerivAt (fun w : E3 => w - noGoC R) (ContinuousLinearMap.id ℝ E3) y :=
    (hasFDerivAt_id y).sub_const (noGoC R)
  exact hf.smul hg

/-- `ΔP = −S`: the pressure exactly cancels the divergence of the nonlinearity. -/
lemma noGoW_divSpace (R : ℝ) (y : E3) : divSpace (noGoW R) y = -noGoS R y := by
  rw [divSpace]
  have hstep : ∀ i : Fin 3, (fderiv ℝ (noGoW R) y (ee i)) i
      = 2 * nsPsi (noGoQ R y)
        + 2 * ((kap ^ 2 / 2) * psiN 1 (noGoQ R y)) * (2 * ((y - noGoC R) i))
            * ((y - noGoC R) i) := by
    intro i
    rw [(hasFDerivAt_noGoW R y).fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
      PiLp.add_apply, PiLp.smul_apply, noGoDQ_apply]
    have hd : (2 * (y 0 - R) * (ee i) 0 + 2 * (y 1 - R) * (ee i) 1 + 2 * (y 2) * (ee i) 2)
        = 2 * ((y - noGoC R) i) := by
      rw [sub_center_apply]
      fin_cases i <;> simp [ee, EuclideanSpace.single_apply]
    rw [hd]
    have hee : ((ee i : E3) i) = 1 := by simp [ee, EuclideanSpace.single_apply]
    rw [hee]
    ring
  simp only [hstep]
  rw [Finset.sum_add_distrib]
  have hsum1 : (∑ _i : Fin 3, 2 * nsPsi (noGoQ R y)) = 6 * nsPsi (noGoQ R y) := by
    simp [Finset.sum_const]; ring
  have hsum2 : (∑ i : Fin 3, 2 * ((kap ^ 2 / 2) * psiN 1 (noGoQ R y)) * (2 * ((y - noGoC R) i))
      * ((y - noGoC R) i))
      = 4 * (∑ i : Fin 3, ((y - noGoC R) i) ^ 2) * ((kap ^ 2 / 2) * psiN 1 (noGoQ R y)) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hq : (∑ i : Fin 3, ((y - noGoC R) i) ^ 2) = noGoQ R y := by
    rw [noGoQ, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp
  rw [hsum1, hsum2, hq]
  have hkey := nsPsi_radial_laplace (noGoQ R y)
  rw [noGoS_radial, show ‖y - noGoC R‖ ^ 2 = noGoQ R y from rfl]
  linarith [hkey]

lemma noGoP_lap (R : ℝ) (y : E3) : divSpace (gradSpace (noGoP R)) y = -noGoS R y := by
  have hfun : gradSpace (noGoP R) = noGoW R := by
    funext w; rw [noGoP_gradSpace, noGoW]
  rw [hfun]
  exact noGoW_divSpace R y

/-- **The pair `(V,P)` realises the Leray projection.**
`div((V·∇)V + ∇P) = 0`, i.e. `−ΔP = ∑ᵢⱼ ∂ᵢ∂ⱼ(VᵢVⱼ)`. -/
theorem noGo_pressure_poisson (R : ℝ) (y : E3) :
    divSpace (fun x => advSpace (noGoV R) x + gradSpace (noGoP R) x) y = 0 := by
  have hfun : (fun x : E3 => advSpace (noGoV R) x + gradSpace (noGoP R) x)
      = fun x : E3 => noGoAdv R x + noGoW R x := by
    funext w
    rw [noGoV_advSpace, noGoP_gradSpace, noGoW]
  rw [hfun, divSpace]
  have hd : ∀ i : Fin 3, fderiv ℝ (fun x : E3 => noGoAdv R x + noGoW R x) y (ee i)
      = fderiv ℝ (noGoAdv R) y (ee i) + fderiv ℝ (noGoW R) y (ee i) := by
    intro i
    have hh : HasFDerivAt (fun x : E3 => noGoAdv R x + noGoW R x)
        (((noGoDN0 R y).smulRight (ee 0) + (noGoDN1 R y).smulRight (ee 1))
          + ((2 * nsPsi (noGoQ R y)) • (ContinuousLinearMap.id ℝ E3)
            + (((2 * ((kap ^ 2 / 2) * psiN 1 (noGoQ R y))) • noGoDQ R y).smulRight
                (y - noGoC R)))) y :=
      (hasFDerivAt_noGoAdv R y).add (hasFDerivAt_noGoW R y)
    rw [hh.fderiv, (hasFDerivAt_noGoAdv R y).fderiv, (hasFDerivAt_noGoW R y).fderiv]
    simp
  simp only [hd, PiLp.add_apply]
  rw [Finset.sum_add_distrib]
  have h1 : (∑ i, (fderiv ℝ (noGoAdv R) y (ee i)) i) = noGoS R y := noGoAdv_divSpace R y
  have h2 : (∑ i, (fderiv ℝ (noGoW R) y (ee i)) i) = -noGoS R y := noGoW_divSpace R y
  rw [h1, h2]
  ring

end ClayNS
