/-
# Row A — one smallness statement about the bare coupling closes every gate

`RowACubicDriveClosure` produces the Row-A completion predicate from local
renormalisation-group data, but still carries five *numerical* side conditions
that have to be checked by hand at a given bare inverse coupling `u₀`:

* the two small-field radius conditions `g(u₀)·Λ_det ≤ θ`, `g(u₀)·Λ_gauge ≤ θ`;
* the Cauchy radius condition `K·g(u₀) ≤ ρ`;
* the debt tolerance `ε < b_Z⁻`;
* the contraction gate `σ = literalKernelMass … < 1/2`.

This file shows they are all consequences of one statement — *the bare coupling
is small enough* — with an explicit threshold.  The mechanism is the one the
shooting coordinate manufactures:

* the quartic debt of the five channels at inverse coupling `p ≥ u₀` is
  `C_int·g(p)⁴ ≤ C_int/u₀²`, so the tolerance is `ε(u₀) = C_int/u₀²` and beats
  any fixed floor `b_Z⁻` once `u₀² ≥ 2C_int/b_Z⁻`;
* the cumulative sensitivity is `σ ≤ (1 + C_mem/(1−θ))·(C_dir/2)(u₀⁻³ +
  1/(2b u₀²))`, because the per-shell weight is `g_j⁶` and the trajectory
  weights are *retained* in the summation, so `σ = O(1/(b u₀²))` and beats `1/2`
  once `u₀² > (1 + C_mem/(1−θ))·C_dir·(1 + 1/b_Z⁻)`;
* the radius conditions are `g(u₀) = u₀^{-1/2} ≤ θ/(Λ+1)`, i.e. `u₀ ≥
  ((Λ+1)/θ)²`.

`rowA_small_bare_coupling` therefore reads: for the literal shell coefficient
with the source-shaped inputs, **there is an explicit threshold `U` such that
every bare inverse coupling `u₀ ≥ U` produces the Row-A completion predicate**
at every cutoff `K` and every observation-scale target above the window floor.
This is the quantitative form of "a sufficiently small bare coupling produces
the tuned trajectory".

**Honest status.**  Row A is not closed; nothing is promoted.  The inputs of
`rowA_small_bare_coupling` are the physical hypotheses listed in
`RowACubicDriveClosure`: the two-sided Gaussian window for the literal shell
Gaussian coefficient, the Cauchy/spectral majorants of the five channels, the
quartic debt bound, the contraction of the irrelevant renormalisation-group map
with a cubically suppressed coupling drive, and the Lipschitz dependence of the
coefficients on the irrelevant state.  What this file removes is the last
*numerical* bookkeeping: none of the gates has to be checked separately any
more.
-/
import RequestProject.YangMills.RowACubicDriveClosure

namespace YangMills

open Finset

variable {Op : Type*} [Fintype Op]

/-! ## 1. The two elementary gates -/

/-- `g(u)⁴ = (u²)⁻¹`. -/
theorem couplingOf_pow_four {u : ℝ} (hu : 0 ≤ u) : couplingOf u ^ 4 = (u ^ 2)⁻¹ := by
  have h := couplingOf_sq hu
  calc couplingOf u ^ 4 = (couplingOf u ^ 2) ^ 2 := by ring
    _ = (u⁻¹) ^ 2 := by rw [h]
    _ = (u ^ 2)⁻¹ := by rw [inv_pow]

/-- **The small-field radius gate.**  `g(u)·Λ ≤ θ` as soon as `u ≥ ((Λ+1)/θ)²`. -/
theorem couplingOf_mul_le_of_radius {Lam theta u : ℝ} (hLam : 0 ≤ Lam) (hth : 0 < theta)
    (hu : ((Lam + 1) / theta) ^ 2 ≤ u) : couplingOf u * Lam ≤ theta := by
  have hc : (0 : ℝ) < theta / (Lam + 1) := by positivity
  have hinv : ((theta / (Lam + 1))⁻¹) ^ 2 ≤ u := by
    rw [inv_div]; exact hu
  have hg : couplingOf u ≤ theta / (Lam + 1) := couplingOf_le_of_inv_sq hc hinv
  have h1 : couplingOf u * Lam ≤ (theta / (Lam + 1)) * Lam :=
    mul_le_mul_of_nonneg_right hg hLam
  have h2 : (theta / (Lam + 1)) * Lam ≤ theta := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-! ## 2. The quartic debt tolerance produced by a bare coupling -/

/-- The debt tolerance of the five channels at bare inverse coupling `u₀`:
`ε(u₀) = C_int/u₀²`, i.e. `C_int·g(u₀)⁴`. -/
noncomputable def quarticDebtTolerance (Cint u₀ : ℝ) : ℝ := Cint / u₀ ^ 2

theorem quarticDebtTolerance_nonneg {Cint u₀ : ℝ} (hC : 0 ≤ Cint) :
    0 ≤ quarticDebtTolerance Cint u₀ := by
  rw [quarticDebtTolerance]; positivity

/-- `u ≤ u²` for `u ≥ 1`. -/
theorem self_le_sq {u : ℝ} (hu : 1 ≤ u) : u ≤ u ^ 2 := by nlinarith

/-- **The debt gate.**  `C/u² ≤ b/2` as soon as `u² ≥ 2C/b`. -/
theorem quarticDebt_le_half {Cint bZm u : ℝ} (hb : 0 < bZm) (hu : 0 < u)
    (h : 2 * Cint / bZm ≤ u ^ 2) : Cint / u ^ 2 ≤ bZm / 2 := by
  have hu2 : (0 : ℝ) < u ^ 2 := by positivity
  rw [div_le_div_iff₀ hu2 (by norm_num : (0 : ℝ) < 2)]
  have h2 : 2 * Cint ≤ u ^ 2 * bZm := by
    have h3 := mul_le_mul_of_nonneg_right h hb.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hb)] at h3
  linarith

/-! ## 3. Every gate from one smallness statement -/

/-- **Row A's completion predicate at every sufficiently small bare coupling.**

The hypotheses are the source-shaped ones of `rowA_completion_of_cubic_drive`,
stated once on a fixed tube `p ≥ u_base`; the interaction sector is asked only
for its quartic bound `|β_Int| ≤ C_int·g⁴`, not for a prescribed tolerance.  The
conclusion exhibits an explicit threshold `U` such that for **every** bare
inverse coupling `u₀ ≥ U`, every cutoff `K`, and every observation target above
the window floor `u₀ + (b_Z⁺ + ε)K`, the Row-A completion predicate holds with
slopes `b_Z⁻ − ε` and `b_Z⁺ + ε`, `ε = C_int/u₀²`.

All five numerical gates — the two small-field radius conditions, the Cauchy
radius, the debt tolerance and the contraction gate `σ < 1/2` — are discharged
by `U ≤ u₀` alone. -/
theorem rowA_small_bare_coupling
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {bet betaZ : ℕ → ℝ → ℝ} {lamD : ℕ → ℝ → ι → ℝ} {lamG : ℕ → ℝ → κ → ℝ}
    {aI aC aL : ℕ → ℝ → ℕ → ℝ} {N : ℕ}
    {dim : Op → ℝ} {Nl : ℕ → ℝ → (Op → ℝ) → (Op → ℝ)} {rst : ℕ → ℝ → (Op → ℝ)}
    {LamDet LamGauge theta AI AC AL Kmaj rho Cdir Lcoef Cmem Cgen L delta eta : ℝ}
    {bZm bZp Cint ubase : ℝ}
    (hstruct : ∀ j p, ubase ≤ p → bet j p
      = literalShellAt betaZ lamD lamG aI aC aL N j p
          (couplingOf (shootingTrajectory bet p j)))
    (hLd : ∀ j p i, |lamD j p i| ≤ LamDet) (hLg : ∀ j p i, |lamG j p i| ≤ LamGauge)
    (hLd0 : 0 ≤ LamDet) (hLg0 : 0 ≤ LamGauge)
    (hI : ∀ j p n, |aI j p n| ≤ AI * Kmaj ^ (n + 4))
    (hC : ∀ j p n, |aC j p n| ≤ AC * Kmaj ^ (n + 4))
    (hLc : ∀ j p n, |aL j p n| ≤ AL * Kmaj ^ (n + 4))
    (hAI : 0 ≤ AI) (hAC : 0 ≤ AC) (hAL : 0 ≤ AL) (hK : 0 ≤ Kmaj)
    (hth0 : 0 < theta) (hth : theta < 1) (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hCdir : analyticDirectSensitivityBound (Fintype.card ι) (Fintype.card κ)
      LamDet LamGauge theta AI AC AL Kmaj rho ≤ Cdir)
    (hZl : ∀ j p, ubase ≤ p → bZm ≤ betaZ j p) (hZu : ∀ j p, ubase ≤ p → betaZ j p ≤ bZp)
    (hIntQ : ∀ j p, ubase ≤ p →
      |frozenShellInteraction (lamD j p) (lamG j p) (aI j p) (aC j p) (aL j p) N
        (couplingOf (shootingTrajectory bet p j))| ≤ Cint * couplingOf p ^ 4)
    (hCint : 0 ≤ Cint)
    (hLblock : 1 < L) (hdim : ∀ o, 4 + delta ≤ dim o)
    (hNlip : ∀ j g x y, ‖Nl j g x - Nl j g y‖ ≤ eta * ‖x - y‖)
    (heta0 : 0 ≤ eta) (heta : eta < 1 - L ^ (-delta))
    (hgen3 : ∀ (j : ℕ) (G g g' : ℝ) (x : Op → ℝ), 0 ≤ g → g ≤ G → 0 ≤ g' → g' ≤ G →
      ‖Nl j g x - Nl j g' x‖ ≤ Cgen * G ^ 3 * |g - g'|)
    (hCgen : 0 ≤ Cgen)
    (hr0 : ∀ p q, ubase ≤ p → ubase ≤ q → rst 0 p = rst 0 q)
    (hrec : ∀ j p, ubase ≤ p →
      rst (j + 1) p = rgStep L dim Nl j (shootingTrajectory bet p j) (rst j p))
    (hlip : ∀ j p q g,
      |literalShellAt betaZ lamD lamG aI aC aL N j p g
        - literalShellAt betaZ lamD lamG aI aC aL N j q g| ≤ Lcoef * ‖rst j p - rst j q‖)
    (hLc0 : 0 ≤ Lcoef)
    (hdom : Lcoef * Cgen ≤ Cmem * (L ^ (-delta) + eta) * Cdir)
    (hCmem : 0 ≤ Cmem)
    (hbZm : 0 < bZm) (hubase : 0 < ubase) :
    ∃ U : ℝ, ubase ≤ U ∧ 1 ≤ U ∧
      ∀ u₀ : ℝ, U ≤ u₀ → ∀ (K : ℕ) (target : ℝ),
        u₀ + (bZp + quarticDebtTolerance Cint u₀) * K ≤ target →
        RowACompletion bet K target
          (bZm - quarticDebtTolerance Cint u₀) (bZp + quarticDebtTolerance Cint u₀)
          (target - (bZp + quarticDebtTolerance Cint u₀) * K)⁻¹ := by
  have hCdir0 : 0 ≤ analyticDirectSensitivityBound (Fintype.card ι) (Fintype.card κ)
      LamDet LamGauge theta AI AC AL Kmaj rho :=
    analyticDirectSensitivityBound_nonneg hth hAI hAC hAL hrho1
  have hCd0 : 0 ≤ Cdir := le_trans hCdir0 hCdir
  set thmem : ℝ := L ^ (-delta) + eta with hthmem
  have hthm0 : 0 ≤ thmem := rgStep_theta_nonneg hLblock heta0
  have hthm1 : thmem < 1 := rgStep_theta_lt_one heta
  have hthden : (0 : ℝ) < 1 - thmem := by linarith
  -- the contraction constant of the whole lane
  set Ctot : ℝ := (1 + Cmem / (1 - thmem)) * Cdir * (1 + 1 / bZm) with hCtot
  have hCtot0 : 0 ≤ Ctot := by
    have h1 : 0 ≤ 1 + Cmem / (1 - thmem) := by positivity
    have h2 : 0 ≤ 1 + 1 / bZm := by positivity
    rw [hCtot]
    exact mul_nonneg (mul_nonneg h1 hCd0) h2
  -- the explicit threshold
  set r1 : ℝ := ((LamDet + 1) / theta) ^ 2 with hr1
  set r2 : ℝ := ((LamGauge + 1) / theta) ^ 2 with hr2
  set r3 : ℝ := ((Kmaj + 1) / rho) ^ 2 with hr3
  have hr10 : 0 ≤ r1 := by rw [hr1]; positivity
  have hr20 : 0 ≤ r2 := by rw [hr2]; positivity
  have hr30 : 0 ≤ r3 := by rw [hr3]; positivity
  have hdebt0 : 0 ≤ 2 * Cint / bZm := by positivity
  refine ⟨ubase + 1 + Ctot + 2 * Cint / bZm + r1 + r2 + r3, by linarith, by linarith, ?_⟩
  intro u₀ hU K target htgt
  -- the elementary consequences of `U ≤ u₀`
  have hu₀1 : 1 ≤ u₀ := by linarith
  have hu₀0 : 0 < u₀ := by linarith
  have hub : ubase ≤ u₀ := by linarith
  have hsq : u₀ ≤ u₀ ^ 2 := self_le_sq hu₀1
  have hCtotlt : Ctot < u₀ ^ 2 := by linarith
  have hdebtle : 2 * Cint / bZm ≤ u₀ ^ 2 := by linarith
  have hr1le : r1 ≤ u₀ := by linarith
  have hr2le : r2 ≤ u₀ := by linarith
  have hr3le : r3 ≤ u₀ := by linarith
  -- the debt tolerance
  set eps : ℝ := quarticDebtTolerance Cint u₀ with heps
  have heps0 : 0 ≤ eps := quarticDebtTolerance_nonneg hCint
  have hepshalf : eps ≤ bZm / 2 := by
    rw [heps, quarticDebtTolerance]
    exact quarticDebt_le_half hbZm hu₀0 hdebtle
  have hepsm : eps < bZm := by linarith
  have hbl : (0 : ℝ) < bZm - eps := by linarith
  -- the radius gates
  have hGLd : couplingOf u₀ * LamDet ≤ theta :=
    couplingOf_mul_le_of_radius hLd0 hth0 (by rw [← hr1]; exact hr1le)
  have hGLg : couplingOf u₀ * LamGauge ≤ theta :=
    couplingOf_mul_le_of_radius hLg0 hth0 (by rw [← hr2]; exact hr2le)
  have hrho : Kmaj * couplingOf u₀ ≤ rho := by
    have h := couplingOf_mul_le_of_radius hK hrho0 (show ((Kmaj + 1) / rho) ^ 2 ≤ u₀ by
      rw [← hr3]; exact hr3le)
    linarith [h, mul_comm (couplingOf u₀) Kmaj]
  -- the interaction sector is below the tolerance on the tube
  have hIntEps : ∀ j p, u₀ ≤ p →
      |frozenShellInteraction (lamD j p) (lamG j p) (aI j p) (aC j p) (aL j p) N
        (couplingOf (shootingTrajectory bet p j))| ≤ eps := by
    intro j p hp
    have hp0 : 0 < p := lt_of_lt_of_le hu₀0 hp
    have h := hIntQ j p (le_trans hub hp)
    have hfour : couplingOf p ^ 4 = (p ^ 2)⁻¹ := couplingOf_pow_four hp0.le
    have hmono : (p ^ 2)⁻¹ ≤ (u₀ ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ hu₀0.le hp 2)
    have : Cint * couplingOf p ^ 4 ≤ Cint * (u₀ ^ 2)⁻¹ := by
      rw [hfour]
      exact mul_le_mul_of_nonneg_left hmono hCint
    have heq : Cint * (u₀ ^ 2)⁻¹ = eps := by
      rw [heps, quarticDebtTolerance, div_eq_mul_inv]
    linarith
  -- the contraction gate
  have hsig : literalKernelMass Cdir Cmem thmem u₀ (bZm - eps) < 1 / 2 := by
    refine literal_sigma_lt_half hCd0 hCmem hthm1 hbl hu₀1 ?_
    have hfac0 : 0 ≤ (1 + Cmem / (1 - thmem)) * Cdir := by positivity
    have hhalf : 1 / (2 * (bZm - eps)) ≤ 1 / bZm := by
      refine one_div_le_one_div_of_le hbZm ?_
      linarith
    have hmono : (1 + Cmem / (1 - thmem)) * Cdir * (1 + 1 / (2 * (bZm - eps)))
        ≤ (1 + Cmem / (1 - thmem)) * Cdir * (1 + 1 / bZm) :=
      mul_le_mul_of_nonneg_left (by linarith) hfac0
    calc (1 + Cmem / (1 - thmem)) * Cdir * (1 + 1 / (2 * (bZm - eps)))
        ≤ Ctot := by rw [hCtot]; exact hmono
      _ < u₀ ^ 2 := hCtotlt
  -- the observation window
  have htube : u₀ ≤ target - (bZp + eps) * K := by linarith
  have hwin : 0 < target - (bZp + eps) * K := lt_of_lt_of_le hu₀0 htube
  exact rowA_completion_of_cubic_drive
    (dim := dim) (Nl := Nl) (rst := rst) (Cgen := Cgen) (Lcoef := Lcoef) (Cmem := Cmem)
    (fun j p hp => hstruct j p (le_trans hub hp))
    hLd hLg hLd0 hLg0 hI hC hLc hAI hAC hAL hK hGLd hGLg hth hrho hrho0.le hrho1 hCdir
    (fun j p hp => hZl j p (le_trans hub hp)) (fun j p hp => hZu j p (le_trans hub hp))
    hIntEps hLblock hdim hNlip heta0 heta hgen3 hCgen
    (fun p q hp hq => hr0 p q (le_trans hub hp) (le_trans hub hq))
    (fun j p hp => hrec j p (le_trans hub hp)) hlip hLc0 hCmem hdom
    hu₀0 hepsm hsig hwin htube

end YangMills
