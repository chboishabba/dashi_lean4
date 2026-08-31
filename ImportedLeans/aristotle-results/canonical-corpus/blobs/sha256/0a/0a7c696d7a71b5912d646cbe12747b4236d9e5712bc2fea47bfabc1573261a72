/-
# Row A — the coupling drive in interval form, and the small-field radius gate

`SmallFieldRGContraction` derives the Row-A completion predicate from the
block-spin scaling structure of the small-field renormalisation-group step.  Its
drive hypothesis `hgen` is stated with the *scale-dependent* constant
`C_gen·g_j³`, where `g_j = g(u₀ + b j)` is the coupling at the tube floor of
scale `j`; that couples the hypothesis to the bare coupling `u₀` and to the
slope `b`, and so cannot be quantified over a range of bare couplings.

This file replaces it by the form the differentiated source majorants actually
produce.  For a channel `R(g) = Σ_{n≥4}a_n gⁿ` with `|a_n| ≤ A Kⁿ` one has, on
any interval `[0,G]` with `KG ≤ ρ < 1`,

    |R'(g)| ≤ A K⁴ (4−3ρ)(1−ρ)⁻² g³,   hence   |R(g) − R(g')| ≤ C G³|g − g'|,

i.e. a Lipschitz bound *on an interval*, with a cubically suppressed constant
that carries the interval's endpoint.  `tube_drive_of_interval_cubic` shows that
this interval form implies the scale-dependent one on the admissible tube, since
the trajectory at scale `j` never leaves `[0, g(u₀ + b j)]`; composing with the
Jacobian of `u = g⁻²` turns the cubic drive into the *sextic* weight
`(C_gen/2)g_j⁶ = literalMarginalWeight C_gen u₀ b j`.

`rowA_completion_of_cubic_drive` is then `rowA_completion_of_scaling_rg_data`
with the interval-form drive, and `couplingOf_le_of_inv_sq` is the elementary
statement that the small-field radius conditions are lower bounds on the bare
inverse coupling.  Both are what `RowASmallBareCoupling` needs in order to
quantify over all sufficiently small bare couplings.

**Honest status.**  Row A is not closed and nothing is promoted; this is a
strengthening of the hypothesis format of an existing conditional theorem, not a
new physical input.
-/
import RequestProject.YangMills.SmallFieldRGContraction

namespace YangMills

open Finset

/-! ## 1. The small-field radius gate -/

/-- The small-field radius condition in the shooting coordinate: `g(u) ≤ c` as
soon as `u ≥ c⁻²`. -/
theorem couplingOf_le_of_inv_sq {c u : ℝ} (hc : 0 < c) (hu : (c⁻¹) ^ 2 ≤ u) :
    couplingOf u ≤ c := by
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu
  have hinv : u⁻¹ ≤ c ^ 2 := by
    have h : ((c⁻¹) ^ 2)⁻¹ = c ^ 2 := by rw [← inv_pow, inv_inv]
    calc u⁻¹ ≤ ((c⁻¹) ^ 2)⁻¹ := inv_anti₀ (by positivity) hu
      _ = c ^ 2 := h
  calc couplingOf u = Real.sqrt u⁻¹ := rfl
    _ ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt hinv
    _ = c := Real.sqrt_sq hc.le

/-! ## 2. The interval form of the cubic coupling drive -/

section Scaling

variable {Op : Type*} [Fintype Op]

/-- **An interval-form cubic drive is the tube drive.**  If the nonlinear part of
the renormalisation-group step is Lipschitz in the coupling on every interval
`[0,G]` with constant `C_gen G³` — the shape produced by differentiating the
source majorants — then on the admissible tube its drive in the shooting
coordinate is exactly the marginal weight `(C_gen/2)g_j⁶`. -/
theorem tube_drive_of_interval_cubic {Nl : ℕ → ℝ → (Op → ℝ) → (Op → ℝ)}
    {Cgen u₀ bl : ℝ} (hCgen : 0 ≤ Cgen) (hu₀ : 0 < u₀) (hbl : 0 < bl)
    (hgen3 : ∀ (j : ℕ) (G g g' : ℝ) (x : Op → ℝ), 0 ≤ g → g ≤ G → 0 ≤ g' → g' ≤ G →
      ‖Nl j g x - Nl j g' x‖ ≤ Cgen * G ^ 3 * |g - g'|)
    (j : ℕ) (a b : ℝ) (x : Op → ℝ) (ha : u₀ + bl * j ≤ a) (hb : u₀ + bl * j ≤ b) :
    ‖Nl j (couplingOf a) x - Nl j (couplingOf b) x‖
      ≤ literalMarginalWeight Cgen u₀ bl j * |a - b| := by
  have hfj : (0 : ℝ) < u₀ + bl * j := by
    have : (0 : ℝ) ≤ bl * j := by positivity
    linarith
  have h1 := hgen3 j (couplingOf (u₀ + bl * j)) (couplingOf a) (couplingOf b) x
    (couplingOf_nonneg _) (couplingOf_le hfj ha) (couplingOf_nonneg _) (couplingOf_le hfj hb)
  exact le_trans h1 (drive_of_cubic_generation hCgen hu₀ hbl ha hb)

/-! ## 3. Row A's completion predicate with the interval-form drive -/

/-- **Row A's completion predicate from the scaling structure and an
interval-form cubic drive.**  Identical in content to
`rowA_completion_of_scaling_rg_data`, except that the coupling drive is assumed
in the form the differentiated source majorants produce — Lipschitz on every
interval `[0,G]` with constant `C_gen G³` — rather than with a constant already
tied to the tube floor of the given bare coupling.  The estimate is then free of
`u₀` and `b`, which is what allows it to be quantified over all sufficiently
small bare couplings. -/
theorem rowA_completion_of_cubic_drive
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {bet betaZ : ℕ → ℝ → ℝ} {lamD : ℕ → ℝ → ι → ℝ} {lamG : ℕ → ℝ → κ → ℝ}
    {aI aC aL : ℕ → ℝ → ℕ → ℝ} {N : ℕ}
    {dim : Op → ℝ} {Nl : ℕ → ℝ → (Op → ℝ) → (Op → ℝ)} {rst : ℕ → ℝ → (Op → ℝ)}
    {LamDet LamGauge theta AI AC AL Kmaj rho Cdir Lcoef Cmem Cgen L delta eta : ℝ}
    {bZm bZp eps u₀ target : ℝ} {K : ℕ}
    (hstruct : ∀ j p, u₀ ≤ p → bet j p
      = literalShellAt betaZ lamD lamG aI aC aL N j p
          (couplingOf (shootingTrajectory bet p j)))
    (hLd : ∀ j p i, |lamD j p i| ≤ LamDet) (hLg : ∀ j p i, |lamG j p i| ≤ LamGauge)
    (hLd0 : 0 ≤ LamDet) (hLg0 : 0 ≤ LamGauge)
    (hI : ∀ j p n, |aI j p n| ≤ AI * Kmaj ^ (n + 4))
    (hC : ∀ j p n, |aC j p n| ≤ AC * Kmaj ^ (n + 4))
    (hLcc : ∀ j p n, |aL j p n| ≤ AL * Kmaj ^ (n + 4))
    (hAI : 0 ≤ AI) (hAC : 0 ≤ AC) (hAL : 0 ≤ AL) (hK : 0 ≤ Kmaj)
    (hGLd : couplingOf u₀ * LamDet ≤ theta) (hGLg : couplingOf u₀ * LamGauge ≤ theta)
    (hth : theta < 1) (hrho : Kmaj * couplingOf u₀ ≤ rho) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hCdir : analyticDirectSensitivityBound (Fintype.card ι) (Fintype.card κ)
      LamDet LamGauge theta AI AC AL Kmaj rho ≤ Cdir)
    (hZl : ∀ j p, u₀ ≤ p → bZm ≤ betaZ j p) (hZu : ∀ j p, u₀ ≤ p → betaZ j p ≤ bZp)
    (hIntEps : ∀ j p, u₀ ≤ p →
      |frozenShellInteraction (lamD j p) (lamG j p) (aI j p) (aC j p) (aL j p) N
        (couplingOf (shootingTrajectory bet p j))| ≤ eps)
    (hLblock : 1 < L) (hdim : ∀ o, 4 + delta ≤ dim o)
    (hNlip : ∀ j g x y, ‖Nl j g x - Nl j g y‖ ≤ eta * ‖x - y‖)
    (heta0 : 0 ≤ eta) (heta : eta < 1 - L ^ (-delta))
    (hgen3 : ∀ (j : ℕ) (G g g' : ℝ) (x : Op → ℝ), 0 ≤ g → g ≤ G → 0 ≤ g' → g' ≤ G →
      ‖Nl j g x - Nl j g' x‖ ≤ Cgen * G ^ 3 * |g - g'|)
    (hCgen : 0 ≤ Cgen)
    (hr0 : ∀ p q, u₀ ≤ p → u₀ ≤ q → rst 0 p = rst 0 q)
    (hrec : ∀ j p, u₀ ≤ p →
      rst (j + 1) p = rgStep L dim Nl j (shootingTrajectory bet p j) (rst j p))
    (hlip : ∀ j p q g,
      |literalShellAt betaZ lamD lamG aI aC aL N j p g
        - literalShellAt betaZ lamD lamG aI aC aL N j q g| ≤ Lcoef * ‖rst j p - rst j q‖)
    (hLc0 : 0 ≤ Lcoef) (hCmem : 0 ≤ Cmem)
    (hdom : Lcoef * Cgen ≤ Cmem * (L ^ (-delta) + eta) * Cdir)
    (hu₀ : 0 < u₀) (hepsm : eps < bZm)
    (hsig : literalKernelMass Cdir Cmem (L ^ (-delta) + eta) u₀ (bZm - eps) < 1 / 2)
    (hwin : 0 < target - (bZp + eps) * K) (htube : u₀ ≤ target - (bZp + eps) * K) :
    RowACompletion bet K target (bZm - eps) (bZp + eps) (target - (bZp + eps) * K)⁻¹ := by
  classical
  set bl : ℝ := bZm - eps with hbldef
  set thm : ℝ := L ^ (-delta) + eta with hthmdef
  have hbl : (0 : ℝ) < bl := by rw [hbldef]; linarith
  have hthm0 : 0 ≤ thm := rgStep_theta_nonneg hLblock heta0
  have hthm1 : thm < 1 := rgStep_theta_lt_one heta
  have hCdir0 : 0 ≤ analyticDirectSensitivityBound (Fintype.card ι) (Fintype.card κ)
      LamDet LamGauge theta AI AC AL Kmaj rho :=
    analyticDirectSensitivityBound_nonneg hth hAI hAC hAL hrho1
  have hCd0 : 0 ≤ Cdir := le_trans hCdir0 hCdir
  -- the trajectory floor on the tube
  have hlow : ∀ j p, u₀ ≤ p → bl ≤ bet j p := by
    intro j p hp
    have h := abs_le.mp (hIntEps j p hp)
    rw [hstruct j p hp, literalShellAt, hbldef]
    have := hZl j p hp
    linarith [h.1]
  have hfloor : ∀ p, u₀ ≤ p → ∀ i, u₀ + bl * i ≤ shootingTrajectory bet p i := fun p hp i =>
    shootingTrajectory_floor hp (fun i' => hlow i' p hp) i
  -- the derived one-step contraction
  have hcon : ∀ j g x y, ‖rgStep L dim Nl j g x - rgStep L dim Nl j g y‖ ≤ thm * ‖x - y‖ :=
    fun j g x y => rgStep_contract hLblock hdim hNlip j g x y
  -- the derived coupling drive, from the interval form
  have hdrv : ∀ j p q x, u₀ ≤ p → u₀ ≤ q →
      ‖rgStep L dim Nl j (shootingTrajectory bet p j) x
          - rgStep L dim Nl j (shootingTrajectory bet q j) x‖
        ≤ literalMarginalWeight Cgen u₀ bl j
            * |shootingTrajectory bet p j - shootingTrajectory bet q j| := by
    intro j p q x hp hq
    rw [rgStep_drive]
    exact tube_drive_of_interval_cubic hCgen hu₀ hbl hgen3 j _ _ x
      (hfloor p hp j) (hfloor q hq j)
  -- the scale-free domination
  have hD : ∀ k, Lcoef * literalMarginalWeight Cgen u₀ bl k
      ≤ Cmem * thm * literalMarginalWeight Cdir u₀ bl k := fun k =>
    literalMarginalWeight_dominate hu₀ hbl hdom k
  -- the coefficient response, derived
  have hmem := literal_mem_of_tube_contraction (bet := bet)
    (betaZ := betaZ) (lamD := lamD) (lamG := lamG) (aI := aI) (aC := aC) (aL := aL) (N := N)
    (R := rgStep L dim Nl) (rst := rst) (D := literalMarginalWeight Cgen u₀ bl)
    (Lcoef := Lcoef) (Cmem := Cmem) (thmem := thm) (Cdir := Cdir) (u₀ := u₀) (bl := bl)
    hr0 hrec hcon hdrv hthm0 hlip hLc0 hCmem hCd0 hu₀ hbl hD
  exact rowA_completion_of_literal_channels hstruct hLd hLg hLd0 hLg0 hI hC hLcc
    hAI hAC hAL hK hGLd hGLg hth hrho hrho0 hrho1 hCdir hZl hZu hIntEps
    (fun j p q g hp hq => hmem j p q g hp hq)
    hCmem hthm0 hthm1 hu₀ hepsm hsig hwin htube

end Scaling

end YangMills
