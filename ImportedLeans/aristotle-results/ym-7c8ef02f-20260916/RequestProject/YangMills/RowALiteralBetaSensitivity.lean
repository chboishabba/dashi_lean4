/-
# Row A — the literal cumulative beta map is a `q < 1` contraction

This is the assembly of the Row-A sensitivity lane.  It puts together

* `LiteralChannelSensitivity` — the *differentiated* source majorants: the five
  literal remainder channels are Lipschitz in the coupling with the cubically
  suppressed constant `C_dir·G³`, where `C_dir` is built from exactly the same
  spectral data `Λ` and Cauchy pair `(A, K)` that bound the channels themselves;
* `InverseCouplingSensitivity` — the shooting coordinate `u = g⁻²`, in which the
  cubic sensitivity acquires a second factor `½g³`, i.e. becomes `g⁶`, and the
  weighted summation `Σ_j g_j⁶ ≤ u₀⁻³ + 1/(2b u₀²)` along a trajectory whose
  inverse coupling grows at least linearly;
* `RowASensitivityBootstrap` — the discrete Duhamel bootstrap converting a
  response kernel of total mass `σ` into a *bare-coupling* Lipschitz constant,
  the marginal/irrelevant split kernel, and the clamping that lets every
  hypothesis be assumed on the admissible tube only.

The result (`rowA_completion_of_literal_channels`) is: for a shell coefficient of
the literal shape

    β_j(p) = β_{Z,j}(p) + [five literal channels with history-`p` coefficients]
             evaluated at the effective coupling g_j(p) = u_j(p)^{-1/2},

whose coefficient (history) response forgets geometrically and is driven by the
marginal weights, the cumulative beta map is a contraction and the Row-A
completion predicate holds, **provided the bare coupling is small enough**:
explicitly `u₀² > (1 + C_mem/(1−θ_mem))·C_dir·(1 + 1/(2b))` suffices
(`literal_sigma_lt_half`).  This is the quantitative mechanism behind
"sufficiently small bare coupling produces the tuned trajectory".

## What is proved and what is still assumed

Proved here: the direct (marginal) sensitivity of the literal channels, its
`g⁶` form in the shooting coordinate, the summation of the weights along the
trajectory, the bootstrap to the bare coupling, the smallness criterion, and the
completion predicate.

Assumed here, and *not* derivable from the Bałaban source pack: `hmem`, the
response of the **coefficients** — the Gaussian coefficient `β_Z`, the spectra
`λ`, and the Taylor coefficients `a_n` — to the earlier history at frozen
coupling, in the geometrically forgetting form
`Σ_{k≤j}C_mem θ_mem^{j−k}s_k|u_k(p) − u_k(q)|`.  No marginal direction is given a
forgetting law: the marginal coupling is carried by the explicit trajectory
recursion and appears as the diagonal of the kernel.  Row A is therefore not
closed by this file; what it removes is the need for any unsourced constant in
the *direct* sensitivity, and it isolates the one remaining physical input.
-/
import RequestProject.YangMills.LiteralChannelSensitivity
import RequestProject.YangMills.InverseCouplingSensitivity
import RequestProject.YangMills.RowASensitivityBootstrap

namespace YangMills

open Finset

/-! ## 1. The trajectory floor on the tube -/

/-- On the admissible tube the generated trajectory inherits the linear floor of
the shell coefficient. -/
theorem shootingTrajectory_floor {bet : ℕ → ℝ → ℝ} {u₀ bl p : ℝ}
    (hp : u₀ ≤ p) (hb : ∀ i, bl ≤ bet i p) (j : ℕ) :
    u₀ + bl * j ≤ shootingTrajectory bet p j := by
  have hsum : bl * j ≤ ∑ i ∈ range j, bet i p := by
    calc bl * j = ∑ _i ∈ range j, bl := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ ∑ i ∈ range j, bet i p := Finset.sum_le_sum fun i _ => hb i
  rw [shootingTrajectory]
  linarith

/-! ## 2. The marginal weight `s_j = (C_dir/2)·g_j⁶` -/

/-- The per-shell marginal sensitivity weight in the shooting coordinate:
`s_j = (C_dir/2)·(u₀ + b j)^{-3} = (C_dir/2)·g_j⁶`.  The cube comes from the
cubic channel derivative *times* the cubic Jacobian `dg/du = −½g³`. -/
noncomputable def literalMarginalWeight (Cdir u₀ bl : ℝ) (j : ℕ) : ℝ :=
  (Cdir / 2) * ((u₀ + bl * j) ^ 3)⁻¹

theorem literalMarginalWeight_nonneg {Cdir u₀ bl : ℝ} (hC : 0 ≤ Cdir) (hu₀ : 0 < u₀)
    (hbl : 0 < bl) (j : ℕ) : 0 ≤ literalMarginalWeight Cdir u₀ bl j := by
  have hx : 0 < u₀ + bl * j := by
    have : (0 : ℝ) ≤ bl * j := by positivity
    linarith
  rw [literalMarginalWeight]
  positivity

/-- **The weights are summable with an `u₀⁻²` gain**, uniformly in the cutoff. -/
theorem literalMarginalWeight_sum_le {Cdir u₀ bl : ℝ} (hC : 0 ≤ Cdir) (hu₀ : 0 < u₀)
    (hbl : 0 < bl) (J : ℕ) :
    ∑ k ∈ range J, literalMarginalWeight Cdir u₀ bl k
      ≤ (Cdir / 2) * ((u₀ ^ 3)⁻¹ + 1 / (2 * bl * u₀ ^ 2)) := by
  have h := sum_inv_cube_linear_le (u₀ := u₀) (b := bl) hu₀ hbl J
  calc ∑ k ∈ range J, literalMarginalWeight Cdir u₀ bl k
      = (Cdir / 2) * ∑ k ∈ range J, ((u₀ + bl * k) ^ 3)⁻¹ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => rfl
    _ ≤ (Cdir / 2) * ((u₀ ^ 3)⁻¹ + 1 / (2 * bl * u₀ ^ 2)) :=
        mul_le_mul_of_nonneg_left h (by positivity)

/-- **The total response mass of the literal kernel**: the marginal weights
resummed, times the factor `1 + C_mem/(1−θ_mem)` contributed by the geometrically
forgetting coefficient response. -/
noncomputable def literalKernelMass (Cdir Cmem thmem u₀ bl : ℝ) : ℝ :=
  (1 + Cmem / (1 - thmem)) * ((Cdir / 2) * ((u₀ ^ 3)⁻¹ + 1 / (2 * bl * u₀ ^ 2)))

/-- **The smallness criterion.**  `u₀² > (1 + C_mem/(1−θ))·C_dir·(1 + 1/(2b))`
and `u₀ ≥ 1` force the total kernel mass below `1/2`, which is exactly the
condition under which the shooting map contracts.  Equivalently: a sufficiently
small bare coupling. -/
theorem literal_sigma_lt_half {Cdir Cmem thmem u₀ bl : ℝ}
    (hC : 0 ≤ Cdir) (hCmem : 0 ≤ Cmem) (hthm1 : thmem < 1)
    (hbl : 0 < bl) (hu₀ : 1 ≤ u₀)
    (hbig : (1 + Cmem / (1 - thmem)) * Cdir * (1 + 1 / (2 * bl)) < u₀ ^ 2) :
    literalKernelMass Cdir Cmem thmem u₀ bl < 1 / 2 := by
  rw [literalKernelMass]
  have hu0 : 0 < u₀ := lt_of_lt_of_le one_pos hu₀
  have hden : 0 < 1 - thmem := by linarith
  have hfac : 0 ≤ 1 + Cmem / (1 - thmem) := by positivity
  have hsq : 0 < u₀ ^ 2 := by positivity
  -- `u₀⁻³ ≤ u₀⁻²` because `u₀ ≥ 1`
  have hcube : (u₀ ^ 3)⁻¹ ≤ (u₀ ^ 2)⁻¹ := by
    have h : u₀ ^ 2 ≤ u₀ ^ 3 := by nlinarith
    exact inv_anti₀ hsq h
  have hsum : (u₀ ^ 3)⁻¹ + 1 / (2 * bl * u₀ ^ 2) ≤ (1 + 1 / (2 * bl)) * (u₀ ^ 2)⁻¹ := by
    have h1 : 1 / (2 * bl * u₀ ^ 2) = (1 / (2 * bl)) * (u₀ ^ 2)⁻¹ := by
      field_simp
    rw [h1]
    have : (1 + 1 / (2 * bl)) * (u₀ ^ 2)⁻¹ = (u₀ ^ 2)⁻¹ + (1 / (2 * bl)) * (u₀ ^ 2)⁻¹ := by ring
    rw [this]
    linarith
  have hstep : (1 + Cmem / (1 - thmem)) * ((Cdir / 2) * ((u₀ ^ 3)⁻¹ + 1 / (2 * bl * u₀ ^ 2)))
      ≤ (1 + Cmem / (1 - thmem)) * ((Cdir / 2) * ((1 + 1 / (2 * bl)) * (u₀ ^ 2)⁻¹)) := by
    refine mul_le_mul_of_nonneg_left ?_ hfac
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  have hfin : (1 + Cmem / (1 - thmem)) * ((Cdir / 2) * ((1 + 1 / (2 * bl)) * (u₀ ^ 2)⁻¹)) < 1 / 2 := by
    have hkey : (1 + Cmem / (1 - thmem)) * Cdir * (1 + 1 / (2 * bl)) * (u₀ ^ 2)⁻¹ < 1 := by
      rw [mul_inv_lt_iff₀ hsq]
      linarith [hbig]
    have hrw : (1 + Cmem / (1 - thmem)) * ((Cdir / 2) * ((1 + 1 / (2 * bl)) * (u₀ ^ 2)⁻¹))
        = ((1 + Cmem / (1 - thmem)) * Cdir * (1 + 1 / (2 * bl)) * (u₀ ^ 2)⁻¹) / 2 := by ring
    rw [hrw]
    linarith
  linarith

/-! ## 3. The literal response kernel -/

/-- The shell coefficient with its history coefficients frozen at the bare
coupling `p`, read as a function of the coupling: exactly the shape produced by
`shellBetaOfSources`. -/
noncomputable def literalShellAt {ι κ : Type*} [Fintype ι] [Fintype κ]
    (betaZ : ℕ → ℝ → ℝ) (lamD : ℕ → ℝ → ι → ℝ) (lamG : ℕ → ℝ → κ → ℝ)
    (aI aC aL : ℕ → ℝ → ℕ → ℝ) (N : ℕ) (j : ℕ) (p g : ℝ) : ℝ :=
  betaZ j p + frozenShellInteraction (lamD j p) (lamG j p) (aI j p) (aC j p) (aL j p) N g

/-- **The literal direct (marginal) sensitivity, in the shooting coordinate.**
Differentiating the source majorants gives a cubic constant in the coupling; the
`u = g⁻²` Jacobian gives a second cubic factor; the result is the weight
`s_j = (C_dir/2)g_j⁶` multiplying the *trajectory* difference at the same scale.
The Gaussian coefficient `β_Z` drops out of this estimate: it carries no direct
coupling dependence, only history dependence. -/
theorem literal_direct_sensitivity {ι κ : Type*} [Fintype ι] [Fintype κ]
    {betaZ : ℕ → ℝ → ℝ} {lamD : ℕ → ℝ → ι → ℝ} {lamG : ℕ → ℝ → κ → ℝ}
    {aI aC aL : ℕ → ℝ → ℕ → ℝ} {N : ℕ}
    {LamDet LamGauge theta AI AC AL Kmaj rho Cdir u₀ bl p x y : ℝ} {j : ℕ}
    (hLd : ∀ i, |lamD j p i| ≤ LamDet) (hLg : ∀ i, |lamG j p i| ≤ LamGauge)
    (hLd0 : 0 ≤ LamDet) (hLg0 : 0 ≤ LamGauge)
    (hI : ∀ n, |aI j p n| ≤ AI * Kmaj ^ (n + 4)) (hC : ∀ n, |aC j p n| ≤ AC * Kmaj ^ (n + 4))
    (hLc : ∀ n, |aL j p n| ≤ AL * Kmaj ^ (n + 4))
    (hAI : 0 ≤ AI) (hAC : 0 ≤ AC) (hAL : 0 ≤ AL) (hK : 0 ≤ Kmaj)
    (hGLd : couplingOf u₀ * LamDet ≤ theta) (hGLg : couplingOf u₀ * LamGauge ≤ theta)
    (hth : theta < 1) (hrho : Kmaj * couplingOf u₀ ≤ rho) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hCdir : analyticDirectSensitivityBound (Fintype.card ι) (Fintype.card κ)
      LamDet LamGauge theta AI AC AL Kmaj rho ≤ Cdir)
    (hu₀ : 0 < u₀) (hbl : 0 < bl) (hx : u₀ + bl * j ≤ x) (hy : u₀ + bl * j ≤ y) :
    |literalShellAt betaZ lamD lamG aI aC aL N j p (couplingOf x)
        - literalShellAt betaZ lamD lamG aI aC aL N j p (couplingOf y)|
      ≤ literalMarginalWeight Cdir u₀ bl j * |x - y| := by
  have hxj : (0 : ℝ) < u₀ + bl * j := by
    have : (0 : ℝ) ≤ bl * j := by positivity
    linarith
  set G : ℝ := couplingOf (u₀ + bl * j) with hG
  have hG0 : 0 ≤ G := couplingOf_nonneg _
  have hGle : G ≤ couplingOf u₀ := by
    refine couplingOf_le hu₀ ?_
    have : (0 : ℝ) ≤ bl * j := by positivity
    linarith
  have hgx : couplingOf x ≤ G := couplingOf_le hxj hx
  have hgy : couplingOf y ≤ G := couplingOf_le hxj hy
  -- the small-field conditions inherit from the bare end
  have hGLd' : G * LamDet ≤ theta :=
    le_trans (mul_le_mul_of_nonneg_right hGle hLd0) hGLd
  have hGLg' : G * LamGauge ≤ theta :=
    le_trans (mul_le_mul_of_nonneg_right hGle hLg0) hGLg
  have hrho' : Kmaj * G ≤ rho := le_trans (mul_le_mul_of_nonneg_left hGle hK) hrho
  -- the differentiated channel bound
  have hchan := abs_frozenShellInteraction_sub_le
    (lamD := lamD j p) (lamG := lamG j p) (aI := aI j p) (aC := aC j p) (aL := aL j p)
    (N := N) (LamDet := LamDet) (LamGauge := LamGauge) (theta := theta)
    (AI := AI) (AC := AC) (AL := AL) (K := Kmaj) (G := G) (rho := rho)
    (g := couplingOf x) (h := couplingOf y)
    hLd hLg hLd0 hLg0 hI hC hLc hAI hAC hAL hK
    (couplingOf_nonneg x) (couplingOf_nonneg y) hgx hgy hGLd' hGLg' hth hrho' hrho0 hrho1
  -- the Jacobian of the shooting coordinate
  have hjac := abs_couplingOf_sub_le (u₀ := u₀ + bl * j) (u := x) (v := y) hxj hx hy
  have hdiff : literalShellAt betaZ lamD lamG aI aC aL N j p (couplingOf x)
      - literalShellAt betaZ lamD lamG aI aC aL N j p (couplingOf y)
      = frozenShellInteraction (lamD j p) (lamG j p) (aI j p) (aC j p) (aL j p) N (couplingOf x)
        - frozenShellInteraction (lamD j p) (lamG j p) (aI j p) (aC j p) (aL j p) N
            (couplingOf y) := by
    rw [literalShellAt, literalShellAt]; ring
  have hCdir0 : 0 ≤ analyticDirectSensitivityBound (Fintype.card ι) (Fintype.card κ)
      LamDet LamGauge theta AI AC AL Kmaj rho :=
    analyticDirectSensitivityBound_nonneg hth hAI hAC hAL hrho1
  have hCd0 : 0 ≤ Cdir := le_trans hCdir0 hCdir
  -- chain the two estimates
  have hstep1 : |literalShellAt betaZ lamD lamG aI aC aL N j p (couplingOf x)
      - literalShellAt betaZ lamD lamG aI aC aL N j p (couplingOf y)|
      ≤ Cdir * G ^ 3 * |couplingOf x - couplingOf y| := by
    rw [hdiff]
    refine le_trans hchan ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCdir (by positivity)) (abs_nonneg _)
  have hstep2 : Cdir * G ^ 3 * |couplingOf x - couplingOf y|
      ≤ Cdir * G ^ 3 * ((1 / 2) * G ^ 3 * |x - y|) :=
    mul_le_mul_of_nonneg_left hjac (by positivity)
  have hG6 : G ^ 3 * G ^ 3 = ((u₀ + bl * j) ^ 3)⁻¹ := by
    have hsq : G ^ 2 = (u₀ + bl * j)⁻¹ := couplingOf_sq hxj.le
    calc G ^ 3 * G ^ 3 = (G ^ 2) ^ 3 := by ring
      _ = ((u₀ + bl * j)⁻¹) ^ 3 := by rw [hsq]
      _ = ((u₀ + bl * j) ^ 3)⁻¹ := by rw [inv_pow]
  have hval : Cdir * G ^ 3 * ((1 / 2) * G ^ 3 * |x - y|)
      = literalMarginalWeight Cdir u₀ bl j * |x - y| := by
    rw [literalMarginalWeight, ← hG6]
    ring
  linarith [hstep1, hstep2, hval.le, hval.ge]

/-! ## 4. The literal response kernel -/

/-- **The mass of the literal response kernel.**  The marginal weights are
resummed with the `u₀⁻²` gain, and the geometrically forgetting coefficient
response multiplies that by `1 + C_mem/(1−θ_mem)` — it can add to the marginal
sensitivity, but it cannot replace it. -/
theorem literal_kernel_mass_le {Cdir Cmem thmem u₀ bl : ℝ}
    (hCd0 : 0 ≤ Cdir) (hCmem : 0 ≤ Cmem) (hthm0 : 0 ≤ thmem) (hthm1 : thmem < 1)
    (hu₀ : 0 < u₀) (hbl : 0 < bl) (J : ℕ) :
    ∑ j ∈ range J, kernelRow (splitKernel Cmem thmem (literalMarginalWeight Cdir u₀ bl)) j
      ≤ literalKernelMass Cdir Cmem thmem u₀ bl :=
  splitKernel_mass_le hCmem hthm0 hthm1
    (fun k => literalMarginalWeight_nonneg hCd0 hu₀ hbl k)
    (fun J' => literalMarginalWeight_sum_le hCd0 hu₀ hbl J') J

/-- **The literal shell coefficient obeys a response-kernel estimate.**  Its
diagonal is the *derived* marginal weight `s_j = (C_dir/2)·g_j⁶` — the
differentiated source majorants composed with the Jacobian of `u = g⁻²` — and its
off-diagonal part is the assumed, geometrically forgetting, coefficient
response.  This is the estimate the bootstrap consumes. -/
theorem literal_response_kernel
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {bet betaZ : ℕ → ℝ → ℝ} {lamD : ℕ → ℝ → ι → ℝ} {lamG : ℕ → ℝ → κ → ℝ}
    {aI aC aL : ℕ → ℝ → ℕ → ℝ} {N : ℕ}
    {LamDet LamGauge theta AI AC AL Kmaj rho Cdir Cmem thmem u₀ bl : ℝ}
    (hstruct : ∀ j p, u₀ ≤ p → bet j p
      = literalShellAt betaZ lamD lamG aI aC aL N j p
          (couplingOf (shootingTrajectory bet p j)))
    (hLd : ∀ j p i, |lamD j p i| ≤ LamDet) (hLg : ∀ j p i, |lamG j p i| ≤ LamGauge)
    (hLd0 : 0 ≤ LamDet) (hLg0 : 0 ≤ LamGauge)
    (hI : ∀ j p n, |aI j p n| ≤ AI * Kmaj ^ (n + 4))
    (hC : ∀ j p n, |aC j p n| ≤ AC * Kmaj ^ (n + 4))
    (hLc : ∀ j p n, |aL j p n| ≤ AL * Kmaj ^ (n + 4))
    (hAI : 0 ≤ AI) (hAC : 0 ≤ AC) (hAL : 0 ≤ AL) (hK : 0 ≤ Kmaj)
    (hGLd : couplingOf u₀ * LamDet ≤ theta) (hGLg : couplingOf u₀ * LamGauge ≤ theta)
    (hth : theta < 1) (hrho : Kmaj * couplingOf u₀ ≤ rho) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hCdir : analyticDirectSensitivityBound (Fintype.card ι) (Fintype.card κ)
      LamDet LamGauge theta AI AC AL Kmaj rho ≤ Cdir)
    (hmem : ∀ j p q g, u₀ ≤ p → u₀ ≤ q →
      |literalShellAt betaZ lamD lamG aI aC aL N j p g
          - literalShellAt betaZ lamD lamG aI aC aL N j q g|
        ≤ ∑ k ∈ range (j + 1), Cmem * thmem ^ (j - k)
            * literalMarginalWeight Cdir u₀ bl k
            * |shootingTrajectory bet p k - shootingTrajectory bet q k|)
    (hu₀ : 0 < u₀) (hbl : 0 < bl) (hlow : ∀ j p, u₀ ≤ p → bl ≤ bet j p) :
    ∀ j p q, u₀ ≤ p → u₀ ≤ q →
      |bet j p - bet j q| ≤ ∑ k ∈ range (j + 1),
        splitKernel Cmem thmem (literalMarginalWeight Cdir u₀ bl) j k
          * |shootingTrajectory bet p k - shootingTrajectory bet q k| := by
  intro j p q hp hq
  have hfloor : ∀ r, u₀ ≤ r → ∀ i, u₀ + bl * i ≤ shootingTrajectory bet r i := fun r hr i =>
    shootingTrajectory_floor hr (fun i' => hlow i' r hr) i
  have hdir := literal_direct_sensitivity
    (betaZ := betaZ) (lamD := lamD) (lamG := lamG) (aI := aI) (aC := aC) (aL := aL)
    (N := N) (LamDet := LamDet) (LamGauge := LamGauge) (theta := theta)
    (AI := AI) (AC := AC) (AL := AL) (Kmaj := Kmaj) (rho := rho) (Cdir := Cdir)
    (u₀ := u₀) (bl := bl) (p := p) (j := j)
    (x := shootingTrajectory bet p j) (y := shootingTrajectory bet q j)
    (fun i => hLd j p i) (fun i => hLg j p i) hLd0 hLg0
    (fun n => hI j p n) (fun n => hC j p n) (fun n => hLc j p n)
    hAI hAC hAL hK hGLd hGLg hth hrho hrho0 hrho1 hCdir hu₀ hbl
    (hfloor p hp j) (hfloor q hq j)
  have hmm := hmem j p q (couplingOf (shootingTrajectory bet q j)) hp hq
  have htri : |bet j p - bet j q|
      ≤ |literalShellAt betaZ lamD lamG aI aC aL N j p
            (couplingOf (shootingTrajectory bet p j))
          - literalShellAt betaZ lamD lamG aI aC aL N j p
            (couplingOf (shootingTrajectory bet q j))|
        + |literalShellAt betaZ lamD lamG aI aC aL N j p
            (couplingOf (shootingTrajectory bet q j))
          - literalShellAt betaZ lamD lamG aI aC aL N j q
            (couplingOf (shootingTrajectory bet q j))| := by
    rw [hstruct j p hp, hstruct j q hq]
    exact abs_sub_le _ _ _
  have hrowsplit : ∑ k ∈ range (j + 1),
      splitKernel Cmem thmem (literalMarginalWeight Cdir u₀ bl) j k
        * |shootingTrajectory bet p k - shootingTrajectory bet q k|
      = literalMarginalWeight Cdir u₀ bl j
          * |shootingTrajectory bet p j - shootingTrajectory bet q j|
        + ∑ k ∈ range (j + 1), Cmem * thmem ^ (j - k) * literalMarginalWeight Cdir u₀ bl k
            * |shootingTrajectory bet p k - shootingTrajectory bet q k| := by
    simp only [splitKernel, add_mul]
    rw [Finset.sum_add_distrib]
    congr 1
    simp
  rw [hrowsplit]
  linarith [htri, hdir, hmm]

/-! ## 5. The target inequality: the literal cumulative beta map contracts -/

/-- **The literal cumulative beta map is `q`-Lipschitz with `q < 1` on the
admissible tube.**  With `𝓑_K(p) = Σ_{j<K}β_j(p)` the literal history-dependent
cumulative beta correction generated by the bare inverse coupling `p`,

    |𝓑_K(p) − 𝓑_K(q)| ≤ q·|p − q|,     q = σ/(1−σ) < 1,

uniformly in the cutoff `K`, where `σ` is the total response mass
`literalKernelMass`.  By `literal_sigma_lt_half`, `σ < 1/2` — hence `q < 1` —
holds as soon as the bare coupling is small enough,
`u₀² > (1 + C_mem/(1−θ_mem))·C_dir·(1 + 1/(2b))`. -/
theorem literal_cumulative_beta_contraction
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {bet betaZ : ℕ → ℝ → ℝ} {lamD : ℕ → ℝ → ι → ℝ} {lamG : ℕ → ℝ → κ → ℝ}
    {aI aC aL : ℕ → ℝ → ℕ → ℝ} {N : ℕ}
    {LamDet LamGauge theta AI AC AL Kmaj rho Cdir Cmem thmem u₀ bl : ℝ}
    (hstruct : ∀ j p, u₀ ≤ p → bet j p
      = literalShellAt betaZ lamD lamG aI aC aL N j p
          (couplingOf (shootingTrajectory bet p j)))
    (hLd : ∀ j p i, |lamD j p i| ≤ LamDet) (hLg : ∀ j p i, |lamG j p i| ≤ LamGauge)
    (hLd0 : 0 ≤ LamDet) (hLg0 : 0 ≤ LamGauge)
    (hI : ∀ j p n, |aI j p n| ≤ AI * Kmaj ^ (n + 4))
    (hC : ∀ j p n, |aC j p n| ≤ AC * Kmaj ^ (n + 4))
    (hLc : ∀ j p n, |aL j p n| ≤ AL * Kmaj ^ (n + 4))
    (hAI : 0 ≤ AI) (hAC : 0 ≤ AC) (hAL : 0 ≤ AL) (hK : 0 ≤ Kmaj)
    (hGLd : couplingOf u₀ * LamDet ≤ theta) (hGLg : couplingOf u₀ * LamGauge ≤ theta)
    (hth : theta < 1) (hrho : Kmaj * couplingOf u₀ ≤ rho) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hCdir : analyticDirectSensitivityBound (Fintype.card ι) (Fintype.card κ)
      LamDet LamGauge theta AI AC AL Kmaj rho ≤ Cdir)
    (hmem : ∀ j p q g, u₀ ≤ p → u₀ ≤ q →
      |literalShellAt betaZ lamD lamG aI aC aL N j p g
          - literalShellAt betaZ lamD lamG aI aC aL N j q g|
        ≤ ∑ k ∈ range (j + 1), Cmem * thmem ^ (j - k)
            * literalMarginalWeight Cdir u₀ bl k
            * |shootingTrajectory bet p k - shootingTrajectory bet q k|)
    (hCmem : 0 ≤ Cmem) (hthm0 : 0 ≤ thmem) (hthm1 : thmem < 1)
    (hu₀ : 0 < u₀) (hbl : 0 < bl) (hlow : ∀ j p, u₀ ≤ p → bl ≤ bet j p)
    (hsig : literalKernelMass Cdir Cmem thmem u₀ bl < 1 / 2) :
    (∀ (K : ℕ) (p q : ℝ), u₀ ≤ p → u₀ ≤ q →
        |∑ j ∈ range K, bet j p - ∑ j ∈ range K, bet j q|
          ≤ (literalKernelMass Cdir Cmem thmem u₀ bl
              / (1 - literalKernelMass Cdir Cmem thmem u₀ bl)) * |p - q|)
      ∧ literalKernelMass Cdir Cmem thmem u₀ bl
          / (1 - literalKernelMass Cdir Cmem thmem u₀ bl) < 1 := by
  have hCdir0 : 0 ≤ analyticDirectSensitivityBound (Fintype.card ι) (Fintype.card κ)
      LamDet LamGauge theta AI AC AL Kmaj rho :=
    analyticDirectSensitivityBound_nonneg hth hAI hAC hAL hrho1
  have hCd0 : 0 ≤ Cdir := le_trans hCdir0 hCdir
  have hw0 : ∀ j k, 0 ≤ splitKernel Cmem thmem (literalMarginalWeight Cdir u₀ bl) j k :=
    fun j k => splitKernel_nonneg hCmem hthm0
      (fun k' => literalMarginalWeight_nonneg hCd0 hu₀ hbl k') j k
  have hker := literal_response_kernel hstruct hLd hLg hLd0 hLg0 hI hC hLc
    hAI hAC hAL hK hGLd hGLg hth hrho hrho0 hrho1 hCdir hmem hu₀ hbl hlow
  have hmass := literal_kernel_mass_le (Cdir := Cdir) (Cmem := Cmem) (thmem := thmem)
    (u₀ := u₀) (bl := bl) hCd0 hCmem hthm0 hthm1 hu₀ hbl
  have hsig0 : 0 ≤ literalKernelMass Cdir Cmem thmem u₀ bl := by
    have h := hmass 0
    simpa using h
  have hsig1 : literalKernelMass Cdir Cmem thmem u₀ bl < 1 := by linarith
  obtain ⟨hq1, -⟩ := kernel_q_lt_one hsig0 hsig
  exact ⟨fun K p q hp hq =>
    cumulative_beta_lipschitz_of_kernel hw0 hker hmass hsig1 hp hq K, hq1⟩

/-! ## 6. The completion predicate for the literal shell coefficient -/

/-- **Row A's completion predicate for the literal shell coefficient, at
sufficiently small bare coupling.**

The shell coefficient is literal: `β_j(p) = β_{Z,j}(p) + Σ(five source channels
with history-`p` coefficients)`, evaluated at the effective coupling
`g_j(p) = u_j(p)^{-1/2}` of the trajectory generated by `p` itself.  The direct
coupling sensitivity is *derived* from the same source norms that bound the
channels; the coefficient (history) response `hmem` is the remaining hypothesis,
and it is asked to forget geometrically only in the irrelevant directions — the
marginal coupling is carried by the trajectory recursion and never assigned a
forgetting law.  Every hypothesis is assumed only on the admissible small-field
tube `u ≥ u₀`. -/
theorem rowA_completion_of_literal_channels
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {bet betaZ : ℕ → ℝ → ℝ} {lamD : ℕ → ℝ → ι → ℝ} {lamG : ℕ → ℝ → κ → ℝ}
    {aI aC aL : ℕ → ℝ → ℕ → ℝ} {N : ℕ}
    {LamDet LamGauge theta AI AC AL Kmaj rho Cdir Cmem thmem : ℝ}
    {bZm bZp eps u₀ target : ℝ} {K : ℕ}
    (hstruct : ∀ j p, u₀ ≤ p → bet j p
      = literalShellAt betaZ lamD lamG aI aC aL N j p
          (couplingOf (shootingTrajectory bet p j)))
    (hLd : ∀ j p i, |lamD j p i| ≤ LamDet) (hLg : ∀ j p i, |lamG j p i| ≤ LamGauge)
    (hLd0 : 0 ≤ LamDet) (hLg0 : 0 ≤ LamGauge)
    (hI : ∀ j p n, |aI j p n| ≤ AI * Kmaj ^ (n + 4))
    (hC : ∀ j p n, |aC j p n| ≤ AC * Kmaj ^ (n + 4))
    (hLc : ∀ j p n, |aL j p n| ≤ AL * Kmaj ^ (n + 4))
    (hAI : 0 ≤ AI) (hAC : 0 ≤ AC) (hAL : 0 ≤ AL) (hK : 0 ≤ Kmaj)
    (hGLd : couplingOf u₀ * LamDet ≤ theta) (hGLg : couplingOf u₀ * LamGauge ≤ theta)
    (hth : theta < 1) (hrho : Kmaj * couplingOf u₀ ≤ rho) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hCdir : analyticDirectSensitivityBound (Fintype.card ι) (Fintype.card κ)
      LamDet LamGauge theta AI AC AL Kmaj rho ≤ Cdir)
    (hZl : ∀ j p, u₀ ≤ p → bZm ≤ betaZ j p) (hZu : ∀ j p, u₀ ≤ p → betaZ j p ≤ bZp)
    (hIntEps : ∀ j p, u₀ ≤ p →
      |frozenShellInteraction (lamD j p) (lamG j p) (aI j p) (aC j p) (aL j p) N
        (couplingOf (shootingTrajectory bet p j))| ≤ eps)
    (hmem : ∀ j p q g, u₀ ≤ p → u₀ ≤ q →
      |literalShellAt betaZ lamD lamG aI aC aL N j p g
          - literalShellAt betaZ lamD lamG aI aC aL N j q g|
        ≤ ∑ k ∈ range (j + 1), Cmem * thmem ^ (j - k)
            * literalMarginalWeight Cdir u₀ (bZm - eps) k
            * |shootingTrajectory bet p k - shootingTrajectory bet q k|)
    (hCmem : 0 ≤ Cmem) (hthm0 : 0 ≤ thmem) (hthm1 : thmem < 1)
    (hu₀ : 0 < u₀) (hepsm : eps < bZm)
    (hsig : literalKernelMass Cdir Cmem thmem u₀ (bZm - eps) < 1 / 2)
    (hwin : 0 < target - (bZp + eps) * K) (htube : u₀ ≤ target - (bZp + eps) * K) :
    RowACompletion bet K target (bZm - eps) (bZp + eps) (target - (bZp + eps) * K)⁻¹ := by
  classical
  have hbl : (0 : ℝ) < bZm - eps := by linarith
  have hCdir0 : 0 ≤ analyticDirectSensitivityBound (Fintype.card ι) (Fintype.card κ)
      LamDet LamGauge theta AI AC AL Kmaj rho :=
    analyticDirectSensitivityBound_nonneg hth hAI hAC hAL hrho1
  have hCd0 : 0 ≤ Cdir := le_trans hCdir0 hCdir
  -- the shell coefficient is trapped on the tube
  have hlow : ∀ j p, u₀ ≤ p → bZm - eps ≤ bet j p := by
    intro j p hp
    have h := abs_le.mp (hIntEps j p hp)
    rw [hstruct j p hp, literalShellAt]
    have := hZl j p hp
    linarith [h.1]
  have hup : ∀ j p, u₀ ≤ p → bet j p ≤ bZp + eps := by
    intro j p hp
    have h := abs_le.mp (hIntEps j p hp)
    rw [hstruct j p hp, literalShellAt]
    have := hZu j p hp
    linarith [h.2]
  -- the response kernel, its mass, and the resulting contraction factor
  have hw0 : ∀ j k,
      0 ≤ splitKernel Cmem thmem (literalMarginalWeight Cdir u₀ (bZm - eps)) j k :=
    fun j k => splitKernel_nonneg hCmem hthm0
      (fun k' => literalMarginalWeight_nonneg hCd0 hu₀ hbl k') j k
  have hker := literal_response_kernel hstruct hLd hLg hLd0 hLg0 hI hC hLc
    hAI hAC hAL hK hGLd hGLg hth hrho hrho0 hrho1 hCdir hmem hu₀ hbl hlow
  have hmass := literal_kernel_mass_le (Cdir := Cdir) (Cmem := Cmem) (thmem := thmem)
    (u₀ := u₀) (bl := bZm - eps) hCd0 hCmem hthm0 hthm1 hu₀ hbl
  have hsig0 : 0 ≤ literalKernelMass Cdir Cmem thmem u₀ (bZm - eps) := by
    have h := hmass 0
    simpa using h
  have hsig1 : literalKernelMass Cdir Cmem thmem u₀ (bZm - eps) < 1 := by linarith
  obtain ⟨hq1, hq0⟩ := kernel_q_lt_one hsig0 hsig
  have hden : 0 < 1 - literalKernelMass Cdir Cmem thmem u₀ (bZm - eps) := by linarith
  set w : ℕ → ℕ → ℝ := splitKernel Cmem thmem (literalMarginalWeight Cdir u₀ (bZm - eps))
    with hwdef
  have hL : ∀ j p q, u₀ ≤ p → u₀ ≤ q →
      |bet j p - bet j q|
        ≤ (kernelRow w j
            * (1 - literalKernelMass Cdir Cmem thmem u₀ (bZm - eps))⁻¹) * |p - q| :=
    fun j p q hp hq => shell_lipschitz_of_kernel hw0 hker hmass hsig1 hp hq j
  have hL0 : ∀ j, 0 ≤ kernelRow w j
      * (1 - literalKernelMass Cdir Cmem thmem u₀ (bZm - eps))⁻¹ := by
    intro j
    have h1 : 0 ≤ kernelRow w j := kernelRow_nonneg hw0 j
    positivity
  have hqK := cumulative_kernel_sensitivity_le hmass hsig1 K
  exact rowA_completion_of_tube_sensitivity
    (bet := bet) (betaZ := betaZ)
    (betaInt := fun j p => frozenShellInteraction (lamD j p) (lamG j p) (aI j p) (aC j p)
      (aL j p) N (couplingOf (shootingTrajectory bet p j)))
    (L := fun j => kernelRow w j
      * (1 - literalKernelMass Cdir Cmem thmem u₀ (bZm - eps))⁻¹)
    (q := literalKernelMass Cdir Cmem thmem u₀ (bZm - eps)
      / (1 - literalKernelMass Cdir Cmem thmem u₀ (bZm - eps)))
    (fun j p hp => by rw [hstruct j p hp, literalShellAt])
    hZl hZu hIntEps hL hL0 hqK hq0 hq1 hwin hepsm htube

end YangMills
