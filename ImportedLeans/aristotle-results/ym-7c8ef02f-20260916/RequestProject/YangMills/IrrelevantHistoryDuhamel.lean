/-
# Row A — the irrelevant history response, derived from a one-step contraction

`RowALiteralBetaSensitivity` reduces the Row-A contraction to two inputs: the
*direct* (marginal) sensitivity of the shell coefficient, which is derived there
from the differentiated source majorants, and the *coefficient* response
`hmem` — how the coefficients of the five channels at scale `j` react to a
change of the earlier history.  `hmem` was stated there in already-summed
convolution form

    |β_j(p; g) − β_j(q; g)| ≤ Σ_{k ≤ j} C_mem θ^{j−k} s_k |u_k(p) − u_k(q)|,

which is a strong shape to assume outright.  This file removes that: it proves
the convolution bound from the *local* data one actually has from a small-field
renormalisation-group step, namely

* the irrelevant state obeys a recursion `r_{j+1} = 𝓡_j(u_j, r_j)`;
* `𝓡_j` is a `θ`-contraction in the irrelevant state, `θ < 1` — this is imposed
  only on the irrelevant directions;
* `𝓡_j` is Lipschitz in the coupling with strength `D_j` — the coupling *drives*
  the irrelevant state, and in the shooting coordinate `u = g⁻²` that driving
  carries the same suppression as the marginal weight;
* the channel coefficients are Lipschitz functions of the irrelevant state;
* the initial irrelevant data is the same for both bare couplings, since only
  the coupling is being varied.

The marginal coupling direction is *not* given a forgetting law: it is carried
by the explicit trajectory recursion and enters the estimate only through the
differences `|u_k(p) − u_k(q)|` on the right-hand side.  This is exactly the
marginal/irrelevant split the shooting lane requires.

`irrelevant_response_duhamel` is the discrete variation-of-constants formula for
such a recursion, and `literal_mem_of_irrelevant_contraction` packages it into
precisely the `hmem` hypothesis consumed by
`literal_cumulative_beta_contraction` and `rowA_completion_of_literal_channels`.
-/
import RequestProject.YangMills.RowALiteralBetaSensitivity

namespace YangMills

open Finset

variable {E : Type*} [NormedAddCommGroup E]

/-! ## 1. The discrete Duhamel formula -/

/-- The Lipschitz strength of the coupling drive is nonnegative. -/
theorem drive_nonneg {R : ℕ → ℝ → E → E} {D : ℕ → ℝ}
    (hdrv : ∀ j a b x, ‖R j a x - R j b x‖ ≤ D j * |a - b|) (j : ℕ) : 0 ≤ D j := by
  have h := hdrv j 1 0 0
  have h1 : |(1 : ℝ) - 0| = 1 := by norm_num
  rw [h1, mul_one] at h
  exact le_trans (norm_nonneg _) h

/-- **Discrete Duhamel bound for the irrelevant history.**  If the irrelevant
state evolves by a recursion that contracts with factor `θ` in the state and is
`D_j`-Lipschitz in the coupling, and if the two histories start from the same
irrelevant data, then the response of the irrelevant state at scale `j` is the
convolution of the geometric kernel `θ^{j−1−k}` with the coupling differences:

    ‖r_j(p) − r_j(q)‖ ≤ Σ_{k<j} θ^{j−1−k} D_k |u_k(p) − u_k(q)|.

No forgetting is imposed on the coupling itself; the coupling appears only as
the drive. -/
theorem irrelevant_response_duhamel
    {R : ℕ → ℝ → E → E} {r : ℕ → ℝ → E} {u : ℕ → ℝ → ℝ} {thmem : ℝ} {D : ℕ → ℝ}
    (hr0 : ∀ p q, r 0 p = r 0 q)
    (hrec : ∀ j p, r (j + 1) p = R j (u j p) (r j p))
    (hcon : ∀ j g x y, ‖R j g x - R j g y‖ ≤ thmem * ‖x - y‖)
    (hdrv : ∀ j a b x, ‖R j a x - R j b x‖ ≤ D j * |a - b|)
    (hth0 : 0 ≤ thmem) :
    ∀ (j : ℕ) (p q : ℝ),
      ‖r j p - r j q‖ ≤ ∑ k ∈ range j, thmem ^ (j - 1 - k) * D k * |u k p - u k q| := by
  intro j
  induction j with
  | zero =>
      intro p q
      rw [hr0 p q]
      simp
  | succ j ih =>
      intro p q
      have hsplit : r (j + 1) p - r (j + 1) q
          = (R j (u j p) (r j p) - R j (u j p) (r j q))
            + (R j (u j p) (r j q) - R j (u j q) (r j q)) := by
        rw [hrec j p, hrec j q]; abel
      have htri : ‖r (j + 1) p - r (j + 1) q‖
          ≤ ‖R j (u j p) (r j p) - R j (u j p) (r j q)‖
            + ‖R j (u j p) (r j q) - R j (u j q) (r j q)‖ := by
        rw [hsplit]; exact norm_add_le _ _
      have h1 : ‖R j (u j p) (r j p) - R j (u j p) (r j q)‖ ≤ thmem * ‖r j p - r j q‖ :=
        hcon j _ _ _
      have h2 : ‖R j (u j p) (r j q) - R j (u j q) (r j q)‖ ≤ D j * |u j p - u j q| :=
        hdrv j _ _ _
      have h3 : thmem * ‖r j p - r j q‖
          ≤ thmem * ∑ k ∈ range j, thmem ^ (j - 1 - k) * D k * |u k p - u k q| :=
        mul_le_mul_of_nonneg_left (ih p q) hth0
      -- rewrite the target sum
      have hkey : ∑ k ∈ range (j + 1), thmem ^ (j + 1 - 1 - k) * D k * |u k p - u k q|
          = thmem * (∑ k ∈ range j, thmem ^ (j - 1 - k) * D k * |u k p - u k q|)
            + D j * |u j p - u j q| := by
        rw [Finset.sum_range_succ]
        have hlast : thmem ^ (j + 1 - 1 - j) * D j * |u j p - u j q|
            = D j * |u j p - u j q| := by
          have : j + 1 - 1 - j = 0 := by omega
          rw [this, pow_zero, one_mul]
        rw [hlast]
        have hbody : ∑ k ∈ range j, thmem ^ (j + 1 - 1 - k) * D k * |u k p - u k q|
            = thmem * ∑ k ∈ range j, thmem ^ (j - 1 - k) * D k * |u k p - u k q| := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k hk => ?_
          have hkj : k < j := Finset.mem_range.mp hk
          have hexp : j + 1 - 1 - k = (j - 1 - k) + 1 := by omega
          rw [hexp, pow_succ]
          ring
        rw [hbody]
      rw [hkey]
      linarith

/-! ## 2. The `hmem` hypothesis, derived -/

/-- **The coefficient (history) response of the literal shell coefficient,
derived from a one-step contraction of the irrelevant renormalisation-group
map.**  The hypotheses are local: a `θ`-contraction of the irrelevant map in the
irrelevant state, a Lipschitz drive by the coupling whose strength is dominated
by the marginal weight (`L_coef·D_k ≤ C_mem·θ·s_k`), Lipschitz dependence of the
channel coefficients on the irrelevant state, and equal initial irrelevant data.
The conclusion is exactly the `hmem` hypothesis consumed by the Row-A
contraction theorems, so this replaces an assumed convolution bound by a derived
one. -/
theorem literal_mem_of_irrelevant_contraction
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {betaZ : ℕ → ℝ → ℝ} {lamD : ℕ → ℝ → ι → ℝ} {lamG : ℕ → ℝ → κ → ℝ}
    {aI aC aL : ℕ → ℝ → ℕ → ℝ} {N : ℕ} {bet : ℕ → ℝ → ℝ}
    {R : ℕ → ℝ → E → E} {r : ℕ → ℝ → E} {D : ℕ → ℝ}
    {Lcoef Cmem thmem Cdir u₀ bl : ℝ}
    (hr0 : ∀ p q, r 0 p = r 0 q)
    (hrec : ∀ j p, r (j + 1) p = R j (shootingTrajectory bet p j) (r j p))
    (hcon : ∀ j g x y, ‖R j g x - R j g y‖ ≤ thmem * ‖x - y‖)
    (hdrv : ∀ j a b x, ‖R j a x - R j b x‖ ≤ D j * |a - b|)
    (hth0 : 0 ≤ thmem)
    (hlip : ∀ j p q g,
      |literalShellAt betaZ lamD lamG aI aC aL N j p g
        - literalShellAt betaZ lamD lamG aI aC aL N j q g| ≤ Lcoef * ‖r j p - r j q‖)
    (hLc0 : 0 ≤ Lcoef) (hCmem : 0 ≤ Cmem) (hCdir : 0 ≤ Cdir) (hu₀ : 0 < u₀) (hbl : 0 < bl)
    (hD : ∀ k, Lcoef * D k ≤ Cmem * thmem * literalMarginalWeight Cdir u₀ bl k) :
    ∀ (j : ℕ) (p q g : ℝ), u₀ ≤ p → u₀ ≤ q →
      |literalShellAt betaZ lamD lamG aI aC aL N j p g
          - literalShellAt betaZ lamD lamG aI aC aL N j q g|
        ≤ ∑ k ∈ range (j + 1), Cmem * thmem ^ (j - k)
            * literalMarginalWeight Cdir u₀ bl k
            * |shootingTrajectory bet p k - shootingTrajectory bet q k| := by
  intro j p q g _ _
  have hduh := irrelevant_response_duhamel (u := fun k v => shootingTrajectory bet v k)
    hr0 hrec hcon hdrv hth0 j p q
  set Δ : ℕ → ℝ := fun k =>
    |shootingTrajectory bet p k - shootingTrajectory bet q k| with hΔ
  have hΔ0 : ∀ k, 0 ≤ Δ k := fun k => abs_nonneg _
  have hs0 : ∀ k, 0 ≤ literalMarginalWeight Cdir u₀ bl k := fun k =>
    literalMarginalWeight_nonneg hCdir hu₀ hbl k
  -- step 1: Lipschitz in the irrelevant state, then Duhamel
  have hstep1 : |literalShellAt betaZ lamD lamG aI aC aL N j p g
      - literalShellAt betaZ lamD lamG aI aC aL N j q g|
      ≤ Lcoef * ∑ k ∈ range j, thmem ^ (j - 1 - k) * D k * Δ k :=
    le_trans (hlip j p q g) (mul_le_mul_of_nonneg_left hduh hLc0)
  -- step 2: absorb `L_coef·D_k` into `C_mem·θ·s_k`, restoring the exponent `j−k`
  have hstep2 : Lcoef * ∑ k ∈ range j, thmem ^ (j - 1 - k) * D k * Δ k
      ≤ ∑ k ∈ range j, Cmem * thmem ^ (j - k) * literalMarginalWeight Cdir u₀ bl k * Δ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hkj : k < j := Finset.mem_range.mp hk
    have hexp : j - k = (j - 1 - k) + 1 := by omega
    have hterm : Lcoef * (thmem ^ (j - 1 - k) * D k * Δ k)
        = (Lcoef * D k) * (thmem ^ (j - 1 - k) * Δ k) := by ring
    have htarget : Cmem * thmem ^ (j - k) * literalMarginalWeight Cdir u₀ bl k * Δ k
        = (Cmem * thmem * literalMarginalWeight Cdir u₀ bl k)
            * (thmem ^ (j - 1 - k) * Δ k) := by
      rw [hexp, pow_succ]
      ring
    rw [hterm, htarget]
    refine mul_le_mul_of_nonneg_right (hD k) ?_
    have : 0 ≤ thmem ^ (j - 1 - k) := pow_nonneg hth0 _
    exact mul_nonneg this (hΔ0 k)
  -- step 3: the missing `k = j` term is nonnegative
  have hstep3 : ∑ k ∈ range j, Cmem * thmem ^ (j - k)
        * literalMarginalWeight Cdir u₀ bl k * Δ k
      ≤ ∑ k ∈ range (j + 1), Cmem * thmem ^ (j - k)
        * literalMarginalWeight Cdir u₀ bl k * Δ k := by
    rw [Finset.sum_range_succ]
    have : 0 ≤ Cmem * thmem ^ (j - j) * literalMarginalWeight Cdir u₀ bl j * Δ j := by
      have h1 : 0 ≤ thmem ^ (j - j) := pow_nonneg hth0 _
      have := hs0 j
      have := hΔ0 j
      positivity
    linarith
  linarith

/-! ## 3. Row A from purely local renormalisation-group data -/

/-- **Row A's completion predicate from local data only.**  Every hypothesis is
a one-scale statement about the source objects:

* the five channels are bounded by their Cauchy/spectral source norms
  (`hLd`–`hLc`), which is what produces the *derived* direct sensitivity;
* the small-field radius holds at the bare end (`hGLd`, `hGLg`, `hrho`);
* the Gaussian coefficient sits in its window and the remainder is below the
  tolerance (`hZl`, `hZu`, `hIntEps`);
* the irrelevant renormalisation-group map contracts in the irrelevant state and
  is driven by the coupling with strength dominated by the marginal weight
  (`hcon`, `hdrv`, `hD`), and the coefficients depend Lipschitz-continuously on
  the irrelevant state (`hlip`);
* the bare coupling is small enough (`hsig`).

No convolution bound and no forgetting law for the marginal coupling is
assumed. -/
theorem rowA_completion_of_local_rg_data
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {bet betaZ : ℕ → ℝ → ℝ} {lamD : ℕ → ℝ → ι → ℝ} {lamG : ℕ → ℝ → κ → ℝ}
    {aI aC aL : ℕ → ℝ → ℕ → ℝ} {N : ℕ}
    {R : ℕ → ℝ → E → E} {r : ℕ → ℝ → E} {D : ℕ → ℝ}
    {LamDet LamGauge theta AI AC AL Kmaj rho Cdir Lcoef Cmem thmem : ℝ}
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
    (hr0 : ∀ p q, r 0 p = r 0 q)
    (hrec : ∀ j p, r (j + 1) p = R j (shootingTrajectory bet p j) (r j p))
    (hcon : ∀ j g x y, ‖R j g x - R j g y‖ ≤ thmem * ‖x - y‖)
    (hdrv : ∀ j a b x, ‖R j a x - R j b x‖ ≤ D j * |a - b|)
    (hlip : ∀ j p q g,
      |literalShellAt betaZ lamD lamG aI aC aL N j p g
        - literalShellAt betaZ lamD lamG aI aC aL N j q g| ≤ Lcoef * ‖r j p - r j q‖)
    (hLc0 : 0 ≤ Lcoef)
    (hD : ∀ k, Lcoef * D k ≤ Cmem * thmem * literalMarginalWeight Cdir u₀ (bZm - eps) k)
    (hCmem : 0 ≤ Cmem) (hthm0 : 0 ≤ thmem) (hthm1 : thmem < 1)
    (hu₀ : 0 < u₀) (hepsm : eps < bZm)
    (hsig : literalKernelMass Cdir Cmem thmem u₀ (bZm - eps) < 1 / 2)
    (hwin : 0 < target - (bZp + eps) * K) (htube : u₀ ≤ target - (bZp + eps) * K) :
    RowACompletion bet K target (bZm - eps) (bZp + eps) (target - (bZp + eps) * K)⁻¹ := by
  have hbl : (0 : ℝ) < bZm - eps := by linarith
  have hCdir0 : 0 ≤ analyticDirectSensitivityBound (Fintype.card ι) (Fintype.card κ)
      LamDet LamGauge theta AI AC AL Kmaj rho :=
    analyticDirectSensitivityBound_nonneg hth hAI hAC hAL hrho1
  have hCd0 : 0 ≤ Cdir := le_trans hCdir0 hCdir
  have hmem := literal_mem_of_irrelevant_contraction (bet := bet)
    (betaZ := betaZ) (lamD := lamD) (lamG := lamG) (aI := aI) (aC := aC) (aL := aL) (N := N)
    (R := R) (r := r) (D := D) (Lcoef := Lcoef) (Cmem := Cmem) (thmem := thmem)
    (Cdir := Cdir) (u₀ := u₀) (bl := bZm - eps)
    hr0 hrec hcon hdrv hthm0 hlip hLc0 hCmem hCd0 hu₀ hbl hD
  exact rowA_completion_of_literal_channels hstruct hLd hLg hLd0 hLg0 hI hC hLc
    hAI hAC hAL hK hGLd hGLg hth hrho hrho0 hrho1 hCdir hZl hZu hIntEps
    (fun j p q g hp hq => hmem j p q g hp hq)
    hCmem hthm0 hthm1 hu₀ hepsm hsig hwin htube

end YangMills
