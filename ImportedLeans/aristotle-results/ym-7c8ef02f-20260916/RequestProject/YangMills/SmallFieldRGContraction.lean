/-
# Row A — the irrelevant contraction factor and the coupling drive, derived

`IrrelevantHistoryDuhamel` reduced the Row-A cumulative-beta contraction to
strictly one-scale data, at the cost of three renormalisation-group constants
that were left as hypotheses:

* `θ < 1`, a uniform one-step contraction of the small-field renormalisation
  group restricted to the irrelevant directions;
* `D_j`, the Lipschitz strength with which the running coupling drives the
  irrelevant state, required to be dominated by the marginal weight
  `s_j = (C_dir/2)g_j⁶`;
* `L_coef`, the Lipschitz dependence of the channel coefficients on the
  irrelevant state.

This file derives the first two from structure rather than assuming numbers, and
turns the third into a *scale-independent* inequality between constants.

## 1. `θ < 1` is irrelevance

A block-spin step of block size `L > 1` acts on the coefficient of a local
operator of scaling dimension `dim o` by the factor `L^{4−dim o}`.  "Irrelevant"
means `dim o ≥ 4 + δ` for some `δ > 0`, and then the factor is at most `L^{−δ}`,
which is `< 1`.  `blockScaling_contract` and `rpow_neg_lt_one` make this exact:
the linear part of the step contracts the irrelevant sector in the supremum
norm, with the explicit factor `L^{−δ}`.  Adding a nonlinear remainder that is
`η`-Lipschitz in the state gives `rgStep_contract`, a genuine contraction with

    θ = L^{−δ} + η < 1   whenever   η < 1 − L^{−δ}.

So `θ` is not a transcribed constant: it is dimensional analysis plus smallness
of the remainder.

## 2. `D_j` is cubic generation seen in the shooting coordinate

The irrelevant sector is *generated* by the coupling, and in the small-field
expansion that generation starts at the quartic order whose derivative is cubic.
Assume therefore the one-scale generation bound

    ‖N_j(g, x) − N_j(g', x)‖ ≤ C_gen · g_j³ · |g − g'|,

with `g_j` the local coupling size.  Composing with the exact Jacobian of the
shooting coordinate `u = g⁻²` (`abs_couplingOf_sub_le`, `|g(a) − g(b)| ≤ ½g³|a−b|`)
gives, on the tube,

    ‖R_j(a, x) − R_j(b, x)‖ ≤ (C_gen/2)·g_j⁶·|a − b| = s_j^{(C_gen)}·|a − b|,

i.e. `D_j` is *exactly* a marginal weight with `C_gen` in place of `C_dir`
(`drive_of_cubic_generation`).  The domination hypothesis
`L_coef·D_k ≤ C_mem·θ·s_k` therefore collapses to the single scale-free
inequality

    L_coef · C_gen ≤ C_mem · θ · C_dir        (`literalMarginalWeight_dominate`),

which can always be met by enlarging `C_mem` — at the price of a larger bare
`u₀` in the smallness criterion, which the criterion allows.

## 3. What this leaves

`rowA_completion_of_scaling_rg_data` is Row A's completion predicate derived
from: the block-spin scaling structure of the irrelevant sector, an
`η`-Lipschitz nonlinear remainder with `η < 1 − L^{−δ}`, a cubic generation
bound, Lipschitz dependence of the channel coefficients on the irrelevant state,
the scale-free constant inequality, and sufficiently small bare coupling.  No
contraction factor, no drive strength, and no convolution bound is assumed.

**Honest status.**  Row A is still not closed.  What remains is to exhibit the
literal Bałaban small-field step in the above shape: a block-spin rescaling of an
irrelevant sector whose retained operators all have dimension `≥ 4 + δ`, plus a
remainder with `η < 1 − L^{−δ}` and cubic generation constant `C_gen`.  That is a
statement about the literal renormalisation-group map, and it is not proved here.
-/
import RequestProject.YangMills.IrrelevantHistoryDuhamel

namespace YangMills

open Finset

/-! ## 1. Irrelevance is contraction -/

section Scaling

variable {Op : Type*}

/-- The linear part of a block-spin step of block size `L`: the coefficient of an
operator of scaling dimension `dim o` is multiplied by `L^{4 − dim o}`. -/
noncomputable def blockScaling (L : ℝ) (dim : Op → ℝ) (r : Op → ℝ) : Op → ℝ :=
  fun o => L ^ (4 - dim o) * r o

/-- A strictly negative exponent of a base `> 1` gives a factor `< 1`. -/
theorem rpow_neg_lt_one {L delta : ℝ} (hL : 1 < L) (hd : 0 < delta) : L ^ (-delta) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg hL (by linarith)

theorem rpow_neg_nonneg {L delta : ℝ} (hL : 1 < L) : 0 ≤ L ^ (-delta) :=
  Real.rpow_nonneg (by linarith) _

/-- **Irrelevance is contraction.**  If every retained operator has scaling
dimension at least `4 + δ` with `δ > 0`, then the linear part of a block-spin
step of block size `L > 1` contracts the irrelevant sector in the supremum norm
by the explicit factor `L^{−δ} < 1`. -/
theorem blockScaling_contract [Fintype Op] {L delta : ℝ} {dim : Op → ℝ}
    (hL : 1 < L) (hdim : ∀ o, 4 + delta ≤ dim o) (r s : Op → ℝ) :
    ‖blockScaling L dim r - blockScaling L dim s‖ ≤ L ^ (-delta) * ‖r - s‖ := by
  have hL0 : (0 : ℝ) < L := by linarith
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun o => ?_
  have hpow : L ^ (4 - dim o) ≤ L ^ (-delta) :=
    Real.rpow_le_rpow_of_exponent_le hL.le (by linarith [hdim o])
  have hpow0 : (0 : ℝ) ≤ L ^ (4 - dim o) := Real.rpow_nonneg hL0.le _
  have hcomp : ‖(blockScaling L dim r - blockScaling L dim s) o‖
      = L ^ (4 - dim o) * ‖(r - s) o‖ := by
    simp only [blockScaling, Pi.sub_apply, Real.norm_eq_abs, ← mul_sub, abs_mul,
      abs_of_nonneg hpow0]
  rw [hcomp]
  have h1 : ‖(r - s) o‖ ≤ ‖r - s‖ := norm_le_pi_norm _ o
  have h2 : (0 : ℝ) ≤ ‖(r - s) o‖ := norm_nonneg _
  nlinarith [norm_nonneg (r - s)]

/-- One small-field renormalisation-group step on the irrelevant sector: the
block-spin rescaling plus a nonlinear remainder driven by the coupling.  The
second argument is the *inverse squared* coupling `u`, the coordinate the
shooting lane runs in. -/
noncomputable def rgStep (L : ℝ) (dim : Op → ℝ)
    (Nl : ℕ → ℝ → (Op → ℝ) → (Op → ℝ)) (j : ℕ) (u : ℝ) (r : Op → ℝ) : Op → ℝ :=
  blockScaling L dim r + Nl j (couplingOf u) r

/-- **The one-step contraction factor of the small-field map, derived.**
`θ = L^{−δ} + η`. -/
theorem rgStep_contract [Fintype Op] {L delta eta : ℝ} {dim : Op → ℝ}
    {Nl : ℕ → ℝ → (Op → ℝ) → (Op → ℝ)}
    (hL : 1 < L) (hdim : ∀ o, 4 + delta ≤ dim o)
    (hNl : ∀ j g x y, ‖Nl j g x - Nl j g y‖ ≤ eta * ‖x - y‖)
    (j : ℕ) (u : ℝ) (x y : Op → ℝ) :
    ‖rgStep L dim Nl j u x - rgStep L dim Nl j u y‖ ≤ (L ^ (-delta) + eta) * ‖x - y‖ := by
  have hsplit : rgStep L dim Nl j u x - rgStep L dim Nl j u y
      = (blockScaling L dim x - blockScaling L dim y)
        + (Nl j (couplingOf u) x - Nl j (couplingOf u) y) := by
    simp only [rgStep]; abel
  calc ‖rgStep L dim Nl j u x - rgStep L dim Nl j u y‖
      ≤ ‖blockScaling L dim x - blockScaling L dim y‖
          + ‖Nl j (couplingOf u) x - Nl j (couplingOf u) y‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ L ^ (-delta) * ‖x - y‖ + eta * ‖x - y‖ := by
        have := blockScaling_contract hL hdim x y
        have := hNl j (couplingOf u) x y
        linarith
    _ = (L ^ (-delta) + eta) * ‖x - y‖ := by ring

/-- The derived contraction factor really is `< 1` when the remainder is small
compared with the dimensional gap. -/
theorem rgStep_theta_lt_one {L delta eta : ℝ}
    (heta : eta < 1 - L ^ (-delta)) : L ^ (-delta) + eta < 1 := by
  linarith

theorem rgStep_theta_nonneg {L delta eta : ℝ} (hL : 1 < L) (heta0 : 0 ≤ eta) :
    0 ≤ L ^ (-delta) + eta :=
  add_nonneg (rpow_neg_nonneg hL) heta0

/-- The block-spin part cancels in the coupling difference: only the remainder
drives the irrelevant state. -/
theorem rgStep_drive (L : ℝ) (dim : Op → ℝ) (Nl : ℕ → ℝ → (Op → ℝ) → (Op → ℝ))
    (j : ℕ) (a b : ℝ) (x : Op → ℝ) :
    rgStep L dim Nl j a x - rgStep L dim Nl j b x
      = Nl j (couplingOf a) x - Nl j (couplingOf b) x := by
  simp only [rgStep]; abel

end Scaling

/-! ## 2. The drive strength is a marginal weight -/

/-- The sixth power of the coupling is the inverse cube of the shooting
coordinate. -/
theorem couplingOf_cube_mul_cube {w : ℝ} (hw : 0 < w) :
    couplingOf w ^ 3 * couplingOf w ^ 3 = (w ^ 3)⁻¹ := by
  have h2 : couplingOf w ^ 2 = w⁻¹ := couplingOf_sq hw.le
  have : couplingOf w ^ 3 * couplingOf w ^ 3 = (couplingOf w ^ 2) ^ 3 := by ring
  rw [this, h2, inv_pow]

/-- **The coupling drive of the irrelevant sector is a marginal weight.**  A
cubic generation bound in the coupling, composed with the Jacobian of the
shooting coordinate `u = g⁻²`, produces exactly the weight
`(C_gen/2)·g_j⁶ = literalMarginalWeight C_gen u₀ b j`. -/
theorem drive_of_cubic_generation {Cgen u₀ bl : ℝ} {j : ℕ} {a b : ℝ}
    (hCgen : 0 ≤ Cgen) (hu₀ : 0 < u₀) (hbl : 0 < bl)
    (ha : u₀ + bl * j ≤ a) (hb : u₀ + bl * j ≤ b) :
    Cgen * couplingOf (u₀ + bl * j) ^ 3 * |couplingOf a - couplingOf b|
      ≤ literalMarginalWeight Cgen u₀ bl j * |a - b| := by
  have hfl : (0 : ℝ) < u₀ + bl * j := by
    have : (0 : ℝ) ≤ bl * j := by positivity
    linarith
  have hlip := abs_couplingOf_sub_le hfl ha hb
  have hg3 : (0 : ℝ) ≤ couplingOf (u₀ + bl * j) ^ 3 := by
    have := couplingOf_nonneg (u₀ + bl * j); positivity
  have hstep : Cgen * couplingOf (u₀ + bl * j) ^ 3 * |couplingOf a - couplingOf b|
      ≤ Cgen * couplingOf (u₀ + bl * j) ^ 3
          * ((1 / 2) * couplingOf (u₀ + bl * j) ^ 3 * |a - b|) := by
    refine mul_le_mul_of_nonneg_left hlip (by positivity)
  have hcube := couplingOf_cube_mul_cube hfl
  have hval : Cgen * couplingOf (u₀ + bl * j) ^ 3
      * ((1 / 2) * couplingOf (u₀ + bl * j) ^ 3 * |a - b|)
      = literalMarginalWeight Cgen u₀ bl j * |a - b| := by
    rw [literalMarginalWeight]
    calc Cgen * couplingOf (u₀ + bl * j) ^ 3
          * ((1 / 2) * couplingOf (u₀ + bl * j) ^ 3 * |a - b|)
        = (Cgen / 2) * (couplingOf (u₀ + bl * j) ^ 3 * couplingOf (u₀ + bl * j) ^ 3)
            * |a - b| := by ring
      _ = Cgen / 2 * ((u₀ + bl * j) ^ 3)⁻¹ * |a - b| := by rw [hcube]
  linarith [hstep, hval.le, hval.ge]

/-- **The domination hypothesis is scale free.**  Because the drive strength and
the marginal weight are the *same* function of the scale, `L_coef·D_k ≤ C_mem·θ·s_k`
holds at every scale as soon as it holds for the constants. -/
theorem literalMarginalWeight_dominate {Cgen Cdir Lcoef Cmem thmem u₀ bl : ℝ}
    (hu₀ : 0 < u₀) (hbl : 0 < bl) (h : Lcoef * Cgen ≤ Cmem * thmem * Cdir) (k : ℕ) :
    Lcoef * literalMarginalWeight Cgen u₀ bl k
      ≤ Cmem * thmem * literalMarginalWeight Cdir u₀ bl k := by
  have hx : (0 : ℝ) < u₀ + bl * k := by
    have : (0 : ℝ) ≤ bl * k := by positivity
    linarith
  have hinv : (0 : ℝ) ≤ (((u₀ + bl * k) ^ 3)⁻¹) := by positivity
  rw [literalMarginalWeight, literalMarginalWeight]
  nlinarith [h, hinv]

/-! ## 3. The Duhamel bound on the admissible tube -/

variable {E : Type*} [NormedAddCommGroup E]

/-- **The discrete Duhamel bound, with all hypotheses restricted to the
admissible tube.**  This is the version needed once the coupling drive is only
Lipschitz *locally* — as it is when its strength carries the local coupling size
`g_j³`, which is the whole point of the derivation. -/
theorem irrelevant_response_duhamel_tube
    {R : ℕ → ℝ → E → E} {rst : ℕ → ℝ → E} {u : ℕ → ℝ → ℝ} {thmem : ℝ} {D : ℕ → ℝ} {u₀ : ℝ}
    (hr0 : ∀ p q, u₀ ≤ p → u₀ ≤ q → rst 0 p = rst 0 q)
    (hrec : ∀ j p, u₀ ≤ p → rst (j + 1) p = R j (u j p) (rst j p))
    (hcon : ∀ j g x y, ‖R j g x - R j g y‖ ≤ thmem * ‖x - y‖)
    (hdrv : ∀ j p q x, u₀ ≤ p → u₀ ≤ q →
      ‖R j (u j p) x - R j (u j q) x‖ ≤ D j * |u j p - u j q|)
    (hth0 : 0 ≤ thmem) :
    ∀ (j : ℕ) (p q : ℝ), u₀ ≤ p → u₀ ≤ q →
      ‖rst j p - rst j q‖ ≤ ∑ k ∈ range j, thmem ^ (j - 1 - k) * D k * |u k p - u k q| := by
  intro j
  induction j with
  | zero =>
      intro p q hp hq
      rw [hr0 p q hp hq]
      simp
  | succ j ih =>
      intro p q hp hq
      have hsplit : rst (j + 1) p - rst (j + 1) q
          = (R j (u j p) (rst j p) - R j (u j p) (rst j q))
            + (R j (u j p) (rst j q) - R j (u j q) (rst j q)) := by
        rw [hrec j p hp, hrec j q hq]; abel
      have htri : ‖rst (j + 1) p - rst (j + 1) q‖
          ≤ ‖R j (u j p) (rst j p) - R j (u j p) (rst j q)‖
            + ‖R j (u j p) (rst j q) - R j (u j q) (rst j q)‖ := by
        rw [hsplit]; exact norm_add_le _ _
      have h1 : ‖R j (u j p) (rst j p) - R j (u j p) (rst j q)‖ ≤ thmem * ‖rst j p - rst j q‖ :=
        hcon j _ _ _
      have h2 : ‖R j (u j p) (rst j q) - R j (u j q) (rst j q)‖ ≤ D j * |u j p - u j q| :=
        hdrv j p q _ hp hq
      have h3 : thmem * ‖rst j p - rst j q‖
          ≤ thmem * ∑ k ∈ range j, thmem ^ (j - 1 - k) * D k * |u k p - u k q| :=
        mul_le_mul_of_nonneg_left (ih p q hp hq) hth0
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

/-! ## 4. The coefficient response from tube data -/

/-- **The `hmem` convolution bound from tube-restricted one-scale data.**  Same
conclusion as `literal_mem_of_irrelevant_contraction`, but the coupling drive is
only required to be Lipschitz at the pairs of trajectory values that actually
occur — which is what a locally-suppressed generation bound provides. -/
theorem literal_mem_of_tube_contraction
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {betaZ : ℕ → ℝ → ℝ} {lamD : ℕ → ℝ → ι → ℝ} {lamG : ℕ → ℝ → κ → ℝ}
    {aI aC aL : ℕ → ℝ → ℕ → ℝ} {N : ℕ} {bet : ℕ → ℝ → ℝ}
    {R : ℕ → ℝ → E → E} {rst : ℕ → ℝ → E} {D : ℕ → ℝ}
    {Lcoef Cmem thmem Cdir u₀ bl : ℝ}
    (hr0 : ∀ p q, u₀ ≤ p → u₀ ≤ q → rst 0 p = rst 0 q)
    (hrec : ∀ j p, u₀ ≤ p → rst (j + 1) p = R j (shootingTrajectory bet p j) (rst j p))
    (hcon : ∀ j g x y, ‖R j g x - R j g y‖ ≤ thmem * ‖x - y‖)
    (hdrv : ∀ j p q x, u₀ ≤ p → u₀ ≤ q →
      ‖R j (shootingTrajectory bet p j) x - R j (shootingTrajectory bet q j) x‖
        ≤ D j * |shootingTrajectory bet p j - shootingTrajectory bet q j|)
    (hth0 : 0 ≤ thmem)
    (hlip : ∀ j p q g,
      |literalShellAt betaZ lamD lamG aI aC aL N j p g
        - literalShellAt betaZ lamD lamG aI aC aL N j q g| ≤ Lcoef * ‖rst j p - rst j q‖)
    (hLc0 : 0 ≤ Lcoef) (hCmem : 0 ≤ Cmem) (hCdir : 0 ≤ Cdir) (hu₀ : 0 < u₀) (hbl : 0 < bl)
    (hD : ∀ k, Lcoef * D k ≤ Cmem * thmem * literalMarginalWeight Cdir u₀ bl k) :
    ∀ (j : ℕ) (p q g : ℝ), u₀ ≤ p → u₀ ≤ q →
      |literalShellAt betaZ lamD lamG aI aC aL N j p g
          - literalShellAt betaZ lamD lamG aI aC aL N j q g|
        ≤ ∑ k ∈ range (j + 1), Cmem * thmem ^ (j - k)
            * literalMarginalWeight Cdir u₀ bl k
            * |shootingTrajectory bet p k - shootingTrajectory bet q k| := by
  intro j p q g hp hq
  have hduh := irrelevant_response_duhamel_tube (u := fun k v => shootingTrajectory bet v k)
    (u₀ := u₀) hr0 hrec hcon hdrv hth0 j p q hp hq
  set Δ : ℕ → ℝ := fun k =>
    |shootingTrajectory bet p k - shootingTrajectory bet q k| with hΔ
  have hΔ0 : ∀ k, 0 ≤ Δ k := fun k => abs_nonneg _
  have hs0 : ∀ k, 0 ≤ literalMarginalWeight Cdir u₀ bl k := fun k =>
    literalMarginalWeight_nonneg hCdir hu₀ hbl k
  have hstep1 : |literalShellAt betaZ lamD lamG aI aC aL N j p g
      - literalShellAt betaZ lamD lamG aI aC aL N j q g|
      ≤ Lcoef * ∑ k ∈ range j, thmem ^ (j - 1 - k) * D k * Δ k :=
    le_trans (hlip j p q g) (mul_le_mul_of_nonneg_left hduh hLc0)
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

/-! ## 5. The constant chain is consistent -/

/-- **The two constant conditions can always be met simultaneously.**  The
scale-free domination `L_coef·C_gen ≤ C_mem·θ·C_dir` is satisfied by taking
`C_mem = L_coef·C_gen/(θ·C_dir)`, and the smallness criterion
`literalKernelMass < 1/2` is then satisfied by taking the bare inverse coupling
`u₀` large enough — equivalently, the bare coupling small enough.  So the
Row-A constant chain is consistent: no choice of `L_coef`, `C_gen`, `C_dir`, `θ`
and slope can obstruct it. -/
theorem exists_constants_for_contraction {Lcoef Cgen Cdir thmem bl : ℝ}
    (hLc0 : 0 ≤ Lcoef) (hCgen : 0 ≤ Cgen) (hCdir : 0 < Cdir)
    (hth0 : 0 < thmem) (hth1 : thmem < 1) (hbl : 0 < bl) :
    ∃ Cmem u₀ : ℝ, 0 ≤ Cmem ∧ 1 ≤ u₀
      ∧ Lcoef * Cgen ≤ Cmem * thmem * Cdir
      ∧ literalKernelMass Cdir Cmem thmem u₀ bl < 1 / 2 := by
  set Cmem : ℝ := Lcoef * Cgen / (thmem * Cdir) with hCmemdef
  have hCmem0 : 0 ≤ Cmem := by
    rw [hCmemdef]
    positivity
  have hdom : Lcoef * Cgen ≤ Cmem * thmem * Cdir := by
    have : Cmem * thmem * Cdir = Lcoef * Cgen := by
      rw [hCmemdef]
      field_simp
    linarith [this.le, this.ge]
  set M : ℝ := (1 + Cmem / (1 - thmem)) * Cdir * (1 + 1 / (2 * bl)) with hMdef
  refine ⟨Cmem, max 1 (M + 1), hCmem0, le_max_left _ _, hdom, ?_⟩
  have hu₀1 : (1 : ℝ) ≤ max 1 (M + 1) := le_max_left _ _
  have hu₀M : M + 1 ≤ max 1 (M + 1) := le_max_right _ _
  have hbig : M < (max 1 (M + 1)) ^ 2 := by nlinarith
  exact literal_sigma_lt_half hCdir.le hCmem0 hth1 hbl hu₀1 hbig

/-! ## 6. Row A from the block-spin scaling structure -/

/-- **Row A's completion predicate from the scaling structure of the small-field
step.**

Compared with `rowA_completion_of_local_rg_data`, neither the contraction factor
`θ` nor the drive strength `D_j` is assumed.  They are produced by:

* `hLblock`, `hdim` — the irrelevant sector consists of operators of scaling
  dimension at least `4 + δ`, and the block-spin step of block size `L > 1`
  rescales them; this gives the linear contraction factor `L^{−δ}`, which is
  `< 1` exactly when the dimensional gap `δ` is positive (`rpow_neg_lt_one`);
  positivity of `δ` is not assumed separately here because `heta` already
  demands `L^{−δ} < 1`;
* `hNlip`, `heta` — the nonlinear remainder of the step is `η`-Lipschitz in the
  state with `η < 1 − L^{−δ}`, so the full step contracts with
  `θ = L^{−δ} + η < 1`;
* `hgen` — the remainder is generated by the coupling at cubic strength
  `C_gen·g_j³`; composed with the Jacobian of `u = g⁻²`, this makes the drive
  strength exactly the marginal weight `(C_gen/2)g_j⁶`;
* `hdom` — the *scale-free* domination `L_coef·C_gen ≤ C_mem·θ·C_dir`, which the
  previous formulation had to impose at every scale separately.

Everything else is the literal five-channel source data of
`rowA_completion_of_literal_channels`, and every hypothesis is imposed only on
the admissible small-field tube `u ≥ u₀`. -/
theorem rowA_completion_of_scaling_rg_data
    {ι κ : Type*} [Fintype ι] [Fintype κ] {Op : Type*} [Fintype Op]
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
    (hgen : ∀ j g g' x, ‖Nl j g x - Nl j g' x‖
      ≤ Cgen * couplingOf (u₀ + (bZm - eps) * j) ^ 3 * |g - g'|)
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
  -- the shell coefficient is trapped from below on the tube, giving the trajectory floor
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
  -- the derived coupling drive
  have hdrv : ∀ j p q x, u₀ ≤ p → u₀ ≤ q →
      ‖rgStep L dim Nl j (shootingTrajectory bet p j) x
          - rgStep L dim Nl j (shootingTrajectory bet q j) x‖
        ≤ literalMarginalWeight Cgen u₀ bl j
            * |shootingTrajectory bet p j - shootingTrajectory bet q j| := by
    intro j p q x hp hq
    rw [rgStep_drive]
    exact le_trans (hgen j _ _ x)
      (drive_of_cubic_generation hCgen hu₀ hbl (hfloor p hp j) (hfloor q hq j))
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

end YangMills
