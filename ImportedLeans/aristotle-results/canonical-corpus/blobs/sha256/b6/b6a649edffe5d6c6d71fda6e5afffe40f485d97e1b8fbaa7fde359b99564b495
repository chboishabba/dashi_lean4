/-
# Row A — the sensitivity bootstrap: from per-shell response weights to `q < 1`

`RowAShooting` needs a *cumulative* Lipschitz constant of the beta history in the
bare inverse coupling, `Σ_{j<K}L_j ≤ q < 1`.  What the physics actually produces
is different in two ways:

* the shell coefficient is Lipschitz in the **effective** coupling at its own
  scale (and, through the memory kernel, at earlier scales), not in the bare
  coupling — the bare-coupling constant has to be bootstrapped;
* the estimate holds only on the **admissible tube** `u ≥ u₀`, not globally,
  while the contraction argument lives on all of `ℝ`.

This file supplies both bridges.

## 1. The bootstrap (discrete Duhamel/Grönwall)

If the shell coefficients obey a *response-kernel* estimate

    |β_j(p) − β_j(q)| ≤ Σ_{k≤j} w_{j,k}·|u_k(p) − u_k(q)|,      w ≥ 0,

with total kernel mass `Σ_{j<J}Σ_{k≤j}w_{j,k} ≤ σ < 1` uniformly in `J`, then the
whole trajectory is Lipschitz in the bare coupling with constant `(1−σ)⁻¹`
(`trajectory_diff_le_of_kernel`), hence each shell coefficient is Lipschitz in
the bare coupling with constant `L_j = (Σ_k w_{j,k})/(1−σ)` and

    Σ_{j<K}L_j ≤ σ/(1−σ),

which is `< 1` as soon as `σ < 1/2` (`cumulative_kernel_sensitivity_le`,
`kernel_q_lt_one`).  The marginal coupling is *not* assigned any forgetting law:
it is carried explicitly by the trajectory recursion, and only the memory weights
`w_{j,k}` for `k < j` are asked to decay.

## 2. Marginal + irrelevant decomposition

`splitKernel` is the sum of the diagonal (marginal, direct) weight `s_j` and a
geometrically decaying memory weight `C·θ^{j−k}·s_k`; its total mass is bounded
by `(1 + C/(1−θ))·Σ_k s_k` (`splitKernel_mass_le`).  So an irrelevant sector that
forgets geometrically contributes only a bounded multiple of the *marginal*
sensitivity: memory can add to the marginal sensitivity but cannot replace it.

## 3. The tube

`clampBare` extends a tube-local estimate to the whole line by clamping the bare
coupling at the floor `u₀`; the clamped map is globally Lipschitz with the same
constants, and the tuned bare coupling produced by the contraction lies in the
tube whenever the observation-scale value does
(`rowA_completion_of_tube_sensitivity`), so the completion predicate holds for
the *literal* shell coefficient, with every hypothesis assumed only on the
admissible small-field tube.
-/
import RequestProject.YangMills.RowACompletion

namespace YangMills

open Finset

/-! ## 1. The response bootstrap -/

/-- The total mass of the response kernel at shell `j`: the marginal weight plus
all the memory weights feeding that shell. -/
noncomputable def kernelRow (w : ℕ → ℕ → ℝ) (j : ℕ) : ℝ := ∑ k ∈ range (j + 1), w j k

theorem kernelRow_nonneg {w : ℕ → ℕ → ℝ} (hw : ∀ j k, 0 ≤ w j k) (j : ℕ) :
    0 ≤ kernelRow w j :=
  Finset.sum_nonneg fun k _ => hw j k

/-- **The bootstrap.**  A response-kernel estimate with total mass `σ < 1` makes
the whole generated trajectory Lipschitz in the bare inverse coupling with
constant `(1−σ)⁻¹`, uniformly in the scale.  The proof is a strong induction: the
shell-`j` difference is controlled by the earlier trajectory differences, which
the induction hypothesis has already bounded. -/
theorem trajectory_diff_le_of_kernel {bet : ℕ → ℝ → ℝ} {w : ℕ → ℕ → ℝ}
    {sigma u₀ v x : ℝ} (hw : ∀ j k, 0 ≤ w j k)
    (hker : ∀ j p q, u₀ ≤ p → u₀ ≤ q →
      |bet j p - bet j q| ≤ ∑ k ∈ range (j + 1),
        w j k * |shootingTrajectory bet p k - shootingTrajectory bet q k|)
    (hmass : ∀ J, ∑ j ∈ range J, kernelRow w j ≤ sigma)
    (hsig1 : sigma < 1) (hv : u₀ ≤ v) (hx : u₀ ≤ x) (j : ℕ) :
    |shootingTrajectory bet v j - shootingTrajectory bet x j| ≤ (1 - sigma)⁻¹ * |v - x| := by
  have hden : 0 < 1 - sigma := by linarith
  induction j using Nat.strong_induction_on with
  | _ j ih =>
      -- the trajectory difference is the bare difference plus the accumulated shell differences
      have hdiff : shootingTrajectory bet v j - shootingTrajectory bet x j
          = (v - x) + ∑ i ∈ range j, (bet i v - bet i x) := by
        rw [shootingTrajectory, shootingTrajectory, Finset.sum_sub_distrib]
        ring
      have hshell : ∀ i ∈ range j, |bet i v - bet i x| ≤ kernelRow w i * ((1 - sigma)⁻¹ * |v - x|) := by
        intro i hi
        have hij : i < j := Finset.mem_range.mp hi
        refine le_trans (hker i v x hv hx) ?_
        have hterm : ∀ k ∈ range (i + 1),
            w i k * |shootingTrajectory bet v k - shootingTrajectory bet x k|
              ≤ w i k * ((1 - sigma)⁻¹ * |v - x|) := by
          intro k hk
          have hkj : k < j := lt_of_lt_of_le (Nat.lt_succ_iff.mpr (Nat.lt_succ_iff.mp
            (Finset.mem_range.mp hk))) hij
          exact mul_le_mul_of_nonneg_left (ih k hkj) (hw i k)
        calc ∑ k ∈ range (i + 1), w i k * |shootingTrajectory bet v k - shootingTrajectory bet x k|
            ≤ ∑ k ∈ range (i + 1), w i k * ((1 - sigma)⁻¹ * |v - x|) :=
              Finset.sum_le_sum hterm
          _ = kernelRow w i * ((1 - sigma)⁻¹ * |v - x|) := by
              rw [kernelRow, Finset.sum_mul]
      have hsum : ∑ i ∈ range j, |bet i v - bet i x|
          ≤ (∑ i ∈ range j, kernelRow w i) * ((1 - sigma)⁻¹ * |v - x|) := by
        calc ∑ i ∈ range j, |bet i v - bet i x|
            ≤ ∑ i ∈ range j, kernelRow w i * ((1 - sigma)⁻¹ * |v - x|) :=
              Finset.sum_le_sum hshell
          _ = (∑ i ∈ range j, kernelRow w i) * ((1 - sigma)⁻¹ * |v - x|) := by
              rw [Finset.sum_mul]
      have hmassj := hmass j
      have hpos : 0 ≤ (1 - sigma)⁻¹ * |v - x| := by positivity
      have hsum2 : ∑ i ∈ range j, |bet i v - bet i x| ≤ sigma * ((1 - sigma)⁻¹ * |v - x|) :=
        le_trans hsum (mul_le_mul_of_nonneg_right hmassj hpos)
      have habs : |shootingTrajectory bet v j - shootingTrajectory bet x j|
          ≤ |v - x| + ∑ i ∈ range j, |bet i v - bet i x| := by
        rw [hdiff]
        have h1 := abs_add_le (v - x) (∑ i ∈ range j, (bet i v - bet i x))
        have h2 := Finset.abs_sum_le_sum_abs (fun i => bet i v - bet i x) (range j)
        linarith
      have hcancel : (1 - sigma) * (1 - sigma)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hden)
      have hfin : |v - x| + sigma * ((1 - sigma)⁻¹ * |v - x|) = (1 - sigma)⁻¹ * |v - x| := by
        have hexp : (1 - sigma)⁻¹ * |v - x| - sigma * ((1 - sigma)⁻¹ * |v - x|)
            = ((1 - sigma) * (1 - sigma)⁻¹) * |v - x| := by ring
        rw [hcancel, one_mul] at hexp
        linarith
      linarith [habs, hsum2, hfin.le, hfin.ge]

/-- **Per-shell Lipschitz constant in the bare coupling**, produced by the
bootstrap. -/
theorem shell_lipschitz_of_kernel {bet : ℕ → ℝ → ℝ} {w : ℕ → ℕ → ℝ}
    {sigma u₀ v x : ℝ} (hw : ∀ j k, 0 ≤ w j k)
    (hker : ∀ j p q, u₀ ≤ p → u₀ ≤ q →
      |bet j p - bet j q| ≤ ∑ k ∈ range (j + 1),
        w j k * |shootingTrajectory bet p k - shootingTrajectory bet q k|)
    (hmass : ∀ J, ∑ j ∈ range J, kernelRow w j ≤ sigma)
    (hsig1 : sigma < 1) (hv : u₀ ≤ v) (hx : u₀ ≤ x) (j : ℕ) :
    |bet j v - bet j x| ≤ (kernelRow w j * (1 - sigma)⁻¹) * |v - x| := by
  refine le_trans (hker j v x hv hx) ?_
  have hterm : ∀ k ∈ range (j + 1),
      w j k * |shootingTrajectory bet v k - shootingTrajectory bet x k|
        ≤ w j k * ((1 - sigma)⁻¹ * |v - x|) := by
    intro k _
    exact mul_le_mul_of_nonneg_left
      (trajectory_diff_le_of_kernel hw hker hmass hsig1 hv hx k) (hw j k)
  calc ∑ k ∈ range (j + 1), w j k * |shootingTrajectory bet v k - shootingTrajectory bet x k|
      ≤ ∑ k ∈ range (j + 1), w j k * ((1 - sigma)⁻¹ * |v - x|) := Finset.sum_le_sum hterm
    _ = (kernelRow w j * (1 - sigma)⁻¹) * |v - x| := by
        simp only [kernelRow, Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring

/-- **The cumulative bare-coupling sensitivity.**  `Σ_{j<K}L_j ≤ σ/(1−σ)`,
uniformly in the cutoff. -/
theorem cumulative_kernel_sensitivity_le {w : ℕ → ℕ → ℝ} {sigma : ℝ}
    (hmass : ∀ J, ∑ j ∈ range J, kernelRow w j ≤ sigma)
    (hsig1 : sigma < 1) (K : ℕ) :
    ∑ j ∈ range K, kernelRow w j * (1 - sigma)⁻¹ ≤ sigma / (1 - sigma) := by
  have hden : 0 < 1 - sigma := by linarith
  rw [← Finset.sum_mul, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (hmass K) (by positivity)

/-- **The cumulative beta map is a `q`-contraction on the tube**, `q = σ/(1−σ)`.
This is the literal target inequality `|𝓑_K(p) − 𝓑_K(q)| ≤ q·|p − q|`: the sum is
over the *whole* prefix of shell coefficients, and the constant is uniform in the
cutoff `K`. -/
theorem cumulative_beta_lipschitz_of_kernel {bet : ℕ → ℝ → ℝ} {w : ℕ → ℕ → ℝ}
    {sigma u₀ v x : ℝ} (hw : ∀ j k, 0 ≤ w j k)
    (hker : ∀ j p q, u₀ ≤ p → u₀ ≤ q →
      |bet j p - bet j q| ≤ ∑ k ∈ range (j + 1),
        w j k * |shootingTrajectory bet p k - shootingTrajectory bet q k|)
    (hmass : ∀ J, ∑ j ∈ range J, kernelRow w j ≤ sigma)
    (hsig1 : sigma < 1) (hv : u₀ ≤ v) (hx : u₀ ≤ x) (K : ℕ) :
    |∑ j ∈ range K, bet j v - ∑ j ∈ range K, bet j x|
      ≤ (sigma / (1 - sigma)) * |v - x| := by
  have hden : 0 < 1 - sigma := by linarith
  have hsub : ∑ j ∈ range K, bet j v - ∑ j ∈ range K, bet j x
      = ∑ j ∈ range K, (bet j v - bet j x) := by
    rw [Finset.sum_sub_distrib]
  rw [hsub]
  calc |∑ j ∈ range K, (bet j v - bet j x)|
      ≤ ∑ j ∈ range K, |bet j v - bet j x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range K, (kernelRow w j * (1 - sigma)⁻¹) * |v - x| :=
        Finset.sum_le_sum fun j _ =>
          shell_lipschitz_of_kernel hw hker hmass hsig1 hv hx j
    _ = (∑ j ∈ range K, kernelRow w j * (1 - sigma)⁻¹) * |v - x| := by
        rw [Finset.sum_mul]
    _ ≤ (sigma / (1 - sigma)) * |v - x| :=
        mul_le_mul_of_nonneg_right (cumulative_kernel_sensitivity_le hmass hsig1 K)
          (abs_nonneg _)

/-- **`σ < 1/2` is exactly what makes the shooting map a contraction.** -/
theorem kernel_q_lt_one {sigma : ℝ} (hsig0 : 0 ≤ sigma) (hsig : sigma < 1 / 2) :
    sigma / (1 - sigma) < 1 ∧ 0 ≤ sigma / (1 - sigma) := by
  have hden : 0 < 1 - sigma := by linarith
  refine ⟨?_, by positivity⟩
  rw [div_lt_one hden]
  linarith

/-! ## 2. Marginal plus geometrically forgetting memory -/

/-- The response kernel of a system whose marginal (coupling) direction is
carried explicitly and whose irrelevant directions forget geometrically:
diagonal weight `s_j`, memory weight `C·θ^{j−k}·s_k`. -/
noncomputable def splitKernel (C theta : ℝ) (s : ℕ → ℝ) (j k : ℕ) : ℝ :=
  (if k = j then s j else 0) + C * theta ^ (j - k) * s k

theorem splitKernel_nonneg {C theta : ℝ} {s : ℕ → ℝ} (hC : 0 ≤ C) (hth : 0 ≤ theta)
    (hs : ∀ k, 0 ≤ s k) (j k : ℕ) : 0 ≤ splitKernel C theta s j k := by
  rw [splitKernel]
  have h1 : 0 ≤ (if k = j then s j else 0) := by
    split <;> simp [hs]
  have h2 : 0 ≤ C * theta ^ (j - k) * s k :=
    mul_nonneg (mul_nonneg hC (pow_nonneg hth _)) (hs k)
  linarith

/-- **The mass of the split kernel.**  Exchanging the order of summation resums
the memory geometrically: the total mass is at most `(1 + C/(1−θ))·Σ_k s_k`.  The
marginal part contributes its own sum and nothing more; the memory can only add
a bounded multiple of it. -/
theorem splitKernel_mass_le {C theta Stot : ℝ} {s : ℕ → ℝ}
    (hC : 0 ≤ C) (hth0 : 0 ≤ theta) (hth1 : theta < 1) (hs : ∀ k, 0 ≤ s k)
    (hStot : ∀ J, ∑ k ∈ range J, s k ≤ Stot) (J : ℕ) :
    ∑ j ∈ range J, kernelRow (splitKernel C theta s) j
      ≤ (1 + C / (1 - theta)) * Stot := by
  have hden : 0 < 1 - theta := by linarith
  have hStot0 : 0 ≤ Stot := le_trans (Finset.sum_nonneg fun k _ => hs k) (hStot 0)
  -- split the rows
  have hrow : ∀ j, kernelRow (splitKernel C theta s) j
      = s j + ∑ k ∈ range (j + 1), C * theta ^ (j - k) * s k := by
    intro j
    simp only [kernelRow, splitKernel]
    rw [Finset.sum_add_distrib]
    congr 1
    simp
  have hsplit : ∑ j ∈ range J, kernelRow (splitKernel C theta s) j
      = (∑ j ∈ range J, s j)
        + ∑ j ∈ range J, ∑ k ∈ range (j + 1), C * theta ^ (j - k) * s k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hrow j
  -- exchange the order of summation in the memory part
  have hswap : ∑ j ∈ range J, ∑ k ∈ range (j + 1), C * theta ^ (j - k) * s k
      = ∑ k ∈ range J, ∑ j ∈ Finset.Ico k J, C * theta ^ (j - k) * s k := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    apply Finset.sum_nbij' (fun p => ⟨p.2, p.1⟩) (fun p => ⟨p.2, p.1⟩) <;>
      simp +contextual [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico]
    all_goals omega
  have hinner : ∀ k, ∑ j ∈ Finset.Ico k J, C * theta ^ (j - k) * s k
      ≤ (C / (1 - theta)) * s k := by
    intro k
    have hfac : ∑ j ∈ Finset.Ico k J, C * theta ^ (j - k) * s k
        = (C * s k) * ∑ j ∈ Finset.Ico k J, theta ^ (j - k) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hmap : ∑ j ∈ Finset.Ico k J, theta ^ (j - k) = ∑ i ∈ range (J - k), theta ^ i := by
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      omega
    have hgeo : ∑ i ∈ range (J - k), theta ^ i ≤ (1 - theta)⁻¹ := by
      have hsm : Summable (fun i : ℕ => theta ^ i) := summable_geometric_of_lt_one hth0 hth1
      have h := hsm.sum_le_tsum (range (J - k)) (fun i _ => pow_nonneg hth0 i)
      rwa [tsum_geometric_of_lt_one hth0 hth1] at h
    have hCs : 0 ≤ C * s k := mul_nonneg hC (hs k)
    calc ∑ j ∈ Finset.Ico k J, C * theta ^ (j - k) * s k
        = (C * s k) * ∑ j ∈ Finset.Ico k J, theta ^ (j - k) := hfac
      _ = (C * s k) * ∑ i ∈ range (J - k), theta ^ i := by rw [hmap]
      _ ≤ (C * s k) * (1 - theta)⁻¹ := mul_le_mul_of_nonneg_left hgeo hCs
      _ = (C / (1 - theta)) * s k := by rw [div_eq_mul_inv]; ring
  have hmem : ∑ j ∈ range J, ∑ k ∈ range (j + 1), C * theta ^ (j - k) * s k
      ≤ (C / (1 - theta)) * Stot := by
    rw [hswap]
    calc ∑ k ∈ range J, ∑ j ∈ Finset.Ico k J, C * theta ^ (j - k) * s k
        ≤ ∑ k ∈ range J, (C / (1 - theta)) * s k := Finset.sum_le_sum fun k _ => hinner k
      _ = (C / (1 - theta)) * ∑ k ∈ range J, s k := by rw [Finset.mul_sum]
      _ ≤ (C / (1 - theta)) * Stot :=
          mul_le_mul_of_nonneg_left (hStot J) (by positivity)
  have hmarg : ∑ j ∈ range J, s j ≤ Stot := hStot J
  have hfin : (1 + C / (1 - theta)) * Stot = Stot + (C / (1 - theta)) * Stot := by ring
  linarith [hsplit.le, hsplit.ge, hmem, hmarg, hfin.le, hfin.ge]

/-! ## 3. From the tube to the line: clamping -/

/-- The bare coupling clamped at the tube floor. -/
noncomputable def clampBare (u₀ : ℝ) (bet : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ :=
  fun j v => bet j (max v u₀)

theorem clampBare_of_le {u₀ v : ℝ} (bet : ℕ → ℝ → ℝ) (hv : u₀ ≤ v) (j : ℕ) :
    clampBare u₀ bet j v = bet j v := by
  rw [clampBare, max_eq_left hv]

theorem clampBare_mem_tube {u₀ : ℝ} (v : ℝ) : u₀ ≤ max v u₀ := le_max_right _ _

theorem shootingTrajectory_clampBare {u₀ v : ℝ} (bet : ℕ → ℝ → ℝ) (hv : u₀ ≤ v) (j : ℕ) :
    shootingTrajectory (clampBare u₀ bet) v j = shootingTrajectory bet v j := by
  rw [shootingTrajectory, shootingTrajectory]
  congr 1
  exact Finset.sum_congr rfl fun i _ => clampBare_of_le bet hv i

/-- **A tube-local Lipschitz estimate extends to the line by clamping**, with the
same constants: clamping is `1`-Lipschitz and lands in the tube. -/
theorem clampBare_lipschitz {bet : ℕ → ℝ → ℝ} {L : ℕ → ℝ} {u₀ : ℝ}
    (hL : ∀ j p q, u₀ ≤ p → u₀ ≤ q → |bet j p - bet j q| ≤ L j * |p - q|)
    (hL0 : ∀ j, 0 ≤ L j) (j : ℕ) (v x : ℝ) :
    |clampBare u₀ bet j v - clampBare u₀ bet j x| ≤ L j * |v - x| := by
  have h := hL j (max v u₀) (max x u₀) (clampBare_mem_tube v) (clampBare_mem_tube x)
  have hmax : |max v u₀ - max x u₀| ≤ |v - x| := by
    simpa using abs_sup_sub_sup_le_abs v x u₀
  refine le_trans h ?_
  exact mul_le_mul_of_nonneg_left hmax (hL0 j)

/-- **Row A's completion predicate from tube-local data.**  Every hypothesis is
assumed only on the admissible small-field tube `u ≥ u₀`; the tuned bare coupling
produced by the contraction is shown to lie in that tube, so the conclusion is
about the literal shell coefficient, not about a clamped surrogate.

The extra hypothesis over `rowA_completion_of_uniform_debt` is `htube`: the
prescribed observation-scale value must be large enough — equivalently the
prescribed physical coupling small enough — that the whole tuned trajectory,
bare end included, stays inside the tube. -/
theorem rowA_completion_of_tube_sensitivity
    {bet betaZ betaInt : ℕ → ℝ → ℝ} {L : ℕ → ℝ} {q target bZm bZp eps u₀ : ℝ} {K : ℕ}
    (hdec : ∀ j v, u₀ ≤ v → bet j v = betaZ j v + betaInt j v)
    (hZl : ∀ j v, u₀ ≤ v → bZm ≤ betaZ j v) (hZu : ∀ j v, u₀ ≤ v → betaZ j v ≤ bZp)
    (hIntEps : ∀ j v, u₀ ≤ v → |betaInt j v| ≤ eps)
    (hL : ∀ j p q, u₀ ≤ p → u₀ ≤ q → |bet j p - bet j q| ≤ L j * |p - q|)
    (hL0 : ∀ j, 0 ≤ L j)
    (hq : ∑ j ∈ range K, L j ≤ q) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hwin : 0 < target - (bZp + eps) * K) (hepsm : eps < bZm)
    (htube : u₀ ≤ target - (bZp + eps) * K) :
    RowACompletion bet K target (bZm - eps) (bZp + eps) (target - (bZp + eps) * K)⁻¹ := by
  classical
  set bet' : ℕ → ℝ → ℝ := clampBare u₀ bet with hbet'
  -- the two-sided shell bounds transfer to the clamped map, globally
  have hlow' : ∀ j v, bZm - eps ≤ bet' j v := by
    intro j v
    have hm : u₀ ≤ max v u₀ := clampBare_mem_tube v
    have h := abs_le.mp (hIntEps j (max v u₀) hm)
    have := hZl j (max v u₀) hm
    rw [hbet', clampBare, hdec j (max v u₀) hm]
    linarith [h.1]
  have hup' : ∀ j v, bet' j v ≤ bZp + eps := by
    intro j v
    have hm : u₀ ≤ max v u₀ := clampBare_mem_tube v
    have h := abs_le.mp (hIntEps j (max v u₀) hm)
    have := hZu j (max v u₀) hm
    rw [hbet', clampBare, hdec j (max v u₀) hm]
    linarith [h.2]
  have hlip' : ∀ j v x, |bet' j v - bet' j x| ≤ L j * |v - x| :=
    fun j v x => clampBare_lipschitz hL hL0 j v x
  have hslope : 0 < bZm - eps := by linarith
  obtain ⟨v, hK, hlowtraj, hwindow, hobs⟩ :=
    tuned_bare_coupling_window (bet := bet') (L := L) (q := q) (target := target)
      (bZm := bZm - eps) (bZp := bZp + eps) (K := K) hlip' hq hq0 hq1
      hlow' hup' hslope.le hwin
  -- the tuned bare coupling is in the tube
  have hv0 : u₀ ≤ v := by
    have h := hlowtraj 0 (Nat.zero_le K)
    rw [shootingTrajectory_zero] at h
    linarith
  -- hence the clamped map agrees with the literal one all along the tuned trajectory
  have htraj : ∀ j, shootingTrajectory bet' v j = shootingTrajectory bet v j := fun j =>
    shootingTrajectory_clampBare bet hv0 j
  have hbetv : ∀ j, bet' j v = bet j v := fun j => clampBare_of_le bet hv0 j
  have htargetpos : 0 < target := by
    have h1 : 0 ≤ bZp + eps := by linarith [hlow' 0 0, hup' 0 0]
    have : 0 ≤ (bZp + eps) * K := by positivity
    linarith
  refine ⟨v, ?_, ⟨?_, by positivity⟩, ?_, hslope, fun k m hkm => ?_⟩
  · rw [← htraj K]; exact hK
  · simp only [couplingSq] at hobs ⊢
    rw [← htraj K]
    exact hobs
  · intro j hj
    have h := hwindow j hj
    simp only [couplingSq] at h ⊢
    rw [← htraj j]
    exact h
  · have hcard : (Finset.Ico k m).card = m - k := Nat.card_Ico k m
    constructor
    · calc (bZm - eps) * (m - k : ℕ) = ∑ _j ∈ Finset.Ico k m, (bZm - eps) := by
            rw [Finset.sum_const, hcard, nsmul_eq_mul]; ring
        _ ≤ ∑ j ∈ Finset.Ico k m, bet j v :=
            Finset.sum_le_sum fun j _ => by rw [← hbetv j]; exact hlow' j v
    · calc ∑ j ∈ Finset.Ico k m, bet j v ≤ ∑ _j ∈ Finset.Ico k m, (bZp + eps) :=
            Finset.sum_le_sum fun j _ => by rw [← hbetv j]; exact hup' j v
        _ = (bZp + eps) * (m - k : ℕ) := by
            rw [Finset.sum_const, hcard, nsmul_eq_mul]; ring

end YangMills
