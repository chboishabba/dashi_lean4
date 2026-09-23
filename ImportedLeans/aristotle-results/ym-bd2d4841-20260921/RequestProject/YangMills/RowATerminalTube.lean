/-
# Row A-i — the *defect-free* bilateral terminal-tail beta tube

`RunningCouplingWindow.cumulative_beta_two_sided` produces the cumulative shell
bound with an additive defect,

    b₋·(m−k) − D  ≤  Σ_{j∈[k,m)} β_j  ≤  b₊·(m−k) + D,

where `D` bounds the total interaction (quartic) debt.  The Row-A completion
contract asks for the *defect-free* bilateral tube on terminal tails,

    b̃₋·n  ≤  Σ_{j=k}^{K−1} β_j  ≤  b̃₊·n,     K = k + n,   b̃₋ > 0,

i.e. the debt has to be absorbed into slightly weakened slopes
`b̃∓ = b∓ ∓ ε`.  This file performs that absorption, in the two regimes in which
it is actually true:

* `terminal_tube_of_small_bare_coupling` — absorption *uniform in the block*:
  the per-shell debt is already below `ε` once the bare inverse coupling
  satisfies `C ≤ ε·u₀²`, because `g_j⁴ ≤ u₀⁻²` along the whole trajectory.  This
  is the version the tuned-bare-coupling construction (Row A-ii) supplies, since
  the tuning drives `u₀` up.
* `terminal_tube_of_late_start` — absorption *asymptotically in `k`*: with no
  smallness of `u₀` at all, the total debt of the block `[k, m)` is bounded by
  `C·κ/u_k ≤ C·κ/(u₀ + b₋k)` by the telescoping estimate
  `debt_block_telescope`, which is below `ε` — and a fortiori below `ε·n` for
  every block length `n ≥ 1` — as soon as the block starts late enough.

The second item is the precise sense in which this is an asymptotic-tail
statement rather than a new RG theorem: the trajectory bound already forces
`Σ_j g_j⁴ < ∞`, hence vanishing block debts.

**Honest status.**  This closes the *analytic* half of the Row A-i contract: the
tube is defect-free, bilateral, with `b̃₋ > 0`, on terminal tails.  Its inputs
are the per-shell two-sided Gaussian bound `b₋ ≤ β_{Z,j} ≤ b₊` and the quartic
remainder bound `|β_{Int,j}| ≤ C·g_j⁴`, both hypotheses carried from the earlier
Row-A files, not results of this one.
-/
import RequestProject.YangMills.RunningCouplingWindow

namespace YangMills

variable {u beta : ℕ → ℝ} {bm bp : ℝ}

/-! ## 0. Two elementary facts about the trajectory -/

/-- The inverse coupling never decreases below its bare value. -/
theorem inverseCoupling_ge_initial (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hb : ∀ j, bm ≤ beta j) (hbm : 0 < bm) (j : ℕ) : u 0 ≤ u j := by
  have h := inverseCoupling_lower hstep hb j
  have hnn : (0:ℝ) ≤ bm * j := mul_nonneg hbm.le (Nat.cast_nonneg j)
  linarith

/-- Telescoping over a half-open block of indices. -/
theorem sum_Ico_telescope (f : ℕ → ℝ) {k m : ℕ} (h : k ≤ m) :
    ∑ j ∈ Finset.Ico k m, (f j - f (j + 1)) = f k - f m := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      rw [Finset.sum_Ico_succ_top hn, ih]
      ring

/-! ## 1. Pointwise smallness of the quartic debt -/

/-- Along a trajectory with positive shell coefficients the squared coupling
never exceeds its bare value. -/
theorem couplingSq_le_initial (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hb : ∀ j, bm ≤ beta j) (hbm : 0 < bm) (hu0 : 0 < u 0) (j : ℕ) :
    couplingSq u j ≤ couplingSq u 0 := by
  have hle : u 0 ≤ u j := inverseCoupling_ge_initial hstep hb hbm j
  simpa [couplingSq] using inv_anti₀ hu0 hle

/-- **Per-shell quartic debt below a prescribed tolerance.**  If the bare
inverse coupling is large enough that `C ≤ ε·u₀²`, then every interaction shell
coefficient obeying the quartic bound is below `ε` in absolute value. -/
theorem debt_pointwise_le {betaInt : ℕ → ℝ} {C eps : ℝ}
    (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hb : ∀ j, bm ≤ beta j) (hbm : 0 < bm) (hu0 : 0 < u 0) (hC : 0 ≤ C)
    (hbig : C ≤ eps * u 0 ^ 2)
    (hdebt : ∀ j, |betaInt j| ≤ C * couplingSq u j ^ 2) (j : ℕ) :
    |betaInt j| ≤ eps := by
  have h1 : couplingSq u j ≤ couplingSq u 0 := couplingSq_le_initial hstep hb hbm hu0 j
  have h0 : 0 ≤ couplingSq u j := by
    have hpos : 0 < u j := inverseCoupling_pos hstep hb hbm.le hu0 j
    simpa [couplingSq] using hpos.le
  have hsq : couplingSq u j ^ 2 ≤ couplingSq u 0 ^ 2 := by
    have := mul_le_mul h1 h1 h0 (le_trans h0 h1)
    simpa [pow_two] using this
  have hinv : couplingSq u 0 ^ 2 = (u 0 ^ 2)⁻¹ := by
    simp [couplingSq, inv_pow]
  have hmul : C * couplingSq u j ^ 2 ≤ C * (u 0 ^ 2)⁻¹ := by
    rw [← hinv]; exact mul_le_mul_of_nonneg_left hsq hC
  have hu2 : 0 < u 0 ^ 2 := by positivity
  have hfin : C * (u 0 ^ 2)⁻¹ ≤ eps := by
    rw [mul_inv_le_iff₀ hu2]
    linarith [hbig]
  exact le_trans (hdebt j) (le_trans hmul hfin)

/-! ## 2. The tube, uniform in the block, for a small bare coupling -/

/-- **Defect-free bilateral tube, uniform in the starting scale.**  With the
Gaussian shell coefficients trapped in `[b₋, b₊]` and a bare inverse coupling
large enough to make the per-shell quartic debt smaller than `ε`, the cumulative
shell sum over *every* block `[k, K)` lies in the tube with slopes `b₋ − ε` and
`b₊ + ε`; the lower slope is strictly positive as soon as `ε < b₋`. -/
theorem terminal_tube_of_small_bare_coupling {betaZ betaInt : ℕ → ℝ}
    {bZm bZp C eps : ℝ} (k K : ℕ)
    (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hb : ∀ j, bm ≤ beta j) (hbm : 0 < bm) (hu0 : 0 < u 0) (hC : 0 ≤ C)
    (hbig : C ≤ eps * u 0 ^ 2)
    (hdebt : ∀ j, |betaInt j| ≤ C * couplingSq u j ^ 2)
    (hZl : ∀ j, bZm ≤ betaZ j) (hZu : ∀ j, betaZ j ≤ bZp) :
    (bZm - eps) * (K - k : ℕ) ≤ ∑ j ∈ Finset.Ico k K, (betaZ j + betaInt j)
      ∧ ∑ j ∈ Finset.Ico k K, (betaZ j + betaInt j) ≤ (bZp + eps) * (K - k : ℕ) := by
  have hcard : (Finset.Ico k K).card = K - k := Nat.card_Ico k K
  have hpt : ∀ j, |betaInt j| ≤ eps := fun j =>
    debt_pointwise_le hstep hb hbm hu0 hC hbig hdebt j
  constructor
  · calc (bZm - eps) * (K - k : ℕ)
        = ∑ _j ∈ Finset.Ico k K, (bZm - eps) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]; ring
      _ ≤ ∑ j ∈ Finset.Ico k K, (betaZ j + betaInt j) :=
          Finset.sum_le_sum fun j _ => by
            have h := abs_le.mp (hpt j)
            linarith [hZl j, h.1]
  · calc ∑ j ∈ Finset.Ico k K, (betaZ j + betaInt j)
        ≤ ∑ _j ∈ Finset.Ico k K, (bZp + eps) :=
          Finset.sum_le_sum fun j _ => by
            have h := abs_le.mp (hpt j)
            linarith [hZu j, h.2]
      _ = (bZp + eps) * (K - k : ℕ) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]; ring

/-! ## 3. The telescoping block-debt estimate -/

/-- **Telescoping block debt.**  `Σ_{j∈[k,m)} g_j⁴ ≤ κ·b₋⁻¹·g_k²` with
`κ = (u₀ + b₊)/u₀`.  The two shell bounds are used in opposite directions:
`β_j ≥ b₋` makes the telescoped increments large, `β_j ≤ b₊` keeps `u_{j+1}`
comparable with `u_j`. -/
theorem debt_block_telescope (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hb : ∀ j, bm ≤ beta j) (hbu : ∀ j, beta j ≤ bp) (hbm : 0 < bm) (hu0 : 0 < u 0)
    (k m : ℕ) :
    ∑ j ∈ Finset.Ico k m, couplingSq u j ^ 2
      ≤ ((u 0 + bp) / u 0) * bm⁻¹ * couplingSq u k := by
  have hupos : ∀ j, 0 < u j := inverseCoupling_pos hstep hb hbm.le hu0
  have hmono : ∀ j, u 0 ≤ u j := inverseCoupling_ge_initial hstep hb hbm
  have hbp0 : 0 ≤ bp := hbm.le.trans ((hb 0).trans (hbu 0))
  set kappa : ℝ := (u 0 + bp) / u 0 with hkappa
  have hkpos : 0 < kappa := by rw [hkappa]; positivity
  have hstepineq : ∀ j, couplingSq u j ^ 2
      ≤ kappa * bm⁻¹ * (couplingSq u j - couplingSq u (j + 1)) := by
    intro j
    have hj : 0 < u j := hupos j
    have hj1 : 0 < u (j + 1) := hupos (j + 1)
    have hdiff : couplingSq u j - couplingSq u (j + 1) = beta j / (u j * u (j + 1)) := by
      have hs : u (j + 1) = u j + beta j := hstep j
      have h1 : u j ≠ 0 := ne_of_gt hj
      have h2 : u (j + 1) ≠ 0 := ne_of_gt hj1
      show (u j)⁻¹ - (u (j + 1))⁻¹ = beta j / (u j * u (j + 1))
      field_simp
      rw [hs]; ring
    have hle1 : bm / (u j * u (j + 1)) ≤ couplingSq u j - couplingSq u (j + 1) := by
      rw [hdiff]
      exact (div_le_div_iff_of_pos_right (by positivity)).mpr (hb j)
    have hu1le : u (j + 1) ≤ kappa * u j := by
      have h1 : u (j + 1) = u j + beta j := hstep j
      have h2 : beta j ≤ bp := hbu j
      have h3 : u 0 ≤ u j := hmono j
      have hk : kappa * u j = u j + (bp / u 0) * u j := by
        rw [hkappa]; field_simp
      have hbpx : bp ≤ (bp / u 0) * u j := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hu0]
        nlinarith
      rw [hk, h1]; linarith
    have hkey : couplingSq u j ^ 2 ≤ kappa * bm⁻¹ * (bm / (u j * u (j + 1))) := by
      have hcalc : kappa * bm⁻¹ * (bm / (u j * u (j + 1))) = kappa / (u j * u (j + 1)) := by
        field_simp
      rw [hcalc]
      have h2 : couplingSq u j ^ 2 = (u j * u j)⁻¹ := by
        simp [couplingSq, pow_two]
      rw [h2, le_div_iff₀ (by positivity)]
      have h3 : (u j * u j)⁻¹ * (u j * u (j + 1)) = u (j + 1) / u j := by
        field_simp
      rw [h3, div_le_iff₀ hj]
      linarith [hu1le]
    refine le_trans hkey ?_
    have hnn : 0 ≤ kappa * bm⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_left hle1 hnn
  by_cases hkm : k ≤ m
  · have hsum : ∑ j ∈ Finset.Ico k m, couplingSq u j ^ 2
        ≤ ∑ j ∈ Finset.Ico k m, kappa * bm⁻¹ * (couplingSq u j - couplingSq u (j + 1)) :=
      Finset.sum_le_sum fun j _ => hstepineq j
    have hfac : ∑ j ∈ Finset.Ico k m, kappa * bm⁻¹ * (couplingSq u j - couplingSq u (j + 1))
        = kappa * bm⁻¹ * (couplingSq u k - couplingSq u m) := by
      rw [← Finset.mul_sum, sum_Ico_telescope (couplingSq u) hkm]
    have hmnn : 0 ≤ couplingSq u m := by
      have := hupos m; simp [couplingSq]; positivity
    have hnn : 0 ≤ kappa * bm⁻¹ := by positivity
    have : kappa * bm⁻¹ * (couplingSq u k - couplingSq u m) ≤ kappa * bm⁻¹ * couplingSq u k := by
      apply mul_le_mul_of_nonneg_left _ hnn
      linarith
    linarith [hsum, hfac.le, hfac.ge]
  · rw [Finset.Ico_eq_empty (by omega)]
    have hknn : 0 ≤ couplingSq u k := by
      have := hupos k; simp [couplingSq]; positivity
    have : 0 ≤ kappa * bm⁻¹ := by positivity
    simpa using mul_nonneg this hknn

/-! ## 4. The tube on late blocks, with no smallness of the bare coupling -/

/-- **Defect-free bilateral tube on terminal tails.**  Without any smallness
assumption on the bare coupling: for every tolerance `ε > 0` there is a starting
scale `k₀` beyond which every block `[k, K)` with `k ≥ k₀` and `K > k` obeys the
defect-free tube with slopes `b_Z∓ ∓ ε`.  The starting scale is explicit, coming
from the telescoping debt estimate together with `u_k ≥ u₀ + b₋k`. -/
theorem terminal_tube_of_late_start {betaZ betaInt : ℕ → ℝ} {bZm bZp C eps : ℝ}
    (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hb : ∀ j, bm ≤ beta j) (hbu : ∀ j, beta j ≤ bp) (hbm : 0 < bm) (hu0 : 0 < u 0)
    (hC : 0 ≤ C) (heps : 0 < eps)
    (hdebt : ∀ j, |betaInt j| ≤ C * couplingSq u j ^ 2)
    (hZl : ∀ j, bZm ≤ betaZ j) (hZu : ∀ j, betaZ j ≤ bZp) :
    ∃ k₀ : ℕ, ∀ k K : ℕ, k₀ ≤ k → k < K →
      (bZm - eps) * (K - k : ℕ) ≤ ∑ j ∈ Finset.Ico k K, (betaZ j + betaInt j)
        ∧ ∑ j ∈ Finset.Ico k K, (betaZ j + betaInt j) ≤ (bZp + eps) * (K - k : ℕ) := by
  have hupos : ∀ j, 0 < u j := inverseCoupling_pos hstep hb hbm.le hu0
  set kappa : ℝ := (u 0 + bp) / u 0 with hkappa
  have hbp0 : 0 ≤ bp := hbm.le.trans ((hb 0).trans (hbu 0))
  have hkpos : 0 < kappa := by rw [hkappa]; positivity
  -- pick `k₀` so large that `C·κ·b₋⁻¹/u_{k₀} < ε`
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, C * kappa * bm⁻¹ / (u 0 + bm * k₀) ≤ eps := by
    obtain ⟨n, hn⟩ := exists_nat_gt ((C * kappa * bm⁻¹ / eps) / bm)
    refine ⟨n, ?_⟩
    have hden : 0 < u 0 + bm * n := by positivity
    rw [div_le_iff₀ hden]
    have h1 : (C * kappa * bm⁻¹ / eps) < bm * n := by
      rw [div_lt_iff₀ hbm] at hn; linarith [hn]
    have h2 : C * kappa * bm⁻¹ < eps * (bm * n) := by
      rw [div_lt_iff₀ heps] at h1; linarith [h1]
    nlinarith [heps.le, hu0.le]
  refine ⟨k₀, fun k K hk hkK => ?_⟩
  have hcard : (Finset.Ico k K).card = K - k := Nat.card_Ico k K
  -- total block debt is at most `ε`
  have hblock : ∑ j ∈ Finset.Ico k K, |betaInt j| ≤ eps := by
    have h1 : ∑ j ∈ Finset.Ico k K, |betaInt j|
        ≤ ∑ j ∈ Finset.Ico k K, C * couplingSq u j ^ 2 :=
      Finset.sum_le_sum fun j _ => hdebt j
    have h2 : ∑ j ∈ Finset.Ico k K, C * couplingSq u j ^ 2
        = C * ∑ j ∈ Finset.Ico k K, couplingSq u j ^ 2 := by
      rw [Finset.mul_sum]
    have h3 : ∑ j ∈ Finset.Ico k K, couplingSq u j ^ 2 ≤ kappa * bm⁻¹ * couplingSq u k :=
      debt_block_telescope hstep hb hbu hbm hu0 k K
    have h4 : couplingSq u k ≤ (u 0 + bm * k)⁻¹ := by
      have hlow := inverseCoupling_lower hstep hb k
      have hden : 0 < u 0 + bm * k := by positivity
      simpa [couplingSq] using inv_anti₀ hden hlow
    have h5 : C * ∑ j ∈ Finset.Ico k K, couplingSq u j ^ 2
        ≤ C * (kappa * bm⁻¹ * (u 0 + bm * k)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ hC
      refine le_trans h3 ?_
      have : 0 ≤ kappa * bm⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_left h4 this
    have h6 : C * (kappa * bm⁻¹ * (u 0 + bm * k)⁻¹) ≤ eps := by
      have hmono : (u 0 + bm * (k₀:ℕ)) ≤ u 0 + bm * k := by
        have : ((k₀:ℕ):ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
        nlinarith [hbm.le]
      have hden0 : 0 < u 0 + bm * (k₀:ℕ) := by positivity
      have hden : 0 < u 0 + bm * k := by positivity
      have hinv : (u 0 + bm * k)⁻¹ ≤ (u 0 + bm * (k₀:ℕ))⁻¹ := inv_anti₀ hden0 hmono
      have hCnn : 0 ≤ C * (kappa * bm⁻¹) := by positivity
      calc C * (kappa * bm⁻¹ * (u 0 + bm * k)⁻¹)
          = C * (kappa * bm⁻¹) * (u 0 + bm * k)⁻¹ := by ring
        _ ≤ C * (kappa * bm⁻¹) * (u 0 + bm * (k₀:ℕ))⁻¹ :=
            mul_le_mul_of_nonneg_left hinv hCnn
        _ = C * kappa * bm⁻¹ / (u 0 + bm * (k₀:ℕ)) := by
            field_simp
        _ ≤ eps := hk₀
    linarith [h1, h2.le, h2.ge, h5, h6]
  -- and `ε ≤ ε·n` for `n ≥ 1`
  have hn1 : (1:ℝ) ≤ (K - k : ℕ) := by
    have : 1 ≤ K - k := by omega
    exact_mod_cast this
  have hepsn : eps ≤ eps * (K - k : ℕ) := by nlinarith [heps.le]
  have hgauss := cumulative_beta_two_sided (betaZ := betaZ) (betaInt := betaInt)
    (bm := bZm) (bp := bZp) (D := eps) (k := k) (m := K)
    (fun j _ => hZl j) (fun j _ => hZu j) hblock
  refine ⟨?_, ?_⟩
  · have := hgauss.1
    nlinarith [this, hepsn]
  · have := hgauss.2
    nlinarith [this, hepsn]

end YangMills
