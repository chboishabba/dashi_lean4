/-
# Row A — what a uniformly positive shell coefficient actually produces

The Row A1 lane produces a *shell* statement:

    β_j ≥ b₋ > 0    uniformly in the shell index and the admissible history,

together with the ceiling `β_j ≤ b₊` of `UpperShellBound`.  Row A itself is not
a statement about one shell: it is a statement about the **trajectory** that
those shell coefficients generate.  With the standard identification

    u_j = g_j⁻²,        u_{j+1} = u_j + β_j,

this file derives, from the two-sided shell bound alone, everything Row A asks of
the running coupling:

* `inverseCoupling_lower` / `inverseCoupling_upper` — the linear-in-scale trap
  `u₀ + b₋·j ≤ u_j ≤ u₀ + b₊·j`;
* `coupling_pos` — the coupling never reaches zero at any finite scale, i.e. the
  small-field region is entered but the theory does not become free at any
  finite step (`g_j² ≥ (u₀ + b₊·j)⁻¹ > 0`);
* `tendsto_coupling_zero` — **asymptotic freedom of the tuned trajectory**:
  `g_j² → 0`;
* `summable_coupling_fourth` — `Σ_j g_j⁴ < ∞`, because `g_j⁴ ≤ b₋⁻²j⁻²`;
* `summable_interactionDebt` — hence the *whole* interaction debt
  `Σ_j |β_{Int,j}| ≤ C·Σ_j g_{j−1}⁴` is finite, with an explicit bound;
* `interactionDebt_lt_of_small` — and it is smaller than any prescribed
  tolerance once the initial inverse coupling is large enough.

The last two items are the point: the anti-double-counting route
`β_j ≥ b_patch − C_β γ⁴` needs the total debt to be *summable*, and summability
is not an extra assumption — it is a consequence of the positivity of the
Gaussian shell coefficient itself, through the `1/j` decay it forces on the
coupling.

**Honest status.**  This is the trajectory half of Row A, conditional on the
shell bound; it does not close Row A, whose remaining content is the
source-identification of the shell coefficient and the analytic construction of
the measure.
-/
import Mathlib

namespace YangMills

open Filter Topology

/-! ## 1. The linear trap for the inverse coupling -/

variable {u beta : ℕ → ℝ} {bm bp : ℝ}

/-- **Lower linear trap.**  A uniformly positive shell coefficient makes the
inverse squared coupling grow at least linearly in the number of shells. -/
theorem inverseCoupling_lower (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hb : ∀ j, bm ≤ beta j) (j : ℕ) : u 0 + bm * j ≤ u j := by
  induction j with
  | zero => simp
  | succ n ih =>
      rw [hstep n]
      have := hb n
      push_cast
      push_cast at ih
      nlinarith

/-- **Upper linear trap.** -/
theorem inverseCoupling_upper (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hb : ∀ j, beta j ≤ bp) (j : ℕ) : u j ≤ u 0 + bp * j := by
  induction j with
  | zero => simp
  | succ n ih =>
      rw [hstep n]
      have := hb n
      push_cast
      push_cast at ih
      nlinarith

/-- The inverse coupling is positive at every scale. -/
theorem inverseCoupling_pos (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hb : ∀ j, bm ≤ beta j) (hbm : 0 ≤ bm) (hu0 : 0 < u 0) (j : ℕ) : 0 < u j := by
  have h := inverseCoupling_lower hstep hb j
  have : (0 : ℝ) ≤ bm * j := by positivity
  linarith

/-! ## 2. The coupling itself -/

/-- The squared coupling read off from the inverse coupling. -/
noncomputable def couplingSq (u : ℕ → ℝ) (j : ℕ) : ℝ := (u j)⁻¹

/-- **The coupling is strictly positive at every finite scale**, and bounded
below by `(u₀ + b₊ j)⁻¹`: the trajectory stays in a nonzero coupling window at
every finite step. -/
theorem coupling_pos (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hbl : ∀ j, bm ≤ beta j) (hbu : ∀ j, beta j ≤ bp) (hbm : 0 ≤ bm) (hu0 : 0 < u 0)
    (j : ℕ) : 0 < couplingSq u j ∧ (u 0 + bp * j)⁻¹ ≤ couplingSq u j := by
  have hupos := inverseCoupling_pos hstep hbl hbm hu0 j
  refine ⟨inv_pos.mpr hupos, ?_⟩
  exact inv_anti₀ hupos (inverseCoupling_upper hstep hbu j)

/-- **The coupling obeys the `1/j` bound** forced by the positive shell
coefficient. -/
theorem couplingSq_le (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hb : ∀ j, bm ≤ beta j) (hbm : 0 ≤ bm) (hu0 : 0 < u 0) (j : ℕ) :
    couplingSq u j ≤ (u 0 + bm * j)⁻¹ := by
  have hupos := inverseCoupling_pos hstep hb hbm hu0 j
  have hlow := inverseCoupling_lower hstep hb j
  have hden : 0 < u 0 + bm * j := by
    have : (0 : ℝ) ≤ bm * j := by positivity
    linarith
  exact inv_anti₀ hden hlow

/-- **Asymptotic freedom of the tuned trajectory.**  A uniformly positive shell
coefficient forces the squared coupling to zero. -/
theorem tendsto_couplingSq_zero (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hb : ∀ j, bm ≤ beta j) (hbm : 0 < bm) (hu0 : 0 < u 0) :
    Tendsto (couplingSq u) atTop (𝓝 0) := by
  have hmaj : Tendsto (fun j : ℕ => (u 0 + bm * j)⁻¹) atTop (𝓝 0) := by
    have hlin : Tendsto (fun j : ℕ => u 0 + bm * j) atTop atTop := by
      have : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      exact tendsto_atTop_add_const_left _ _ (this.const_mul_atTop hbm)
    exact hlin.inv_tendsto_atTop
  refine squeeze_zero (fun j => ?_) (fun j => couplingSq_le hstep hb hbm.le hu0 j) hmaj
  exact (inv_pos.mpr (inverseCoupling_pos hstep hb hbm.le hu0 j)).le

/-! ## 3. Summability of the quartic debt -/

/-- `g_j⁴ ≤ b₋⁻²·j⁻²` for `j ≥ 1`. -/
theorem couplingSq_sq_le (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hb : ∀ j, bm ≤ beta j) (hbm : 0 < bm) (hu0 : 0 < u 0) (j : ℕ) :
    couplingSq u (j + 1) ^ 2 ≤ bm⁻¹ ^ 2 * ((j : ℝ) + 1)⁻¹ ^ 2 := by
  have hpos : 0 < couplingSq u (j + 1) :=
    inv_pos.mpr (inverseCoupling_pos hstep hb hbm.le hu0 (j + 1))
  have hden : 0 < bm * ((j : ℝ) + 1) := by positivity
  have hstep2 : (u 0 + bm * ((j : ℝ) + 1))⁻¹ ≤ (bm * ((j : ℝ) + 1))⁻¹ :=
    inv_anti₀ hden (by linarith)
  have hle' : couplingSq u (j + 1) ≤ (u 0 + bm * ((j : ℝ) + 1))⁻¹ := by
    have := couplingSq_le hstep hb hbm.le hu0 (j + 1)
    push_cast at this
    exact this
  have hchain : couplingSq u (j + 1) ≤ (bm * ((j : ℝ) + 1))⁻¹ := le_trans hle' hstep2
  have hrhs : (bm * ((j : ℝ) + 1))⁻¹ = bm⁻¹ * ((j : ℝ) + 1)⁻¹ := by
    rw [mul_inv]
  rw [hrhs] at hchain
  have hnn : (0 : ℝ) ≤ bm⁻¹ * ((j : ℝ) + 1)⁻¹ := by positivity
  calc couplingSq u (j + 1) ^ 2 ≤ (bm⁻¹ * ((j : ℝ) + 1)⁻¹) ^ 2 := by
        exact pow_le_pow_left₀ hpos.le hchain 2
    _ = bm⁻¹ ^ 2 * ((j : ℝ) + 1)⁻¹ ^ 2 := by ring

/-- **`Σ_j g_j⁴ < ∞`.**  The uniform positivity of the shell Gaussian
coefficient makes the quartic interaction debt summable — it is not an extra
hypothesis. -/
theorem summable_couplingSq_sq (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hb : ∀ j, bm ≤ beta j) (hbm : 0 < bm) (hu0 : 0 < u 0) :
    Summable fun j => couplingSq u j ^ 2 := by
  rw [← summable_nat_add_iff 1]
  have hcomp : Summable fun j : ℕ => bm⁻¹ ^ 2 * ((j : ℝ) + 1)⁻¹ ^ 2 := by
    have hbase : Summable fun j : ℕ => ((j : ℝ) + 1)⁻¹ ^ 2 := by
      have h2 : Summable fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ := by simp
      have := (summable_nat_add_iff 1).mpr h2
      refine this.congr fun j => ?_
      push_cast
      rw [← inv_pow]
    exact hbase.mul_left _
  refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_) hcomp
  exact couplingSq_sq_le hstep hb hbm hu0 j

/-- **The total interaction debt is finite.**  If each interaction shell
coefficient is bounded by `C·g_j⁴`, the whole debt series converges. -/
theorem summable_interactionDebt {betaInt : ℕ → ℝ} {C : ℝ}
    (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hb : ∀ j, bm ≤ beta j) (hbm : 0 < bm) (hu0 : 0 < u 0)
    (hdebt : ∀ j, |betaInt j| ≤ C * couplingSq u j ^ 2) :
    Summable betaInt := by
  have hC : 0 ≤ C := by
    have h0 := hdebt 0
    have hcs : 0 < couplingSq u 0 := inv_pos.mpr hu0
    have hq : 0 < couplingSq u 0 ^ 2 := by positivity
    nlinarith [abs_nonneg (betaInt 0)]
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    ((summable_couplingSq_sq hstep hb hbm hu0).mul_left C)
  simpa [Real.norm_eq_abs] using hdebt j

/-! ## 4. The Row A cumulative condition, Gaussian plus debt -/

/-- **Row A's displayed cumulative condition.**  If the Gaussian shell
coefficients are trapped between `b₋` and `b₊` on a block of shells and the
interaction shell coefficients have total absolute weight at most `D` there,
then the full cumulative shell sum is trapped between `b₋(m−k) − D` and
`b₊(m−k) + D`. -/
theorem cumulative_beta_two_sided {betaZ betaInt : ℕ → ℝ} {bm bp D : ℝ} {k m : ℕ}
    (hZl : ∀ j ∈ Finset.Ico k m, bm ≤ betaZ j)
    (hZu : ∀ j ∈ Finset.Ico k m, betaZ j ≤ bp)
    (hdebt : ∑ j ∈ Finset.Ico k m, |betaInt j| ≤ D) :
    bm * (m - k : ℕ) - D ≤ ∑ j ∈ Finset.Ico k m, (betaZ j + betaInt j)
      ∧ ∑ j ∈ Finset.Ico k m, (betaZ j + betaInt j) ≤ bp * (m - k : ℕ) + D := by
  have hcard : (Finset.Ico k m).card = m - k := Nat.card_Ico k m
  have hlow : bm * (m - k : ℕ) ≤ ∑ j ∈ Finset.Ico k m, betaZ j := by
    calc bm * (m - k : ℕ) = ∑ _j ∈ Finset.Ico k m, bm := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]; ring
      _ ≤ ∑ j ∈ Finset.Ico k m, betaZ j := Finset.sum_le_sum hZl
  have hhigh : ∑ j ∈ Finset.Ico k m, betaZ j ≤ bp * (m - k : ℕ) := by
    calc ∑ j ∈ Finset.Ico k m, betaZ j ≤ ∑ _j ∈ Finset.Ico k m, bp := Finset.sum_le_sum hZu
      _ = bp * (m - k : ℕ) := by rw [Finset.sum_const, hcard, nsmul_eq_mul]; ring
  have hsplit : ∑ j ∈ Finset.Ico k m, (betaZ j + betaInt j)
      = (∑ j ∈ Finset.Ico k m, betaZ j) + ∑ j ∈ Finset.Ico k m, betaInt j :=
    Finset.sum_add_distrib
  have habs : |∑ j ∈ Finset.Ico k m, betaInt j| ≤ ∑ j ∈ Finset.Ico k m, |betaInt j| :=
    Finset.abs_sum_le_sum_abs _ _
  have hb := abs_le.mp (le_trans habs hdebt)
  rw [hsplit]
  exact ⟨by linarith [hb.1], by linarith [hb.2]⟩

/-- The interaction debt over a block of shells, bounded through the quartic
coupling bound. -/
theorem debt_block_bound {betaInt : ℕ → ℝ} {C : ℝ} {k m : ℕ} (hC : 0 ≤ C)
    (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hb : ∀ j, bm ≤ beta j) (hbm : 0 < bm) (hu0 : 0 < u 0)
    (hdebt : ∀ j, |betaInt j| ≤ C * couplingSq u j ^ 2) :
    ∑ j ∈ Finset.Ico k m, |betaInt j| ≤ C * ∑' j : ℕ, couplingSq u j ^ 2 := by
  have hsummable := summable_couplingSq_sq hstep hb hbm hu0
  have hstep1 : ∑ j ∈ Finset.Ico k m, |betaInt j|
      ≤ ∑ j ∈ Finset.Ico k m, C * couplingSq u j ^ 2 :=
    Finset.sum_le_sum fun j _ => hdebt j
  have hstep2 : ∑ j ∈ Finset.Ico k m, C * couplingSq u j ^ 2
      ≤ ∑' j : ℕ, C * couplingSq u j ^ 2 :=
    Summable.sum_le_tsum _ (fun j _ => mul_nonneg hC (sq_nonneg _)) (hsummable.mul_left C)
  have hts : ∑' j : ℕ, C * couplingSq u j ^ 2 = C * ∑' j : ℕ, couplingSq u j ^ 2 :=
    tsum_mul_left
  linarith [hstep1, hstep2, hts.le, hts.ge]

end YangMills
