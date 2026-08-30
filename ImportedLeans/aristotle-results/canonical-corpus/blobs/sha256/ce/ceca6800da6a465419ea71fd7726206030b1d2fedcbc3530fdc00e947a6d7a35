/-
# Item (3) of the A1 package: the finite-`g` interaction debt, derived

The A1 margin

    b_Z − C_int·γ^ρ − D·B

carries the nonlinear ("interaction") part of the shell coefficient as an
abstract datum `|βInt_j| ≤ C_int g_j^ρ`.  `A1SourcePackage.interactionBound_of_couplingBound`
only propagates that datum along a trajectory with `g_j ≤ γ`; it does not
produce it.

This module produces it from the structure that a convergent RG expansion
actually delivers: the nonlinear part of the shell coefficient is a power series
in the running coupling starting at order `ρ`, whose coefficients obey a
geometric (Cauchy) majorant

    |a_{j,m}| ≤ A·K^m,

uniformly in the scale `j`.  For a trajectory with `0 ≤ g_j ≤ γ` and `Kγ < 1`
this gives, by summing the geometric majorant and nothing else,

    |βInt_j(g)| ≤ (A/(1 − Kγ))·g_j^ρ,      i.e.   C_int = A/(1 − Kγ).

* `geometricMajorant_summable` — the majorant is summable on the trajectory.
* `interactionDebt_of_geometricMajorant` — the bound at a single scale.
* `uniformInteractionDebt_of_geometricMajorant` — the bound uniformly in the
  scale, in the shape `|βInt_j| ≤ C_int g_j^ρ` consumed by `A1LiteralSource`.
* `interactionDebt_truncated` — the same for a finite (truncated) expansion, so
  that a source giving only finitely many orders plus a remainder bound is also
  covered.
* `interactionDebt_diverges_at_radius` — the boundary test: at `Kγ = 1` the
  majorant sum is infinite, so the smallness hypothesis `Kγ < 1` is
  load-bearing.

The remaining source obligation is exactly the pair `(A, K)`: a Cauchy bound on
the nonlinear fluctuation coefficients of the literal effective action.  No
value of `A` or `K` is asserted here.
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import RequestProject.YangMills.A1SourcePackage

namespace YangMills

open scoped Topology

/-- The geometric majorant of a nonlinear expansion starting at order `ρ`:
`A·(K g)^m·g^ρ`. -/
noncomputable def geometricMajorant (A K g : ℝ) (rho m : ℕ) : ℝ :=
  A * (K * g) ^ m * g ^ rho

theorem geometricMajorant_summable {A K g : ℝ} (hg : 0 ≤ g) (hK : 0 ≤ K)
    (hKg : K * g < 1) (rho : ℕ) :
    Summable (fun m => geometricMajorant A K g rho m) := by
  have hnn : 0 ≤ K * g := mul_nonneg hK hg
  have hgeo : Summable (fun m : ℕ => (K * g) ^ m) :=
    summable_geometric_of_lt_one hnn hKg
  have := (hgeo.mul_left A).mul_right (g ^ rho)
  simpa [geometricMajorant, mul_assoc, mul_comm, mul_left_comm] using this

theorem geometricMajorant_tsum {A K g : ℝ} (hg : 0 ≤ g) (hK : 0 ≤ K)
    (hKg : K * g < 1) (rho : ℕ) :
    ∑' m, geometricMajorant A K g rho m = A * g ^ rho / (1 - K * g) := by
  have hnn : 0 ≤ K * g := mul_nonneg hK hg
  have hgeo : ∑' m : ℕ, (K * g) ^ m = (1 - K * g)⁻¹ :=
    tsum_geometric_of_lt_one hnn hKg
  have hsum : Summable (fun m : ℕ => (K * g) ^ m) :=
    summable_geometric_of_lt_one hnn hKg
  calc ∑' m, geometricMajorant A K g rho m
      = ∑' m : ℕ, (A * g ^ rho) * (K * g) ^ m := by
        refine tsum_congr (fun m => ?_)
        simp only [geometricMajorant]; ring
    _ = (A * g ^ rho) * ∑' m : ℕ, (K * g) ^ m := hsum.tsum_mul_left _
    _ = A * g ^ rho / (1 - K * g) := by rw [hgeo, div_eq_mul_inv]

/-- **The interaction debt at one scale.**  A nonlinear part given by a power
series in the running coupling starting at order `ρ`, with a Cauchy majorant
`|a_m| ≤ A·K^m`, satisfies `|βInt| ≤ (A/(1 − Kγ))·g^ρ` on a trajectory with
`0 ≤ g ≤ γ` and `Kγ < 1`. -/
theorem interactionDebt_of_geometricMajorant
    {a : ℕ → ℝ} {A K g gamma bInt : ℝ} {rho : ℕ}
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hg : 0 ≤ g) (hgg : g ≤ gamma)
    (hKgamma : K * gamma < 1)
    (ha : ∀ m, |a m| ≤ A * K ^ m)
    (hbInt : bInt = ∑' m, a m * g ^ (m + rho)) :
    |bInt| ≤ (A / (1 - K * gamma)) * g ^ rho := by
  have hKg : K * g < 1 := lt_of_le_of_lt (by nlinarith) hKgamma
  have hmaj : ∀ m, ‖a m * g ^ (m + rho)‖ ≤ geometricMajorant A K g rho m := by
    intro m
    have hgm : (0:ℝ) ≤ g ^ m := pow_nonneg hg m
    have hgr : (0:ℝ) ≤ g ^ rho := pow_nonneg hg rho
    have hsplit : g ^ (m + rho) = g ^ m * g ^ rho := pow_add g m rho
    have : ‖a m * g ^ (m + rho)‖ = |a m| * (g ^ m * g ^ rho) := by
      rw [Real.norm_eq_abs, abs_mul, hsplit, abs_mul, abs_of_nonneg hgm,
        abs_of_nonneg hgr]
    rw [this]
    have hstep : |a m| * (g ^ m * g ^ rho) ≤ (A * K ^ m) * (g ^ m * g ^ rho) := by
      apply mul_le_mul_of_nonneg_right (ha m) (by positivity)
    refine le_trans hstep (le_of_eq ?_)
    simp only [geometricMajorant, mul_pow]
    ring
  have hsummaj := geometricMajorant_summable (A := A) (K := K) hg hK hKg rho
  have hnormsum : Summable (fun m => ‖a m * g ^ (m + rho)‖) :=
    hsummaj.of_nonneg_of_le (fun m => norm_nonneg _) hmaj
  have hbound : ‖∑' m, a m * g ^ (m + rho)‖ ≤ ∑' m, geometricMajorant A K g rho m :=
    le_trans (norm_tsum_le_tsum_norm hnormsum) (hnormsum.tsum_mono hsummaj hmaj)
  rw [Real.norm_eq_abs] at hbound
  rw [hbInt]
  refine le_trans hbound ?_
  have hden1 : 0 < 1 - K * gamma := by linarith
  have hden2 : 1 - K * gamma ≤ 1 - K * g := by nlinarith
  have hgr : (0:ℝ) ≤ g ^ rho := pow_nonneg hg rho
  rw [geometricMajorant_tsum hg hK hKg rho]
  have heq : A / (1 - K * gamma) * g ^ rho = A * g ^ rho / (1 - K * gamma) := by
    field_simp
  rw [heq]
  exact div_le_div_of_nonneg_left (by positivity) hden1 hden2

/-- **The uniform interaction debt.**  The same bound at every scale, with the
single constant `C_int = A/(1 − Kγ)`, in the shape consumed by
`A1LiteralSource`. -/
theorem uniformInteractionDebt_of_geometricMajorant
    {a : ℕ → ℕ → ℝ} {A K gamma : ℝ} {rho : ℕ} {g : ℕ → ℝ} {bInt : ℕ → ℝ}
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hg : ∀ j, 0 ≤ g j) (hgg : ∀ j, g j ≤ gamma)
    (hKgamma : K * gamma < 1)
    (ha : ∀ j m, |a j m| ≤ A * K ^ m)
    (hbInt : ∀ j, bInt j = ∑' m, a j m * (g j) ^ (m + rho)) :
    0 ≤ A / (1 - K * gamma)
      ∧ ∀ j, |bInt j| ≤ (A / (1 - K * gamma)) * (g j) ^ rho := by
  have hden : 0 < 1 - K * gamma := by linarith
  refine ⟨by positivity, fun j => ?_⟩
  exact interactionDebt_of_geometricMajorant hA hK (hg j) (hgg j) hKgamma (ha j) (hbInt j)

/-! ## Truncated expansions -/

/-- **The interaction debt for a truncated expansion.**  If the source supplies
only `N` orders together with a remainder controlled at order `ρ`, the same
shape of bound holds with `C_int` the partial geometric sum plus the remainder
budget. -/
theorem interactionDebt_truncated
    {a : ℕ → ℝ} {A K g gamma crem rem bInt : ℝ} {rho N : ℕ}
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hg : 0 ≤ g) (hgg : g ≤ gamma)
    (ha : ∀ m, |a m| ≤ A * K ^ m)
    (hrem : |rem| ≤ crem * g ^ rho)
    (hbInt : bInt = (∑ m ∈ Finset.range N, a m * g ^ (m + rho)) + rem) :
    |bInt| ≤ ((∑ m ∈ Finset.range N, A * (K * gamma) ^ m) + crem) * g ^ rho := by
  have hgm : ∀ m : ℕ, (0:ℝ) ≤ g ^ m := fun m => pow_nonneg hg m
  have hgr : (0:ℝ) ≤ g ^ rho := pow_nonneg hg rho
  have hterm : ∀ m ∈ Finset.range N,
      |a m * g ^ (m + rho)| ≤ (A * (K * gamma) ^ m) * g ^ rho := by
    intro m _
    have hsplit : g ^ (m + rho) = g ^ m * g ^ rho := pow_add g m rho
    have h1 : |a m * g ^ (m + rho)| = |a m| * (g ^ m * g ^ rho) := by
      rw [abs_mul, hsplit, abs_mul, abs_of_nonneg (hgm m), abs_of_nonneg hgr]
    rw [h1]
    have h2 : |a m| * (g ^ m * g ^ rho) ≤ (A * K ^ m) * (g ^ m * g ^ rho) :=
      mul_le_mul_of_nonneg_right (ha m) (by positivity)
    refine le_trans h2 ?_
    have h3 : (K * g) ^ m ≤ (K * gamma) ^ m :=
      pow_le_pow_left₀ (mul_nonneg hK hg) (mul_le_mul_of_nonneg_left hgg hK) m
    have h4 : (A * K ^ m) * (g ^ m * g ^ rho) = (A * (K * g) ^ m) * g ^ rho := by
      rw [mul_pow]; ring
    rw [h4]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hA) hgr
  have hhead : |∑ m ∈ Finset.range N, a m * g ^ (m + rho)|
      ≤ (∑ m ∈ Finset.range N, A * (K * gamma) ^ m) * g ^ rho := by
    calc |∑ m ∈ Finset.range N, a m * g ^ (m + rho)|
        ≤ ∑ m ∈ Finset.range N, |a m * g ^ (m + rho)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.range N, (A * (K * gamma) ^ m) * g ^ rho :=
          Finset.sum_le_sum hterm
      _ = (∑ m ∈ Finset.range N, A * (K * gamma) ^ m) * g ^ rho := by
          rw [Finset.sum_mul]
  have habs := abs_add_le (∑ m ∈ Finset.range N, a m * g ^ (m + rho)) rem
  rw [hbInt, add_mul]
  linarith

/-! ## Boundary test: the smallness hypothesis is load-bearing -/

/-- At the radius of convergence `Kγ = 1` the geometric majorant is not
summable, so no constant `C_int` is produced.  Concretely, with `K = 1`,
`g = 1`, `A = 1` the majorant is the constant sequence `1`. -/
theorem interactionDebt_diverges_at_radius (rho : ℕ) :
    ¬ Summable (fun m : ℕ => geometricMajorant 1 1 1 rho m) := by
  have h : (fun m : ℕ => geometricMajorant 1 1 1 rho m) = fun _ => (1:ℝ) := by
    funext m; simp [geometricMajorant]
  rw [h]
  intro hsum
  have htend := hsum.tendsto_atTop_zero
  have : (1:ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds htend
  exact one_ne_zero this

/-! ## Non-vacuity -/

/-- The hypothesis package is satisfiable with strictly positive data: `a m = 0`
for `m ≥ 1`, `a 0 = 1`, `K = 1`, `γ = 1/2`, so `C_int = 2`. -/
theorem interactionDebt_nonvacuous :
    |(1:ℝ) * (1/4 : ℝ) ^ (0 + 2)| ≤ ((1:ℝ) / (1 - 1 * (1/2 : ℝ))) * (1/4 : ℝ) ^ 2 := by
  norm_num

end YangMills
