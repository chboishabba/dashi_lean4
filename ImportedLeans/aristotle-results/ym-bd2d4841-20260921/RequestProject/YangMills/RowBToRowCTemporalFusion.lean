/-
# B → C fusion: the marked shell energy pays the temporal curvature debt

Row B produces a *geometric marked shell energy*

    E_n = Σ_{X ∈ shell n} |act X| ≤ (A·B)·rⁿ,      r = e^{ν−μ} < 1

(`RowBShellEnergy.shell_energy_geometric`), and Row C's temporal half needs a
cutoff-uniform bound on the accumulated negative curvature debt `Σ_n η_n`.

This file welds the two, in the only form that survives the log-heat second
variation (`LogHeatSecondVariation.hasDerivAt_tilted_expectation`): the
dynamical debt is dominated by the *static* marked shell **plus** a covariance
response,

    η_n ≤ E_n + Cov_n.

* `geometric_debt_prefix`, `geometric_debt_tsum` — the general geometric shell
  compiler: `η_n ≤ A·rⁿ` gives `Σ_{n<N} η_n ≤ A/(1−r)` for every `N`.
* `curvature_debt_of_marked_shell` — Row B's activity/entropy hypotheses plus a
  geometric covariance shell give the cutoff-uniform accumulated debt
  `(A·B)/(1−r) + A_cov/(1−r_cov)`.  So the *summation* half of Row C's temporal
  obligation is not separate physics: it is Row B's estimate plus the covariance
  response.
* `marked_shell_meets_envelope` — if the Row-B ratio satisfies `r ≤ 17/32`, the
  marked shell fits inside the repository's existing `17/32` curvature envelope.

**Honest status.**  The physical inputs are Row B's activity and entropy
majorants (unproved, and not transcribable from the available source scan), the
same-object domination `η_n ≤ E_n + Cov_n`, and the covariance shell.  Nothing
here closes Row B or Row C, and the frozen research count is unchanged.
-/
import RequestProject.YangMills.RowBShellEnergy
import RequestProject.YangMills.HeatDoobCurvatureDebt
import RequestProject.YangMills.BetaObserver

namespace YangMills

open Finset

/-- **Geometric shell compiler.**  A geometric majorant for a nonnegative shell
family gives a bound on every prefix sum, uniform in the cutoff. -/
theorem geometric_debt_prefix {eta : ℕ → ℝ} {A r : ℝ}
    (hA : 0 ≤ A) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hshell : ∀ n, eta n ≤ A * r ^ n) (N : ℕ) :
    ∑ n ∈ range N, eta n ≤ A / (1 - r) := by
  calc ∑ n ∈ range N, eta n ≤ ∑ n ∈ range N, A * r ^ n :=
        Finset.sum_le_sum fun n _ => hshell n
    _ = A * ∑ n ∈ range N, r ^ n := by rw [Finset.mul_sum]
    _ ≤ A * (1 / (1 - r)) :=
        mul_le_mul_of_nonneg_left (geom_sum_le_inv_one_sub hr0 hr1 N) hA
    _ = A / (1 - r) := by ring

/-- The same bound for the total (infinite) debt of a nonnegative family. -/
theorem geometric_debt_tsum {eta : ℕ → ℝ} {A r : ℝ}
    (hA : 0 ≤ A) (hr0 : 0 ≤ r) (hr1 : r < 1) (heta : ∀ n, 0 ≤ eta n)
    (hshell : ∀ n, eta n ≤ A * r ^ n) :
    ∑' n : ℕ, eta n ≤ A / (1 - r) :=
  Real.tsum_le_of_sum_range_le heta fun N => geometric_debt_prefix hA hr0 hr1 hshell N

section Fusion

variable {X : Type*}

/-- **Row B pays the temporal half of Row C, up to the covariance response.**
With Row B's activity and entropy majorants for the marked shell, a covariance
shell, and the same-object domination `η_n ≤ E_n + Cov_n`, the accumulated
negative curvature debt is bounded uniformly in the cutoff. -/
theorem curvature_debt_of_marked_shell {shell : ℕ → Finset X} {act : X → ℝ}
    {eta Cov : ℕ → ℝ} {A B mu nu Acov rcov : ℝ}
    (hact : ∀ n, ∀ x ∈ shell n, |act x| ≤ A * Real.exp (-(mu * n)))
    (hcard : ∀ n, ((shell n).card : ℝ) ≤ B * Real.exp (nu * n))
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hnu : nu < mu)
    (hdom : ∀ n, eta n ≤ (∑ x ∈ shell n, |act x|) + Cov n)
    (hAcov : 0 ≤ Acov) (hrcov0 : 0 ≤ rcov) (hrcov1 : rcov < 1)
    (hcov : ∀ n, Cov n ≤ Acov * rcov ^ n) (N : ℕ) :
    ∑ n ∈ range N, eta n
      ≤ (A * B) / (1 - shellRatio nu mu) + Acov / (1 - rcov) := by
  have hshellE : ∀ n, ∑ x ∈ shell n, |act x| ≤ (A * B) * shellRatio nu mu ^ n :=
    fun n => shell_energy_geometric hact hcard hA n
  have hsplit : ∑ n ∈ range N, eta n
      ≤ ∑ n ∈ range N, ((∑ x ∈ shell n, |act x|) + Cov n) :=
    Finset.sum_le_sum fun n _ => hdom n
  have hdistrib : ∑ n ∈ range N, ((∑ x ∈ shell n, |act x|) + Cov n)
      = (∑ n ∈ range N, ∑ x ∈ shell n, |act x|) + ∑ n ∈ range N, Cov n :=
    Finset.sum_add_distrib
  have hE : ∑ n ∈ range N, ∑ x ∈ shell n, |act x|
      ≤ (A * B) / (1 - shellRatio nu mu) :=
    geometric_debt_prefix (mul_nonneg hA hB) (shellRatio_nonneg nu mu)
      (shellRatio_lt_one hnu) hshellE N
  have hC : ∑ n ∈ range N, Cov n ≤ Acov / (1 - rcov) :=
    geometric_debt_prefix hAcov hrcov0 hrcov1 hcov N
  linarith [hsplit, hdistrib.le, hdistrib.ge, hE, hC]

/-- **The marked shell fits the existing `17/32` curvature envelope** as soon as
the Row-B ratio does. -/
theorem marked_shell_meets_envelope {shell : ℕ → Finset X} {act : X → ℝ}
    {A B mu nu : ℝ}
    (hact : ∀ n, ∀ x ∈ shell n, |act x| ≤ A * Real.exp (-(mu * n)))
    (hcard : ∀ n, ((shell n).card : ℝ) ≤ B * Real.exp (nu * n))
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hratio : shellRatio nu mu ≤ 17 / 32) (n : ℕ) :
    ∑ x ∈ shell n, |act x| ≤ (A * B) * (17 / 32 : ℝ) ^ n := by
  refine (shell_energy_geometric hact hcard hA n).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hA hB)
  exact pow_le_pow_left₀ (shellRatio_nonneg nu mu) hratio n

end Fusion

end YangMills
