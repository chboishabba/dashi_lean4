/-
# Row B — the geometric shell energy from a source-shaped polymer majorant

The Row-B completion contract asks, as its one scalar theorem, for a geometric
shell energy

    E_d ≤ E₀·r^d,     0 ≤ r < 1,

after which the summation, coefficient-cap and weighted-Cauchy machinery is
downstream.  The source-native input it is supposed to come from is the polymer
activity estimate of Bałaban's cluster-expansion paper (CMP 116, *Renormalization
Group Approach to Lattice Gauge Field Theories II. Cluster Expansions*, 116
(1988) 1–22), whose activity bounds have the shape

    |E^{(k)}(X)| ≤ (constant)·exp(−μ·d_k(X)),

an exponential majorant in the polymer size functional `d_k(X)` (not in the
Euclidean diameter).

This file proves the implication that turns that majorant into the geometric
shell energy, with the entropy of the polymer family made explicit:

* `shell_energy_geometric` — if the activities on the shell `{X : d(X) = n}` are
  bounded by `A·e^{−μn}` and the shell contains at most `B·e^{νn}` polymers with
  `0 ≤ ν < μ`, then the shell energy obeys `E_n ≤ (A·B)·r^n` with
  `r = e^{ν−μ} ∈ [0,1)`;
* `shell_energy_ratio_lt_one` — the ratio really is `< 1`, which is the content
  of the entropy-versus-decay competition;
* `shell_energy_summable` and `shell_energy_tsum_le` — the total energy is finite
  with the explicit bound `A·B/(1−r)`.

**Honest status.**  The two hypotheses are the physics: the exponential activity
majorant (Row B4) and the polymer entropy bound.  Neither is proved here, and
neither is transcribed from the source: the source estimates carry unspecified
`O(1)` constants and are stated for the specific polymer families of the cluster
expansion.  What is proved here is that these two inputs — and nothing more —
give the geometric shell energy `E_d ≤ E₀r^d` that the Row-B contract names, with
explicit constants.  Row B is not closed by this file.
-/
import Mathlib

namespace YangMills

open Finset

variable {X : Type*}

/-- The competition ratio of a polymer family: entropy exponent `ν` against decay
exponent `μ`. -/
noncomputable def shellRatio (nu mu : ℝ) : ℝ := Real.exp (nu - mu)

/-- **The ratio is strictly below one exactly when decay beats entropy.** -/
theorem shellRatio_lt_one {nu mu : ℝ} (h : nu < mu) : shellRatio nu mu < 1 := by
  rw [shellRatio]
  exact Real.exp_lt_one_iff.mpr (by linarith)

theorem shellRatio_nonneg (nu mu : ℝ) : 0 ≤ shellRatio nu mu := (Real.exp_pos _).le

/-- **Geometric shell energy from an exponential activity majorant and an
entropy bound.**  `E_n = Σ_{X : d(X)=n} |activity X| ≤ (A·B)·r^n`, `r = e^{ν−μ}`. -/
theorem shell_energy_geometric {shell : ℕ → Finset X} {act : X → ℝ} {A B mu nu : ℝ}
    (hact : ∀ n, ∀ x ∈ shell n, |act x| ≤ A * Real.exp (-(mu * n)))
    (hcard : ∀ n, ((shell n).card : ℝ) ≤ B * Real.exp (nu * n))
    (hA : 0 ≤ A) (n : ℕ) :
    ∑ x ∈ shell n, |act x| ≤ (A * B) * shellRatio nu mu ^ n := by
  have hstep : ∑ x ∈ shell n, |act x| ≤ ((shell n).card : ℝ) * (A * Real.exp (-(mu * n))) := by
    calc ∑ x ∈ shell n, |act x| ≤ ∑ _x ∈ shell n, A * Real.exp (-(mu * n)) :=
          Finset.sum_le_sum (hact n)
      _ = ((shell n).card : ℝ) * (A * Real.exp (-(mu * n))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hpos : 0 ≤ A * Real.exp (-(mu * n)) := by positivity
  have hstep2 : ((shell n).card : ℝ) * (A * Real.exp (-(mu * n)))
      ≤ (B * Real.exp (nu * n)) * (A * Real.exp (-(mu * n))) :=
    mul_le_mul_of_nonneg_right (hcard n) hpos
  have hcalc : (B * Real.exp (nu * n)) * (A * Real.exp (-(mu * n)))
      = (A * B) * shellRatio nu mu ^ n := by
    rw [shellRatio, ← Real.exp_nat_mul]
    rw [show (n : ℝ) * (nu - mu) = nu * n + -(mu * n) by ring, Real.exp_add]
    ring
  linarith [hstep, hstep2, hcalc.le, hcalc.ge]

/-- The total polymer energy is summable. -/
theorem shell_energy_summable {shell : ℕ → Finset X} {act : X → ℝ} {A B mu nu : ℝ}
    (hact : ∀ n, ∀ x ∈ shell n, |act x| ≤ A * Real.exp (-(mu * n)))
    (hcard : ∀ n, ((shell n).card : ℝ) ≤ B * Real.exp (nu * n))
    (hA : 0 ≤ A) (hmn : nu < mu) :
    Summable fun n => ∑ x ∈ shell n, |act x| := by
  have hr0 : 0 ≤ shellRatio nu mu := shellRatio_nonneg nu mu
  have hr1 : shellRatio nu mu < 1 := shellRatio_lt_one hmn
  have hgeo : Summable fun n : ℕ => (A * B) * shellRatio nu mu ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  refine Summable.of_nonneg_of_le (fun n => Finset.sum_nonneg fun x _ => abs_nonneg _)
    (fun n => shell_energy_geometric hact hcard hA n) hgeo

/-- The explicit total-energy bound `A·B/(1−r)`. -/
theorem shell_energy_tsum_le {shell : ℕ → Finset X} {act : X → ℝ} {A B mu nu : ℝ}
    (hact : ∀ n, ∀ x ∈ shell n, |act x| ≤ A * Real.exp (-(mu * n)))
    (hcard : ∀ n, ((shell n).card : ℝ) ≤ B * Real.exp (nu * n))
    (hA : 0 ≤ A) (hmn : nu < mu) :
    ∑' n : ℕ, (∑ x ∈ shell n, |act x|) ≤ (A * B) / (1 - shellRatio nu mu) := by
  have hr0 : 0 ≤ shellRatio nu mu := shellRatio_nonneg nu mu
  have hr1 : shellRatio nu mu < 1 := shellRatio_lt_one hmn
  have hsum := shell_energy_summable hact hcard hA hmn
  have hgeo : Summable fun n : ℕ => (A * B) * shellRatio nu mu ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hle : ∑' n : ℕ, (∑ x ∈ shell n, |act x|)
      ≤ ∑' n : ℕ, (A * B) * shellRatio nu mu ^ n :=
    hsum.tsum_le_tsum (fun n => shell_energy_geometric hact hcard hA n) hgeo
  have hval : ∑' n : ℕ, (A * B) * shellRatio nu mu ^ n
      = (A * B) * (1 - shellRatio nu mu)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  rw [div_eq_mul_inv]
  linarith [hle, hval.le, hval.ge]

end YangMills
