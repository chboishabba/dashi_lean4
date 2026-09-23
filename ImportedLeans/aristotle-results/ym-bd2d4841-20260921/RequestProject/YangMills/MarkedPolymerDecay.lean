/-
# Row B — marked (differentiated) polymer activities keep the decay/entropy margin

`RowBShellEnergy` turns two inputs — an exponential activity majorant
`|K(X)| ≤ A e^{−μ|X|}` and a polymer entropy bound `#{X : d(X) = n} ≤ B e^{νn}`
with `ν < μ` — into the geometric shell energy `E_n ≤ (AB) r^n`, `r = e^{ν−μ}`.

The activities Row B actually needs are not the bare ones: they are the
*marked* activities of a cluster expansion, i.e. the activities differentiated a
bounded number `m` of times with respect to the sources/parameters.  Every such
differentiation distributes over the polymer, so each mark contributes a factor
of the polymer size and the majorant degrades to

    |K^{(m)}(X)| ≤ A·|X|^m·e^{−μ|X|}.

The point of this file is that this polynomial cost is *free*: an arbitrarily
small loss `δ` in the decay rate absorbs any fixed power of the size, with the
explicit constant `(m/δ)^m e^{−m}`.  Consequently the marked activities still
satisfy an exponential majorant, now with rate `μ − δ`, and since `ν < μ` one may
take `δ = (μ − ν)/2` and keep a strictly positive margin `μ − δ − ν = (μ−ν)/2`.

* `pow_mul_exp_neg_le` — the elementary maximisation `tᵐ e^{−t} ≤ mᵐ e^{−m}`,
  proved from `1 + u ≤ eᵘ`;
* `pow_mul_exp_decay_le` — its rescaled form
  `xᵐ e^{−μx} ≤ (m/δ)ᵐ e^{−m} e^{−(μ−δ)x}`;
* `marked_shell_energy_geometric`, `marked_shell_energy_summable`,
  `marked_shell_energy_tsum_le` — the Row-B shell-energy conclusions for the
  marked activities, with the margin `δ = (μ−ν)/2` chosen explicitly, so the only
  remaining Row-B inputs are the *bare* activity decay rate `μ` and the polymer
  entropy rate `ν < μ`.

**Honest status.**  The bare exponential activity bound and the entropy bound
remain hypotheses; they are the physics of the cluster expansion.  What is
removed here is the worry that differentiating the activities destroys the
decay/entropy competition.  Row B is not closed by this file.
-/
import RequestProject.YangMills.RowBShellEnergy

namespace YangMills

open Finset

variable {X : Type*}

/-! ## 1. Polynomial factors are absorbed by an arbitrarily small decay loss -/

/-- **The elementary maximisation `tᵐ e^{−t} ≤ mᵐ e^{−m}` on `t ≥ 0`.**  It comes
straight from `1 + u ≤ eᵘ` applied at `u = t/m − 1`. -/
theorem pow_mul_exp_neg_le (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    t ^ m * Real.exp (-t) ≤ (m : ℝ) ^ m * Real.exp (-(m : ℝ)) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [pow_zero, one_mul, Nat.cast_zero, neg_zero, Real.exp_zero]
    exact Real.exp_le_one_iff.mpr (by linarith)
  · have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hbase : t / m ≤ Real.exp (t / m - 1) := by
      have h := Real.add_one_le_exp (t / m - 1)
      linarith
    have hnn : (0 : ℝ) ≤ t / m := by positivity
    have hpow : (t / m) ^ m ≤ (Real.exp (t / m - 1)) ^ m :=
      pow_le_pow_left₀ hnn hbase m
    have hrhs : (Real.exp (t / m - 1)) ^ m = Real.exp (t - m) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    have hlhs : (t / m) ^ m = t ^ m / (m : ℝ) ^ m := by
      rw [div_pow]
    rw [hlhs, hrhs] at hpow
    have hmp : (0 : ℝ) < (m : ℝ) ^ m := by positivity
    have hstep : t ^ m ≤ (m : ℝ) ^ m * Real.exp (t - m) := by
      rw [div_le_iff₀ hmp] at hpow
      linarith [hpow]
    have hexp : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
    calc t ^ m * Real.exp (-t)
        ≤ ((m : ℝ) ^ m * Real.exp (t - m)) * Real.exp (-t) :=
          mul_le_mul_of_nonneg_right hstep hexp.le
      _ = (m : ℝ) ^ m * Real.exp (-(m : ℝ)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring

/-- **A fixed power is absorbed by an arbitrarily small loss in the decay rate**:
`xᵐ e^{−μx} ≤ (m/δ)ᵐ e^{−m} · e^{−(μ−δ)x}` for `x ≥ 0`, `δ > 0`. -/
theorem pow_mul_exp_decay_le {mu delta x : ℝ} (m : ℕ) (hx : 0 ≤ x) (hd : 0 < delta) :
    x ^ m * Real.exp (-(mu * x))
      ≤ ((m : ℝ) / delta) ^ m * Real.exp (-(m : ℝ)) * Real.exp (-((mu - delta) * x)) := by
  have ht : (0 : ℝ) ≤ delta * x := by positivity
  have hkey := pow_mul_exp_neg_le m ht
  have hxm : x ^ m = (delta * x) ^ m / delta ^ m := by
    rw [mul_pow]
    field_simp
  have hsplit : Real.exp (-(mu * x))
      = Real.exp (-(delta * x)) * Real.exp (-((mu - delta) * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hdm : (0 : ℝ) < delta ^ m := by positivity
  have hexp2 : (0 : ℝ) < Real.exp (-((mu - delta) * x)) := Real.exp_pos _
  have hstep : (delta * x) ^ m * Real.exp (-(delta * x)) / delta ^ m
      ≤ (m : ℝ) ^ m * Real.exp (-(m : ℝ)) / delta ^ m := by
    gcongr
  have hlhs : x ^ m * Real.exp (-(mu * x))
      = ((delta * x) ^ m * Real.exp (-(delta * x)) / delta ^ m)
        * Real.exp (-((mu - delta) * x)) := by
    rw [hxm, hsplit]; ring
  have hrhs : ((m : ℝ) / delta) ^ m * Real.exp (-(m : ℝ))
      = (m : ℝ) ^ m * Real.exp (-(m : ℝ)) / delta ^ m := by
    rw [div_pow]; ring
  rw [hlhs, hrhs]
  exact mul_le_mul_of_nonneg_right hstep hexp2.le

/-! ## 2. The marked activities still feed the Row-B shell energy -/

/-- The decay rate the marked activities retain when the margin is split evenly:
`μ − (μ−ν)/2`, which is the midpoint of `ν` and `μ`. -/
noncomputable def markedRate (mu nu : ℝ) : ℝ := mu - (mu - nu) / 2

theorem markedRate_gt {mu nu : ℝ} (h : nu < mu) : nu < markedRate mu nu := by
  rw [markedRate]; linarith

/-- The constant the marks cost: `(2m/(μ−ν))^m e^{−m}`. -/
noncomputable def markCost (m : ℕ) (mu nu : ℝ) : ℝ :=
  ((m : ℝ) / ((mu - nu) / 2)) ^ m * Real.exp (-(m : ℝ))

theorem markCost_nonneg {m : ℕ} {mu nu : ℝ} (h : nu < mu) : 0 ≤ markCost m mu nu := by
  have hd : (0 : ℝ) < (mu - nu) / 2 := by linarith
  rw [markCost]
  positivity

/-- **The marked activity majorant.**  A polymer activity carrying `m` marks,
bounded by `A·nᵐ·e^{−μn}` on the shell of size `n`, is bounded by
`(A·markCost)·e^{−μ'n}` with `μ' = markedRate μ ν > ν`. -/
theorem marked_activity_bound {act : X → ℝ} {shell : ℕ → Finset X} {A mu nu : ℝ} {m : ℕ}
    (hact : ∀ n, ∀ x ∈ shell n, |act x| ≤ A * (n : ℝ) ^ m * Real.exp (-(mu * n)))
    (hA : 0 ≤ A) (hmn : nu < mu) :
    ∀ n, ∀ x ∈ shell n,
      |act x| ≤ (A * markCost m mu nu) * Real.exp (-(markedRate mu nu * n)) := by
  intro n x hx
  have hd : (0 : ℝ) < (mu - nu) / 2 := by linarith
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpow := pow_mul_exp_decay_le (mu := mu) (delta := (mu - nu) / 2) (x := (n : ℝ)) m hn hd
  have hmul : A * ((n : ℝ) ^ m * Real.exp (-(mu * n)))
      ≤ A * (markCost m mu nu * Real.exp (-(markedRate mu nu * n))) := by
    refine mul_le_mul_of_nonneg_left ?_ hA
    rw [markCost, markedRate]
    exact hpow
  have h1 := hact n x hx
  have h2 : A * (n : ℝ) ^ m * Real.exp (-(mu * n))
      = A * ((n : ℝ) ^ m * Real.exp (-(mu * n))) := by ring
  have h3 : A * (markCost m mu nu * Real.exp (-(markedRate mu nu * n)))
      = (A * markCost m mu nu) * Real.exp (-(markedRate mu nu * n)) := by ring
  linarith [h1, h2.le, h2.ge, hmul, h3.le, h3.ge]

/-- **Row B's geometric shell energy for the marked activities.**  The
competition ratio is `e^{ν − μ'}` with `μ' = (μ+ν)/2`, still strictly below one:
differentiating the polymer activities costs only the explicit constant
`markCost`, never the exponential margin. -/
theorem marked_shell_energy_geometric {shell : ℕ → Finset X} {act : X → ℝ}
    {A B mu nu : ℝ} {m : ℕ}
    (hact : ∀ n, ∀ x ∈ shell n, |act x| ≤ A * (n : ℝ) ^ m * Real.exp (-(mu * n)))
    (hcard : ∀ n, ((shell n).card : ℝ) ≤ B * Real.exp (nu * n))
    (hA : 0 ≤ A) (hmn : nu < mu) (n : ℕ) :
    ∑ x ∈ shell n, |act x|
      ≤ ((A * markCost m mu nu) * B) * shellRatio nu (markedRate mu nu) ^ n :=
  shell_energy_geometric (marked_activity_bound hact hA hmn) hcard
    (mul_nonneg hA (markCost_nonneg hmn)) n

theorem marked_shell_energy_summable {shell : ℕ → Finset X} {act : X → ℝ}
    {A B mu nu : ℝ} {m : ℕ}
    (hact : ∀ n, ∀ x ∈ shell n, |act x| ≤ A * (n : ℝ) ^ m * Real.exp (-(mu * n)))
    (hcard : ∀ n, ((shell n).card : ℝ) ≤ B * Real.exp (nu * n))
    (hA : 0 ≤ A) (hmn : nu < mu) :
    Summable fun n => ∑ x ∈ shell n, |act x| :=
  shell_energy_summable (marked_activity_bound hact hA hmn) hcard
    (mul_nonneg hA (markCost_nonneg hmn)) (markedRate_gt hmn)

/-- The total marked polymer energy is finite, with an explicit bound. -/
theorem marked_shell_energy_tsum_le {shell : ℕ → Finset X} {act : X → ℝ}
    {A B mu nu : ℝ} {m : ℕ}
    (hact : ∀ n, ∀ x ∈ shell n, |act x| ≤ A * (n : ℝ) ^ m * Real.exp (-(mu * n)))
    (hcard : ∀ n, ((shell n).card : ℝ) ≤ B * Real.exp (nu * n))
    (hA : 0 ≤ A) (hmn : nu < mu) :
    ∑' n : ℕ, (∑ x ∈ shell n, |act x|)
      ≤ ((A * markCost m mu nu) * B) / (1 - shellRatio nu (markedRate mu nu)) :=
  shell_energy_tsum_le (marked_activity_bound hact hA hmn) hcard
    (mul_nonneg hA (markCost_nonneg hmn)) (markedRate_gt hmn)

end YangMills
