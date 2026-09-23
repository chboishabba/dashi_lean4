/-
# Row B — the CMP 116 polymer activity rate, expressed in block units

`RowBLatticePolymerEnergy` reduced Row B to a single scalar: an exponential
activity majorant

    |K(Y)| ≤ A·|Y|^m·e^{−μ|Y|},   μ > ν = 1 + 2 log 8,

for the cluster-expansion polymer activities, the entropy rate `ν` having been
discharged unconditionally by `LatticeAnimalEntropy` and the *marks* (i.e. the
differentiated activities Row B actually needs) having been shown by
`MarkedPolymerDecay` to cost only an explicit constant.
`PolymerActivityDecay` then showed that a rate is manufactured by the Mayer
product structure as soon as the per-constituent interaction is small.

This file addresses the remaining bookkeeping question, which is a genuine
source-reading issue rather than a soft one: **the rate in the source is not
stated per polymer, it is stated per unit-lattice volume or per tree length**,
and the polymers of the `k`-th cluster expansion are unions of blocks of `M⁴`
unit sites.  Comparing the source rate with the entropy rate `ν` — which counts
*blocks*, because the polymers are connected in the block lattice — therefore
requires a conversion, and the conversion is where the block size `M` enters.

The two shapes the source's small-field activity estimates take are

    |K(Y)| ≤ A·e^{−¼(κ₁−1)M⁻⁴|Y|}      (volume form, `|Y|` in unit sites)
    |K(Y)| ≤ A·e^{−(1−4δ)κ·d(Y)}       (tree form, `d(Y)` a tree length)

and this file converts each of them into the block-unit form Row B consumes.

* `cmp116BlockRate κ₁ = (κ₁−1)/4`.  The volume form has an `M⁻⁴` in the
  exponent and the volume of an `n`-block polymer is `M⁴n`, so **`M` cancels
  exactly**: the block-unit rate is `(κ₁−1)/4`, independent of the block size.
  This is `cmp116_block_activity_bound`.
* `cmp116BlockRate_exceeds_entropy` — hence the Row-B competition `μ > ν` is
  the completely explicit numerical condition

        κ₁ > 5 + 8 log 8   (≈ 21.64)

  on the source's own large-field/regularity parameter.  Nothing about `M`, and
  no `O(1)` constant, is involved.
* `cmp116TreeRate δ κ = (1−4δ)κ`, `cmp116_tree_activity_bound` — the tree form
  converts as well: a connected polymer of `n` blocks has tree length at least
  `n−1` in block units, so the tree estimate gives the block-unit rate
  `(1−4δ)κ` at the cost of a single prefactor `e^{(1−4δ)κ}`.  The competition is
  then `(1−4δ)κ > 1 + 2 log 8`.
* `cmp116_block_marked_shell_energy_geometric`,
  `cmp116_block_marked_shell_energy_tsum_le`,
  `cmp116_tree_marked_shell_energy_geometric` — Row B's geometric shell energy
  and finite total energy, for activities presented in the source's own two
  shapes.

**Honest status.**  Row B is *not* closed and nothing is promoted.  What is
proved here is the conversion: once the literal differentiated CMP 116
activities are known to satisfy a majorant of either source shape, the Row-B
margin `μ > ν` is an explicit inequality on a single source parameter, and the
block size `M` — which was the reason the comparison looked scale-dependent —
provably drops out.  What is *not* proved here is that the literal activities
satisfy such a majorant; that identification is the outstanding Row-B
obligation, and the hypotheses `hact` below are exactly where it is still
assumed.
-/
import RequestProject.YangMills.PolymerActivityDecay

namespace YangMills

open Finset

/-! ## 1. The volume form: the block size cancels -/

/-- The block-unit decay rate carried by the CMP 116 small-field polymer
majorant `e^{−¼(κ₁−1)M⁻⁴|Y|}`, once the unit-lattice volume `|Y|` of a polymer
built from `M⁴`-site blocks is expressed in block units.  The block size `M`
does not appear: it cancels between the `M⁻⁴` of the source exponent and the
`M⁴` sites of a block. -/
noncomputable def cmp116BlockRate (kappa1 : ℝ) : ℝ := (kappa1 - 1) / 4

/-- **The Row-B margin in the volume form is one explicit inequality on the
source's own parameter.**  `(κ₁−1)/4 > 1 + 2 log 8` is `κ₁ > 5 + 8 log 8`. -/
theorem cmp116BlockRate_exceeds_entropy {kappa1 : ℝ} (h : 5 + 8 * Real.log 8 < kappa1) :
    lattice4EntropyRate < cmp116BlockRate kappa1 := by
  rw [lattice4EntropyRate, cmp116BlockRate]
  linarith

/-- The threshold is a genuine number: `5 + 8 log 8 < 22`. -/
theorem cmp116_threshold_lt_22 : 5 + 8 * Real.log 8 < 22 := by
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    have : (8 : ℝ) = 2 ^ (3 : ℕ) := by norm_num
    rw [this, Real.log_pow]
    push_cast
    ring
  rw [h8]
  nlinarith [Real.log_two_lt_d9]

/-- **The volume-form conversion.**  If the activity of a polymer obeys the
source majorant `A·n^m·e^{−(rate/M⁴)·vol}` and the polymer of shell `n` has
unit-lattice volume `M⁴n`, then it obeys the block-unit majorant
`A·n^m·e^{−rate·n}`. -/
theorem cmp116_block_activity_bound
    {shell : ℕ → Finset (Finset (Fin 4 → ℤ))} {act vol : Finset (Fin 4 → ℤ) → ℝ}
    {A kappa1 : ℝ} {M m : ℕ} (hM : 0 < M)
    (hvol : ∀ n, ∀ S ∈ shell n, vol S = (M : ℝ) ^ 4 * n)
    (hact : ∀ n, ∀ S ∈ shell n,
      |act S| ≤ A * (n : ℝ) ^ m
        * Real.exp (-(cmp116BlockRate kappa1 / (M : ℝ) ^ 4 * vol S)))
    (n : ℕ) : ∀ S ∈ shell n,
      |act S| ≤ A * (n : ℝ) ^ m * Real.exp (-(cmp116BlockRate kappa1 * n)) := by
  intro S hS
  have hMne : ((M : ℝ)) ^ 4 ≠ 0 := by
    have : (0 : ℝ) < M := by exact_mod_cast hM
    positivity
  have h := hact n S hS
  rw [hvol n S hS] at h
  have hcancel : cmp116BlockRate kappa1 / (M : ℝ) ^ 4 * ((M : ℝ) ^ 4 * n)
      = cmp116BlockRate kappa1 * n := by
    field_simp
  rwa [hcancel] at h

/-- **Row B's geometric shell energy for CMP 116 volume-form activities.**  The
only inputs are the source majorant and the explicit threshold on `κ₁`; the
entropy is the proved lattice-animal bound and the block size cancels. -/
theorem cmp116_block_marked_shell_energy_geometric
    {shell : ℕ → Finset (Finset (Fin 4 → ℤ))} {act vol : Finset (Fin 4 → ℤ) → ℝ}
    {A kappa1 : ℝ} {M m : ℕ} {v : Fin 4 → ℤ} (hM : 0 < M)
    (hshell : ∀ n, ∀ S ∈ shell n, IsAnimal (nbFromE latticeStep) v S ∧ S.card = n)
    (hvol : ∀ n, ∀ S ∈ shell n, vol S = (M : ℝ) ^ 4 * n)
    (hact : ∀ n, ∀ S ∈ shell n,
      |act S| ≤ A * (n : ℝ) ^ m
        * Real.exp (-(cmp116BlockRate kappa1 / (M : ℝ) ^ 4 * vol S)))
    (hA : 0 ≤ A) (hkappa : 5 + 8 * Real.log 8 < kappa1) (n : ℕ) :
    ∑ S ∈ shell n, |act S|
      ≤ ((A * markCost m (cmp116BlockRate kappa1) lattice4EntropyRate) * 2)
          * shellRatio lattice4EntropyRate
              (markedRate (cmp116BlockRate kappa1) lattice4EntropyRate) ^ n :=
  lattice4_marked_shell_energy_geometric (v := v) hshell
    (cmp116_block_activity_bound hM hvol hact) hA
    (cmp116BlockRate_exceeds_entropy hkappa) n

/-- The total marked polymer energy of the CMP 116 volume-form activities is
finite, with an explicit bound. -/
theorem cmp116_block_marked_shell_energy_tsum_le
    {shell : ℕ → Finset (Finset (Fin 4 → ℤ))} {act vol : Finset (Fin 4 → ℤ) → ℝ}
    {A kappa1 : ℝ} {M m : ℕ} {v : Fin 4 → ℤ} (hM : 0 < M)
    (hshell : ∀ n, ∀ S ∈ shell n, IsAnimal (nbFromE latticeStep) v S ∧ S.card = n)
    (hvol : ∀ n, ∀ S ∈ shell n, vol S = (M : ℝ) ^ 4 * n)
    (hact : ∀ n, ∀ S ∈ shell n,
      |act S| ≤ A * (n : ℝ) ^ m
        * Real.exp (-(cmp116BlockRate kappa1 / (M : ℝ) ^ 4 * vol S)))
    (hA : 0 ≤ A) (hkappa : 5 + 8 * Real.log 8 < kappa1) :
    ∑' n : ℕ, (∑ S ∈ shell n, |act S|)
      ≤ ((A * markCost m (cmp116BlockRate kappa1) lattice4EntropyRate) * 2)
          / (1 - shellRatio lattice4EntropyRate
              (markedRate (cmp116BlockRate kappa1) lattice4EntropyRate)) :=
  lattice4_marked_shell_energy_tsum_le (v := v) hshell
    (cmp116_block_activity_bound hM hvol hact) hA
    (cmp116BlockRate_exceeds_entropy hkappa)

/-! ## 2. The tree form -/

/-- The block-unit decay rate carried by the CMP 116 tree-length majorant
`e^{−(1−4δ)κ·d(Y)}`. -/
noncomputable def cmp116TreeRate (delta kappa : ℝ) : ℝ := (1 - 4 * delta) * kappa

/-- **The tree-form conversion.**  A connected polymer of `n` blocks has tree
length at least `n − 1` in block units, so a tree-form majorant is a block-unit
majorant with the same rate, at the cost of one prefactor `e^{rate}`. -/
theorem cmp116_tree_activity_bound
    {shell : ℕ → Finset (Finset (Fin 4 → ℤ))} {act d : Finset (Fin 4 → ℤ) → ℝ}
    {A delta kappa : ℝ} {m : ℕ} (hA : 0 ≤ A)
    (hrate : 0 ≤ cmp116TreeRate delta kappa)
    (hd : ∀ n, ∀ S ∈ shell n, (n : ℝ) - 1 ≤ d S)
    (hact : ∀ n, ∀ S ∈ shell n,
      |act S| ≤ A * (n : ℝ) ^ m * Real.exp (-(cmp116TreeRate delta kappa * d S)))
    (n : ℕ) : ∀ S ∈ shell n,
      |act S| ≤ (A * Real.exp (cmp116TreeRate delta kappa)) * (n : ℝ) ^ m
        * Real.exp (-(cmp116TreeRate delta kappa * n)) := by
  intro S hS
  set r := cmp116TreeRate delta kappa with hr
  have h := hact n S hS
  have hmono : Real.exp (-(r * d S)) ≤ Real.exp (-(r * ((n : ℝ) - 1))) := by
    apply Real.exp_le_exp.mpr
    have := hd n S hS
    nlinarith
  have hsplit : Real.exp (-(r * ((n : ℝ) - 1))) = Real.exp r * Real.exp (-(r * n)) := by
    rw [← Real.exp_add]
    ring_nf
  have hpre : (0 : ℝ) ≤ A * (n : ℝ) ^ m := by positivity
  calc |act S| ≤ A * (n : ℝ) ^ m * Real.exp (-(r * d S)) := h
    _ ≤ A * (n : ℝ) ^ m * (Real.exp r * Real.exp (-(r * n))) := by
        rw [← hsplit]; exact mul_le_mul_of_nonneg_left hmono hpre
    _ = (A * Real.exp r) * (n : ℝ) ^ m * Real.exp (-(r * n)) := by ring

/-- **Row B's geometric shell energy for CMP 116 tree-form activities.**  The
margin is the explicit inequality `(1−4δ)κ > 1 + 2 log 8`. -/
theorem cmp116_tree_marked_shell_energy_geometric
    {shell : ℕ → Finset (Finset (Fin 4 → ℤ))} {act d : Finset (Fin 4 → ℤ) → ℝ}
    {A delta kappa : ℝ} {m : ℕ} {v : Fin 4 → ℤ} (hA : 0 ≤ A)
    (hshell : ∀ n, ∀ S ∈ shell n, IsAnimal (nbFromE latticeStep) v S ∧ S.card = n)
    (hd : ∀ n, ∀ S ∈ shell n, (n : ℝ) - 1 ≤ d S)
    (hact : ∀ n, ∀ S ∈ shell n,
      |act S| ≤ A * (n : ℝ) ^ m * Real.exp (-(cmp116TreeRate delta kappa * d S)))
    (hmu : lattice4EntropyRate < cmp116TreeRate delta kappa) (n : ℕ) :
    ∑ S ∈ shell n, |act S|
      ≤ (((A * Real.exp (cmp116TreeRate delta kappa))
            * markCost m (cmp116TreeRate delta kappa) lattice4EntropyRate) * 2)
          * shellRatio lattice4EntropyRate
              (markedRate (cmp116TreeRate delta kappa) lattice4EntropyRate) ^ n := by
  have hrate : 0 ≤ cmp116TreeRate delta kappa := by
    have hnu : (0 : ℝ) < lattice4EntropyRate := by
      have : (0 : ℝ) < Real.log 8 := Real.log_pos (by norm_num)
      rw [lattice4EntropyRate]; linarith
    linarith
  exact lattice4_marked_shell_energy_geometric (v := v) hshell
    (cmp116_tree_activity_bound hA hrate hd hact) (by positivity) hmu n

/-- The tree-form margin in terms of the source parameters: `κ > (1+2 log 8)/(1−4δ)`. -/
theorem cmp116TreeRate_exceeds_entropy {delta kappa : ℝ} (hd : 4 * delta < 1)
    (h : lattice4EntropyRate / (1 - 4 * delta) < kappa) :
    lattice4EntropyRate < cmp116TreeRate delta kappa := by
  rw [cmp116TreeRate]
  have hpos : (0 : ℝ) < 1 - 4 * delta := by linarith
  rw [div_lt_iff₀ hpos] at h
  nlinarith

end YangMills
