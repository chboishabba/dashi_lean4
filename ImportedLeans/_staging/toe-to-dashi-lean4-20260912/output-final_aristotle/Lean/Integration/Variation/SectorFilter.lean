import Integration.Variation.Pairing

/-!
# QFT/GR frontier, lane 10 — sector aggregation beyond summability

Lane 1 aggregates sectors in two ways: over a finite index set (`pair_sum`) and
over an infinite *summable* family (`pair_tsum`), and lane 3 lifts the latter to
the stress level (`CutoffLimit.sector_aggregate_variation_tsum`).  Item 6 of the
frontier report flags exactly what those results do not cover: a sector total

```
T_total = ∑_G T_G
```

that is only *conditionally* convergent, i.e. that exists as a limit along an
exhaustion of the sector index but is not an unconditional sum.

This lane settles that item, in both directions.

* **Positive.**  Aggregation along an exhaustion is compatible with the pairing:
  if the partial sector sums converge to a total, the partial sector pairings
  converge to the pairing of the total (`tendsto_pair_of_tendsto_sum`), the
  total is unique (`exhaustion_total_unique`), and the summable case is the
  special case `hasSum_pair`.
* **Negative.**  The summability hypothesis of lane 1/lane 3 cannot be dropped.
  There is an explicit real sector family whose partial sums converge to `1`
  while `∑'` — the unconditional aggregate those theorems use — reports `0`
  (`conditionally_convergent_sector_family`).  Transporting it into an
  inner-product space gives a sector family with a genuine nonzero exhaustion
  total whose unconditional aggregate is the zero tensor
  (`exhaustion_total_is_not_the_unconditional_total`), so the two notions of
  "the total stress" are not interchangeable.

The witness is the telescoping family `f n = (-1)ⁿ (1/(n+1) + 1/(n+2))`, whose
partial sums are `1 - (-1)ᴺ/(N+1)` exactly.

## What is *not* proved

Nothing here says which of the two aggregates a physical sector decomposition
should use, and nothing here provides a renormalisation scheme: the point is
only that the choice is a real one and that the summable theorems do not make it.
-/

namespace Integration.Variation.SectorFilter

open Integration.Variation.Pairing
open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Summable sector aggregation at the level of the pairing. -/
theorem hasSum_pair {ι : Type*} {T : ι → H} {A : H} (h : HasSum T A) (v : H) :
    HasSum (fun i => pair (T i) v) (pair A v) := by
  have := (innerSL ℝ (E := H) v).hasSum h
  simpa [pair, real_inner_comm] using this

/-- **Aggregation along an exhaustion.**  If the partial sector sums converge to
a total tensor, then the partial sector pairings converge to the pairing of that
total — no summability required. -/
theorem tendsto_pair_of_tendsto_sum {ι : Type*} (T : ι → H) (A : H) (v : H)
    (s : ℕ → Finset ι)
    (h : Tendsto (fun N => ∑ i ∈ s N, T i) atTop (𝓝 A)) :
    Tendsto (fun N => ∑ i ∈ s N, pair (T i) v) atTop (𝓝 (pair A v)) := by
  have key := ((innerSL ℝ (E := H) v).continuous.tendsto A).comp h
  simp only [Function.comp_def] at key
  have hrw : (fun N => (innerSL ℝ (E := H) v) (∑ i ∈ s N, T i))
      = fun N => ∑ i ∈ s N, pair (T i) v := by
    funext N
    simp [pair, real_inner_comm]
  rw [hrw] at key
  simpa [pair, real_inner_comm] using key

omit [InnerProductSpace ℝ H] in
/-- The exhaustion total is unique when it exists. -/
theorem exhaustion_total_unique {ι : Type*} (T : ι → H) (s : ℕ → Finset ι) {A B : H}
    (hA : Tendsto (fun N => ∑ i ∈ s N, T i) atTop (𝓝 A))
    (hB : Tendsto (fun N => ∑ i ∈ s N, T i) atTop (𝓝 B)) : A = B :=
  tendsto_nhds_unique hA hB

/-- Summability transfers back along a nonzero direction. -/
theorem summable_of_smul_const {f : ℕ → ℝ} {e : H} (he : e ≠ 0)
    (h : Summable fun n => f n • e) : Summable f := by
  have hmap : Summable (fun n => (innerSL ℝ (E := H) e) (f n • e)) :=
    h.map (innerSL ℝ (E := H) e).toLinearMap.toAddMonoidHom
      (innerSL ℝ (E := H) e).continuous
  have hrw : (fun n => (innerSL ℝ (E := H) e) (f n • e)) = fun n => f n * ‖e‖ ^ 2 := by
    funext n
    simp
  rw [hrw] at hmap
  have hne : (‖e‖ : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr he)
  have hcancel : (fun n => f n * ‖e‖ ^ 2 / ‖e‖ ^ 2) = f := by
    funext n
    exact mul_div_cancel_right₀ (f n) hne
  have hfin := hmap.div_const (‖e‖ ^ 2)
  rwa [hcancel] at hfin

/-- The telescoping witness family `f n = (-1)ⁿ (1/(n+1) + 1/(n+2))`. -/
noncomputable def altTail (n : ℕ) : ℝ := (-1 : ℝ) ^ n / (n + 1)

noncomputable def condFamily (n : ℕ) : ℝ := altTail n - altTail (n + 1)

theorem condFamily_eq (n : ℕ) :
    condFamily n = (-1 : ℝ) ^ n * (1 / (n + 1) + 1 / (n + 2)) := by
  have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((n : ℝ) + 1 + 1) ≠ 0 := by positivity
  simp only [condFamily, altTail, pow_succ]
  push_cast
  field_simp
  ring

/-- The partial sums of the witness family telescope exactly. -/
theorem sum_range_condFamily (N : ℕ) :
    ∑ i ∈ Finset.range N, condFamily i = 1 - (-1 : ℝ) ^ N / (N + 1) := by
  have := Finset.sum_range_sub' (f := altTail) N
  simpa [condFamily, altTail] using this

theorem tendsto_altTail : Tendsto altTail atTop (𝓝 (0 : ℝ)) := by
  have hbound : ∀ n : ℕ, |altTail n| ≤ 1 / (n + 1) := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [altTail, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos hpos]
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine squeeze_zero_norm (fun n => ?_) hlim
  simpa using hbound n

/-- The witness family is not summable: its absolute values dominate the
harmonic series. -/
theorem not_summable_condFamily : ¬ Summable condFamily := by
  intro hsum
  have habs : Summable fun n => |condFamily n| := summable_abs_iff.2 hsum
  have hle : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ |condFamily n| := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    rw [condFamily_eq, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (by positivity : (0:ℝ) < 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 2))]
    have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  have hharm : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) :=
    habs.of_nonneg_of_le (fun n => by positivity) hle
  have hshift : Summable fun n : ℕ => 1 / ((n : ℝ)) := by
    refine (summable_nat_add_iff 1).1 ?_
    simpa using hharm
  exact Real.not_summable_one_div_natCast hshift

/-- **A conditionally convergent sector family.**  Its partial sums converge to
`1`, it is not summable, and therefore the unconditional aggregate `∑'` reports
`0`: the summability hypothesis in the infinite sector-aggregation theorems is
not removable. -/
theorem conditionally_convergent_sector_family :
    ∃ f : ℕ → ℝ, ¬ Summable f ∧
      Tendsto (fun N => ∑ i ∈ Finset.range N, f i) atTop (𝓝 1) ∧ ∑' i, f i = 0 := by
  refine ⟨condFamily, not_summable_condFamily, ?_, tsum_eq_zero_of_not_summable
    not_summable_condFamily⟩
  have hrw : (fun N => ∑ i ∈ Finset.range N, condFamily i)
      = fun N => 1 - altTail N := by
    funext N
    rw [sum_range_condFamily]
    rfl
  rw [hrw]
  simpa using tendsto_altTail.const_sub 1

/-- **The exhaustion total is not the unconditional total.**  In any nonzero
inner-product space there is a sector family whose partial sums along the
natural exhaustion converge to a nonzero tensor, while the unconditional
aggregate used by the summable theorems is the zero tensor.  Both are pairing
compatible — lane 1's `pair_tsum` is simply reporting a different object. -/
theorem exhaustion_total_is_not_the_unconditional_total (e : H) (he : e ≠ 0) :
    ∃ T : ℕ → H, ¬ Summable T ∧
      Tendsto (fun N => ∑ i ∈ Finset.range N, T i) atTop (𝓝 e) ∧
      ∑' i, T i = 0 ∧ (0 : H) ≠ e := by
  obtain ⟨f, hns, htend, htsum⟩ := conditionally_convergent_sector_family
  refine ⟨fun n => f n • e, ?_, ?_, ?_, fun h => he h.symm⟩
  · intro hsum
    exact hns (summable_of_smul_const he hsum)
  · have hsmul : Tendsto (fun N => (∑ i ∈ Finset.range N, f i) • e) atTop (𝓝 ((1 : ℝ) • e)) :=
      htend.smul_const e
    simpa [Finset.sum_smul] using hsmul
  · exact tsum_eq_zero_of_not_summable fun hsum => hns (summable_of_smul_const he hsum)

end Integration.Variation.SectorFilter
