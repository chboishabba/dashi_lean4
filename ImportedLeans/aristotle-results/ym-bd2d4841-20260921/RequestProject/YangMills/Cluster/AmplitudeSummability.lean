/-
# B4: outer amplitude control

This file proves the outer CMP116 amplitude estimate

  `∑_Y A_Y ≤ A_src`,

uniformly in the family of localization domains, hence uniformly in the volume.

The hypotheses are exactly the two things B3 supplies and the small-field input:

* each domain `Y` is connected and contains the fixed source mark `v`;
* `0 ≤ A_Y ≤ c * η ^ (#Y - 1)` — the per-domain amplitude produced by
  `per_domain_tree_localization`, with `c` the uniform bound on the total activity of
  a domain.

The entropy of connected domains is not assumed: it is the theorem
`card_domains_le`, proved from the closed-tour construction and bounded-degree walk
counting.  The resulting constant

  `A_src = c * ∑' m, (2m+1) * (Δ² η) ^ m`

is finite precisely in the small-field regime `Δ² η < 1`.
-/
import RequestProject.YangMills.Cluster.DomainCount

open Finset

namespace RequestProject.YangMills.Cluster

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- The Kotecký–Preiss series of the domain entropy.  Finite exactly when `Δ² η < 1`. -/
noncomputable def clusterSeries (Δ : ℕ) (η : ℝ) : ℝ :=
  ∑' m : ℕ, (2 * (m : ℝ) + 1) * ((Δ : ℝ) ^ 2 * η) ^ m

theorem summable_clusterSeries (Δ : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη : (Δ : ℝ) ^ 2 * η < 1) :
    Summable fun m : ℕ => (2 * (m : ℝ) + 1) * ((Δ : ℝ) ^ 2 * η) ^ m := by
  set r : ℝ := (Δ : ℝ) ^ 2 * η with hr
  have hr0 : 0 ≤ r := mul_nonneg (by positivity) hη0
  have hnorm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hη
  have h1 : Summable fun m : ℕ => (m : ℝ) ^ 1 * r ^ m :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have h2 : Summable fun m : ℕ => r ^ m := summable_geometric_of_norm_lt_one hnorm
  refine ((h1.mul_left 2).add h2).congr fun m => ?_
  ring

theorem clusterSeries_nonneg (Δ : ℕ) (η : ℝ) (hη0 : 0 ≤ η) : 0 ≤ clusterSeries Δ η := by
  refine tsum_nonneg fun m => ?_
  have : (0 : ℝ) ≤ (Δ : ℝ) ^ 2 * η := mul_nonneg (by positivity) hη0
  positivity

/-- **B4, outer amplitude control.**  The amplitudes of any finite family of connected
localization domains through a fixed source mark sum to at most
`c * clusterSeries Δ η`, uniformly in the family. -/
theorem outer_amplitude_summability (G : SimpleGraph V) [G.LocallyFinite] (Δ : ℕ)
    (hΔ1 : 1 ≤ Δ) (hΔ : ∀ x, G.degree x ≤ Δ) (v : V) (η c : ℝ) (hc : 0 ≤ c)
    (hη0 : 0 ≤ η) (hη : (Δ : ℝ) ^ 2 * η < 1)
    (𝒟 : Finset (Finset V)) (A : Finset V → ℝ)
    (hdom : ∀ Y ∈ 𝒟, v ∈ Y ∧ IsDomainConnected G Y)
    (hA : ∀ Y ∈ 𝒟, 0 ≤ A Y ∧ A Y ≤ c * η ^ (#Y - 1)) :
    ∑ Y ∈ 𝒟, A Y ≤ c * clusterSeries Δ η := by
  classical
  set N := 𝒟.sup fun Y => #Y - 1 with hN
  set g : ℕ → ℝ := fun m => (2 * (m : ℝ) + 1) * ((Δ : ℝ) ^ 2 * η) ^ m with hg
  have hmaps : ∀ Y ∈ 𝒟, (#Y - 1) ∈ Finset.range (N + 1) := by
    intro Y hY
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.le_sup (f := fun Y => #Y - 1) hY))
  -- step 1: replace the amplitudes by their small-field majorant
  have step1 : ∑ Y ∈ 𝒟, A Y ≤ ∑ Y ∈ 𝒟, c * η ^ (#Y - 1) :=
    Finset.sum_le_sum fun Y hY => (hA Y hY).2
  -- step 2: fibre the family over the reduced domain size
  have step2 : ∑ Y ∈ 𝒟, c * η ^ (#Y - 1)
      = ∑ m ∈ Finset.range (N + 1), ∑ Y ∈ 𝒟 with #Y - 1 = m, c * η ^ (#Y - 1) :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  -- step 3: on each fibre use the entropy bound
  have step3 : ∀ m ∈ Finset.range (N + 1),
      (∑ Y ∈ 𝒟 with #Y - 1 = m, c * η ^ (#Y - 1)) ≤ c * g m := by
    intro m _
    have hfib : ∀ Y ∈ 𝒟.filter fun Y => #Y - 1 = m,
        v ∈ Y ∧ IsDomainConnected G Y ∧ #Y = m + 1 := by
      intro Y hY
      rw [Finset.mem_filter] at hY
      obtain ⟨hv, hconn⟩ := hdom Y hY.1
      have hcard : 1 ≤ #Y := Finset.card_pos.mpr ⟨v, hv⟩
      exact ⟨hv, hconn, by omega⟩
    have hcount : #(𝒟.filter fun Y => #Y - 1 = m) ≤ (2 * m + 1) * Δ ^ (2 * m) :=
      card_domains_le G Δ hΔ1 hΔ v m _ hfib
    have hconst : (∑ Y ∈ 𝒟 with #Y - 1 = m, c * η ^ (#Y - 1))
        = (#(𝒟.filter fun Y => #Y - 1 = m) : ℝ) * (c * η ^ m) := by
      rw [Finset.sum_congr rfl (fun Y hY => by
        rw [(Finset.mem_filter.mp hY).2]), Finset.sum_const, nsmul_eq_mul]
    rw [hconst]
    have hcη : (0 : ℝ) ≤ c * η ^ m := mul_nonneg hc (pow_nonneg hη0 m)
    calc (#(𝒟.filter fun Y => #Y - 1 = m) : ℝ) * (c * η ^ m)
        ≤ ((2 * m + 1 : ℕ) * (Δ : ℝ) ^ (2 * m)) * (c * η ^ m) := by
          refine mul_le_mul_of_nonneg_right ?_ hcη
          exact_mod_cast hcount
      _ = c * g m := by
          rw [hg]
          push_cast
          rw [mul_pow, ← pow_mul]
          ring
  -- step 4: compare the finite sum with the full Kotecký–Preiss series
  have hsummable := summable_clusterSeries Δ η hη0 hη
  have hgnn : ∀ m : ℕ, 0 ≤ g m := by
    intro m
    have : (0 : ℝ) ≤ (Δ : ℝ) ^ 2 * η := mul_nonneg (by positivity) hη0
    rw [hg]; positivity
  calc ∑ Y ∈ 𝒟, A Y
      ≤ ∑ Y ∈ 𝒟, c * η ^ (#Y - 1) := step1
    _ = ∑ m ∈ Finset.range (N + 1), ∑ Y ∈ 𝒟 with #Y - 1 = m, c * η ^ (#Y - 1) := step2
    _ ≤ ∑ m ∈ Finset.range (N + 1), c * g m := Finset.sum_le_sum step3
    _ = c * ∑ m ∈ Finset.range (N + 1), g m := by rw [Finset.mul_sum]
    _ ≤ c * clusterSeries Δ η := by
        refine mul_le_mul_of_nonneg_left ?_ hc
        exact hsummable.sum_le_tsum _ (fun m _ => hgnn m)

end RequestProject.YangMills.Cluster
