/-
# B3 + B4: the selected boundary obeys the connecting exponential decay

This file composes the per-domain tree localization (B3) with the outer amplitude
control (B4) into the statement the CMP116 route needs:

  `|selected boundary| ≤ A_src * W (d_selected)`,  `W d = η ^ d`,

where `d_selected = G.dist a b` is the genuine graph distance between the two source
marks and `A_src = c * clusterSeries Δ η` is a constant independent of the family of
localization domains, hence of the volume.

The inputs are the literal expansion data:

* `term t` — the differentiated CMP116 generalized-walk/local-activity term carried by
  the connecting walk `wt t` between the two marks;
* `|term t| ≤ amp t * (η*η) ^ (wt t).length` — the factorwise majorant, with the
  activity weight `η*η` per edge of the connecting walk;
* `(wt t).support.toFinset = Y` — the surviving term of the domain `Y` lives exactly on
  `Y` (so both source marks belong to `Y` and `Y` is connected: this is proved, not
  assumed, via `isDomainConnected_support`);
* `∑ amplitudes of a domain ≤ c` — the uniform small-field activity bound;
* `Δ² η < 1` — the small-field regime.

No step of the composition is postulated.
-/
import RequestProject.YangMills.Cluster.AmplitudeSummability
import RequestProject.YangMills.Cluster.TreeLocalization

open Finset

namespace RequestProject.YangMills.Cluster

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- **B3 + B4.**  The selected CMP116 boundary of any finite family of localization
domains is bounded by a volume-independent amplitude times the exponential weight at
the graph distance between the two source marks. -/
theorem selected_boundary_below_connecting_decay {ι : Type*}
    (G : SimpleGraph V) [G.LocallyFinite] (Δ : ℕ) (hΔ1 : 1 ≤ Δ)
    (hΔ : ∀ x, G.degree x ≤ Δ) (a b : V) (η c : ℝ) (hc : 0 ≤ c)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hη : (Δ : ℝ) ^ 2 * η < 1)
    (𝒟 : Finset (Finset V)) (terms : Finset V → Finset ι) (wt : ι → G.Walk a b)
    (amp term : ι → ℝ) (commonY : Finset V → ℝ)
    (hamp : ∀ t, 0 ≤ amp t)
    (hne : ∀ Y ∈ 𝒟, (terms Y).Nonempty)
    (hsupp : ∀ Y ∈ 𝒟, ∀ t ∈ terms Y, (wt t).support.toFinset = Y)
    (hterm : ∀ Y ∈ 𝒟, ∀ t ∈ terms Y, |term t| ≤ amp t * (η * η) ^ (wt t).length)
    (hact : ∀ Y ∈ 𝒟, ∑ t ∈ terms Y, amp t ≤ c)
    (hcommon : ∀ Y ∈ 𝒟, commonY Y = ∑ t ∈ terms Y, term t) :
    |∑ Y ∈ 𝒟, commonY Y| ≤ (c * clusterSeries Δ η) * η ^ G.dist a b := by
  classical
  set A : Finset V → ℝ := fun Y => (∑ t ∈ terms Y, amp t) * η ^ (#Y - 1) with hAdef
  -- every domain is connected and contains the source mark `a`
  have hdom : ∀ Y ∈ 𝒟, a ∈ Y ∧ IsDomainConnected G Y := by
    intro Y hY
    obtain ⟨t, ht⟩ := hne Y hY
    have hYs := hsupp Y hY t ht
    constructor
    · rw [← hYs]; exact List.mem_toFinset.mpr (Walk.start_mem_support _)
    · rw [← hYs]; exact isDomainConnected_support (wt t)
  -- B3: per-domain localization
  have hB3 : ∀ Y ∈ 𝒟, |commonY Y| ≤ A Y * η ^ G.dist a b := by
    intro Y hY
    have hspan : ∀ t ∈ terms Y, Y ⊆ (wt t).support.toFinset := by
      intro t ht; rw [hsupp Y hY t ht]
    calc |commonY Y| = |∑ t ∈ terms Y, term t| := by rw [hcommon Y hY]
      _ ≤ ∑ t ∈ terms Y, |term t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ terms Y, amp t * (η * η) ^ (wt t).length :=
          Finset.sum_le_sum (hterm Y hY)
      _ ≤ A Y * η ^ G.dist a b :=
          per_domain_tree_localization_dist Y (terms Y) wt amp
            (fun t _ => hamp t) η hη0 hη1 hspan
  -- B4: outer amplitude control
  have hAnn : ∀ Y ∈ 𝒟, 0 ≤ A Y ∧ A Y ≤ c * η ^ (#Y - 1) := by
    intro Y hY
    refine ⟨mul_nonneg (Finset.sum_nonneg fun t _ => hamp t) (pow_nonneg hη0 _), ?_⟩
    exact mul_le_mul_of_nonneg_right (hact Y hY) (pow_nonneg hη0 _)
  have hB4 : ∑ Y ∈ 𝒟, A Y ≤ c * clusterSeries Δ η :=
    outer_amplitude_summability G Δ hΔ1 hΔ a η c hc hη0 hη 𝒟 A hdom hAnn
  calc |∑ Y ∈ 𝒟, commonY Y|
      ≤ ∑ Y ∈ 𝒟, |commonY Y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ Y ∈ 𝒟, A Y * η ^ G.dist a b := Finset.sum_le_sum hB3
    _ = (∑ Y ∈ 𝒟, A Y) * η ^ G.dist a b := by rw [← Finset.sum_mul]
    _ ≤ (c * clusterSeries Δ η) * η ^ G.dist a b :=
        mul_le_mul_of_nonneg_right hB4 (pow_nonneg hη0 _)

end RequestProject.YangMills.Cluster

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Cluster

#print axioms card_domains_le
#print axioms per_domain_tree_localization
#print axioms outer_amplitude_summability
#print axioms selected_boundary_below_connecting_decay

end Audit
