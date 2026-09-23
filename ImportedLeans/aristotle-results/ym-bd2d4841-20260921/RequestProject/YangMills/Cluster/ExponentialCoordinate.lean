/-
# The geometric weight in the physical exponential coordinate

The tree localization produces the decay weight `W d = η ^ d`.  The physical
(continuum-facing) coordinate is an exponential `exp (-m d)` with a strictly positive
mass `m`.  This file identifies the two, with `m = -log η`, and records the resulting
uniform exponential clustering bound for the selected CMP116 boundary.
-/
import RequestProject.YangMills.Cluster.SelectedBoundary

namespace RequestProject.YangMills.Cluster

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- The mass associated with a geometric activity weight `η`. -/
noncomputable def clusterMass (η : ℝ) : ℝ := -Real.log η

theorem clusterMass_pos {η : ℝ} (h0 : 0 < η) (h1 : η < 1) : 0 < clusterMass η := by
  rw [clusterMass, neg_pos]
  exact Real.log_neg h0 h1

/-- The geometric weight is literally the physical exponential weight. -/
theorem pow_eq_exp_clusterMass {η : ℝ} (h0 : 0 < η) (d : ℕ) :
    η ^ d = Real.exp (-(clusterMass η * d)) := by
  rw [clusterMass, neg_mul, neg_neg, Real.exp_mul, Real.exp_log h0, Real.rpow_natCast]

/-- **Uniform exponential clustering of the selected boundary.**  Restating the
B3 + B4 bound in the physical exponential coordinate: the selected CMP116 boundary
decays as `exp (-m · d)` in the distance between the two source marks, with a strictly
positive mass `m` and a constant independent of the family of localization domains. -/
theorem selected_boundary_exponential_clustering {ι : Type*}
    (G : SimpleGraph V) [G.LocallyFinite] (Δ : ℕ) (hΔ1 : 1 ≤ Δ)
    (hΔ : ∀ x, G.degree x ≤ Δ) (a b : V) (η c : ℝ) (hc : 0 ≤ c)
    (hη0 : 0 < η) (hη1 : η < 1) (hη : (Δ : ℝ) ^ 2 * η < 1)
    (𝒟 : Finset (Finset V)) (terms : Finset V → Finset ι) (wt : ι → G.Walk a b)
    (amp term : ι → ℝ) (commonY : Finset V → ℝ)
    (hamp : ∀ t, 0 ≤ amp t)
    (hne : ∀ Y ∈ 𝒟, (terms Y).Nonempty)
    (hsupp : ∀ Y ∈ 𝒟, ∀ t ∈ terms Y, (wt t).support.toFinset = Y)
    (hterm : ∀ Y ∈ 𝒟, ∀ t ∈ terms Y, |term t| ≤ amp t * (η * η) ^ (wt t).length)
    (hact : ∀ Y ∈ 𝒟, ∑ t ∈ terms Y, amp t ≤ c)
    (hcommon : ∀ Y ∈ 𝒟, commonY Y = ∑ t ∈ terms Y, term t) :
    0 < clusterMass η ∧
      |∑ Y ∈ 𝒟, commonY Y|
        ≤ (c * clusterSeries Δ η) * Real.exp (-(clusterMass η * G.dist a b)) := by
  refine ⟨clusterMass_pos hη0 hη1, ?_⟩
  have key := selected_boundary_below_connecting_decay G Δ hΔ1 hΔ a b η c hc
    hη0.le hη1.le hη 𝒟 terms wt amp term commonY hamp hne hsupp hterm hact hcommon
  rwa [pow_eq_exp_clusterMass hη0] at key

end RequestProject.YangMills.Cluster

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Cluster

#print axioms selected_boundary_exponential_clustering

end Audit
