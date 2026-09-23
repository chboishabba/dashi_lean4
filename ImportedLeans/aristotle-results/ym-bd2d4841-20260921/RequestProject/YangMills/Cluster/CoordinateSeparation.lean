/-
# Physical coordinate separation is a lower bound for the graph distance

The decay produced by the tree localization is exponential in the *graph* distance
between the two source marks.  To read it as decay in a physical separation one needs

  `physical separation ≤ graph distance`.

This file proves the general tool for that: any coordinate that moves by at most one
unit along an edge of the support graph has coordinate separation bounded by the graph
distance.  Applied to a lattice coordinate (a time slice label, say), this converts a
physical separation into the exponent of the cluster bound.
-/
import RequestProject.YangMills.Cluster.ExponentialCoordinate

namespace RequestProject.YangMills.Cluster

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A unit-Lipschitz coordinate moves by at most the length of a walk. -/
theorem abs_sub_le_length_of_unitLipschitz {f : V → ℝ}
    (hf : ∀ x y, G.Adj x y → |f x - f y| ≤ 1) {a b : V} (w : G.Walk a b) :
    |f a - f b| ≤ w.length := by
  induction w with
  | nil => simp
  | cons hadj q ih =>
    rename_i x y z
    have hstep : |f x - f y| ≤ 1 := hf x y hadj
    have htri : |f x - f z| ≤ |f x - f y| + |f y - f z| := abs_sub_le _ _ _
    rw [Walk.length_cons]
    push_cast
    linarith

/-- **Coordinate separation bounds the graph distance from below.**  If `f` changes by
at most one unit along every edge, then the coordinate separation of two reachable
vertices is at most their graph distance. -/
theorem abs_sub_le_dist_of_unitLipschitz {f : V → ℝ}
    (hf : ∀ x y, G.Adj x y → |f x - f y| ≤ 1) {a b : V} (hr : G.Reachable a b) :
    |f a - f b| ≤ G.dist a b := by
  obtain ⟨w, hw⟩ := hr.exists_walk_length_eq_dist
  have := abs_sub_le_length_of_unitLipschitz hf w
  rwa [hw] at this

/-- The exponential weight at the graph distance is dominated by the exponential weight
at the physical coordinate separation. -/
theorem exp_dist_le_exp_coordinate {f : V → ℝ}
    (hf : ∀ x y, G.Adj x y → |f x - f y| ≤ 1) {a b : V} (hr : G.Reachable a b)
    {η : ℝ} (h0 : 0 < η) (h1 : η < 1) :
    Real.exp (-(clusterMass η * G.dist a b)) ≤ Real.exp (-(clusterMass η * |f a - f b|)) := by
  have hm : 0 < clusterMass η := clusterMass_pos h0 h1
  have hsep := abs_sub_le_dist_of_unitLipschitz hf hr
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- **The cluster bound in a physical coordinate.**  The selected CMP116 boundary decays
exponentially in the separation of the two source marks measured by any unit-Lipschitz
coordinate on the support graph, with a strictly positive mass and a constant
independent of the family of localization domains. -/
theorem selected_boundary_exponential_clustering_coordinate {ι : Type*} [DecidableEq V]
    [G.LocallyFinite] (Δ : ℕ) (hΔ1 : 1 ≤ Δ) (hΔ : ∀ x, G.degree x ≤ Δ) {a b : V}
    (f : V → ℝ) (hf : ∀ x y, G.Adj x y → |f x - f y| ≤ 1) (hr : G.Reachable a b)
    (η c : ℝ) (hc : 0 ≤ c) (hη0 : 0 < η) (hη1 : η < 1) (hηΔ : (Δ : ℝ) ^ 2 * η < 1)
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
        ≤ (c * clusterSeries Δ η) * Real.exp (-(clusterMass η * |f a - f b|)) := by
  obtain ⟨hmass, hbound⟩ := selected_boundary_exponential_clustering G Δ hΔ1 hΔ a b η c hc
    hη0 hη1 hηΔ 𝒟 terms wt amp term commonY hamp hne hsupp hterm hact hcommon
  refine ⟨hmass, hbound.trans (mul_le_mul_of_nonneg_left ?_ ?_)⟩
  · exact exp_dist_le_exp_coordinate hf hr hη0 hη1
  · exact mul_nonneg hc (clusterSeries_nonneg Δ η hη0.le)

end RequestProject.YangMills.Cluster

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Cluster

#print axioms abs_sub_le_dist_of_unitLipschitz
#print axioms selected_boundary_exponential_clustering_coordinate

end Audit
