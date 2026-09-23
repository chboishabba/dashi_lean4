/-
# Feeding the cluster bound into the existing continuum chain

`ExponentialCoordinate.lean` proves, with no unproved analytic input, that a selected
CMP116 boundary built from connecting walks in a bounded-degree graph obeys a
volume-uniform exponential bound in the graph distance between the two source marks.

`Continuum/WilsonLimit.lean` already contains the converse end of the route: from a
*cutoff-uniform* exponential clustering estimate for the literal Wilson covariance
`loopCov`, and nothing else, a subsequence of cutoffs exists along which the continuum
connected covariance obeys the same bound.

This file is the adapter between the two.  It is deliberately stated as an adapter:
its hypothesis `henv` is exactly the remaining *source attachment* — the statement that
the literal Wilson covariance at separation `t` is dominated by the selected boundary
of a CMP116 expansion whose two source marks sit at graph distance at least `t`.  That
attachment is **not** proved here and nothing in this file claims it is.  What is
proved is that once it is supplied, the cutoff-uniform clustering hypothesis of
`exists_subseq_wilson_continuum_clustering` follows mechanically, with an explicit
positive mass and an explicit volume-independent constant.
-/
import Mathlib
import RequestProject.YangMills.Cluster.ExponentialCoordinate
import RequestProject.YangMills.Continuum.WilsonLimit

namespace RequestProject.YangMills.Cluster

open Filter Topology MeasureTheory SimpleGraph
open RequestProject.YangMills.Lattice
open RequestProject.YangMills.RouteS
open RequestProject.YangMills.Continuum
open scoped ComplexConjugate

variable {Grp : Type*} [Group Grp] [TopologicalSpace Grp] [IsTopologicalGroup Grp]
  [CompactSpace Grp] [T2Space Grp] [MeasurableSpace Grp] [BorelSpace Grp]
  [SecondCountableTopology Grp]

/-- **Cutoff-uniform clustering from a cluster expansion.**  If, at every cutoff `k`
and separation `t`, the literal Wilson covariance is dominated by the selected boundary
of a CMP116 expansion whose connecting walks join two marks at graph distance at least
`t`, then the literal covariance obeys a cutoff-uniform exponential bound with mass
`clusterMass η > 0` and constant `c * clusterSeries Δ η`. -/
theorem wilson_uniform_clustering_of_cluster_expansion
    {V : Type*} [DecidableEq V] (Gr : SimpleGraph V) [Gr.LocallyFinite]
    (Δ : ℕ) (hΔ1 : 1 ≤ Δ) (hΔdeg : ∀ z, Gr.degree z ≤ Δ)
    (η c : ℝ) (hc : 0 ≤ c) (hη0 : 0 < η) (hη1 : η < 1) (hηΔ : (Δ : ℝ) ^ 2 * η < 1)
    (size : ℕ → ℕ) (beta : ℕ → ℝ) (chi : Grp → ℝ)
    (x y : (k : ℕ) → Site (size k)) (p q : List Step)
    {κ : Type*} (markL markR : ℕ → ℕ → V)
    (dom : ℕ → ℕ → Finset (Finset V))
    (terms : ℕ → ℕ → Finset V → Finset κ)
    (wt : (k t : ℕ) → κ → Gr.Walk (markL k t) (markR k t))
    (amp term : ℕ → ℕ → κ → ℝ) (commonY : ℕ → ℕ → Finset V → ℝ)
    (hamp : ∀ k t s, 0 ≤ amp k t s)
    (hne : ∀ k t, ∀ Y ∈ dom k t, (terms k t Y).Nonempty)
    (hsupp : ∀ k t, ∀ Y ∈ dom k t, ∀ s ∈ terms k t Y,
      (wt k t s).support.toFinset = Y)
    (hterm : ∀ k t, ∀ Y ∈ dom k t, ∀ s ∈ terms k t Y,
      |term k t s| ≤ amp k t s * (η * η) ^ (wt k t s).length)
    (hact : ∀ k t, ∀ Y ∈ dom k t, ∑ s ∈ terms k t Y, amp k t s ≤ c)
    (hcommon : ∀ k t, ∀ Y ∈ dom k t, commonY k t Y = ∑ s ∈ terms k t Y, term k t s)
    (hsep : ∀ k t, t ≤ Gr.dist (markL k t) (markR k t))
    (henv : ∀ k t, ‖loopCov (size k) Grp (beta k) chi (x k) (y k) p q t‖
      ≤ |∑ Y ∈ dom k t, commonY k t Y|) :
    ∀ k t : ℕ, ‖loopCov (size k) Grp (beta k) chi (x k) (y k) p q t‖
      ≤ (c * clusterSeries Δ η) * Real.exp (-(clusterMass η * t)) := by
  intro k t
  obtain ⟨hmass, hbound⟩ := selected_boundary_exponential_clustering Gr Δ hΔ1 hΔdeg
    (markL k t) (markR k t) η c hc hη0 hη1 hηΔ (dom k t) (terms k t) (wt k t)
    (amp k t) (term k t) (commonY k t) (hamp k t) (hne k t) (hsupp k t) (hterm k t)
    (hact k t) (hcommon k t)
  have hconst : (0 : ℝ) ≤ c * clusterSeries Δ η :=
    mul_nonneg hc (clusterSeries_nonneg Δ η hη0.le)
  have hmono : Real.exp (-(clusterMass η * Gr.dist (markL k t) (markR k t)))
      ≤ Real.exp (-(clusterMass η * t)) := by
    refine Real.exp_le_exp.mpr ?_
    have : (t : ℝ) ≤ (Gr.dist (markL k t) (markR k t) : ℝ) := by exact_mod_cast hsep k t
    nlinarith [hmass.le]
  calc ‖loopCov (size k) Grp (beta k) chi (x k) (y k) p q t‖
      ≤ |∑ Y ∈ dom k t, commonY k t Y| := henv k t
    _ ≤ (c * clusterSeries Δ η) *
          Real.exp (-(clusterMass η * Gr.dist (markL k t) (markR k t))) := hbound
    _ ≤ (c * clusterSeries Δ η) * Real.exp (-(clusterMass η * t)) :=
        mul_le_mul_of_nonneg_left hmono hconst

/-- **The adapter chained into the existing continuum capstone.**  With the same source
attachment, the continuum connected covariance produced by
`exists_subseq_wilson_continuum_clustering` obeys the exponential bound with the mass
and the constant coming from the cluster expansion. -/
theorem exists_subseq_continuum_clustering_of_cluster_expansion
    {V : Type*} [DecidableEq V] (Gr : SimpleGraph V) [Gr.LocallyFinite]
    (Δ : ℕ) (hΔ1 : 1 ≤ Δ) (hΔdeg : ∀ z, Gr.degree z ≤ Δ)
    (η c : ℝ) (hc : 0 ≤ c) (hη0 : 0 < η) (hη1 : η < 1) (hηΔ : (Δ : ℝ) ^ 2 * η < 1)
    (size : ℕ → ℕ) (beta : ℕ → ℝ) (chi : Grp → ℝ) (hchi : Continuous chi)
    {M : ℝ} (hM : ∀ g : Grp, |chi g| ≤ M)
    (x y : (k : ℕ) → Site (size k)) (p q : List Step)
    {κ : Type*} (markL markR : ℕ → ℕ → V)
    (dom : ℕ → ℕ → Finset (Finset V))
    (terms : ℕ → ℕ → Finset V → Finset κ)
    (wt : (k t : ℕ) → κ → Gr.Walk (markL k t) (markR k t))
    (amp term : ℕ → ℕ → κ → ℝ) (commonY : ℕ → ℕ → Finset V → ℝ)
    (hamp : ∀ k t s, 0 ≤ amp k t s)
    (hne : ∀ k t, ∀ Y ∈ dom k t, (terms k t Y).Nonempty)
    (hsupp : ∀ k t, ∀ Y ∈ dom k t, ∀ s ∈ terms k t Y,
      (wt k t s).support.toFinset = Y)
    (hterm : ∀ k t, ∀ Y ∈ dom k t, ∀ s ∈ terms k t Y,
      |term k t s| ≤ amp k t s * (η * η) ^ (wt k t s).length)
    (hact : ∀ k t, ∀ Y ∈ dom k t, ∑ s ∈ terms k t Y, amp k t s ≤ c)
    (hcommon : ∀ k t, ∀ Y ∈ dom k t, commonY k t Y = ∑ s ∈ terms k t Y, term k t s)
    (hsep : ∀ k t, t ≤ Gr.dist (markL k t) (markR k t))
    (henv : ∀ k t, ‖loopCov (size k) Grp (beta k) chi (x k) (y k) p q t‖
      ≤ |∑ Y ∈ dom k t, commonY k t Y|) :
    0 < clusterMass η ∧
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ abInf aInf bInf : ℕ → ℂ,
      (∀ t, Tendsto (fun k => ∫ U, conj (loopObs chi (x (φ k)) p U) *
          loopObs chi (y (φ k) + timeVec (size (φ k)) t) q U
          ∂(gibbs (size (φ k)) Grp (beta (φ k)) chi)) atTop (𝓝 (abInf t))) ∧
      (∀ t, Tendsto (fun k => ∫ U, loopObs chi (x (φ k)) p U
          ∂(gibbs (size (φ k)) Grp (beta (φ k)) chi)) atTop (𝓝 (aInf t))) ∧
      (∀ t, Tendsto (fun k => ∫ U, loopObs chi (y (φ k) + timeVec (size (φ k)) t) q U
          ∂(gibbs (size (φ k)) Grp (beta (φ k)) chi)) atTop (𝓝 (bInf t))) ∧
      ∀ t, ‖connected (abInf t) (aInf t) (bInf t)‖
        ≤ (c * clusterSeries Δ η) * Real.exp (-(clusterMass η * t)) := by
  refine ⟨clusterMass_pos hη0 hη1, ?_⟩
  exact exists_subseq_wilson_continuum_clustering size beta chi hchi hM x y p q
    (wilson_uniform_clustering_of_cluster_expansion Gr Δ hΔ1 hΔdeg η c hc hη0 hη1 hηΔ
      size beta chi x y p q markL markR dom terms wt amp term commonY hamp hne hsupp
      hterm hact hcommon hsep henv)

end RequestProject.YangMills.Cluster

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Cluster

#print axioms wilson_uniform_clustering_of_cluster_expansion
#print axioms exists_subseq_continuum_clustering_of_cluster_expansion

end Audit
