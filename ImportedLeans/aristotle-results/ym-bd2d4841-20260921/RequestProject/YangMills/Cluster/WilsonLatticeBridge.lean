/-
# The cluster expansion on the literal lattice, fed into the continuum limit

`Cluster/WilsonClusterBridge.lean` is an adapter with two source hypotheses: `henv`, the
identification of the literal Wilson covariance with the selected boundary of a CMP116
expansion, and `hsep`, the assertion that the two source marks are at graph distance at
least the Euclidean separation `t`.

This file removes the second one.  On the literal lattice the expansion lives on the
nearest-neighbour support graph `latticeGraph (size k)`, the two marks are the literal
insertion sites `x k` and `y k + timeVec (size k) t`, the entropy constant is the proved
`Δ = 8`, and the separation statement is the *theorem*
`le_dist_timeVec_of_sameSlice` — valid, as it must be on a torus, for separations below
half the period.  What is left is `henv` alone: the source attachment, which is not
proved here and is not claimed to be.

* `wilson_lattice_clustering_of_cluster_expansion` — the finite-volume estimate, for
  every cutoff and every separation the volume can accommodate;
* `exists_subseq_wilson_lattice_continuum_clustering` — chained through the
  eventual-clustering capstone of `Continuum/EventualClustering.lean`: as the volumes
  grow, the continuum connected covariance inherits the same mass and constant.
-/
import Mathlib
import RequestProject.YangMills.Cluster.LatticeTimeDistance
import RequestProject.YangMills.Continuum.EventualClustering

namespace RequestProject.YangMills.Cluster

open Filter Topology MeasureTheory SimpleGraph
open RequestProject.YangMills.Lattice
open RequestProject.YangMills.RouteS
open RequestProject.YangMills.Continuum
open scoped ComplexConjugate

variable {Grp : Type*} [Group Grp] [TopologicalSpace Grp] [IsTopologicalGroup Grp]
  [CompactSpace Grp] [T2Space Grp] [MeasurableSpace Grp] [BorelSpace Grp]
  [SecondCountableTopology Grp]

/-- **Finite-volume clustering of the literal Wilson covariance from a lattice cluster
expansion.**  The two insertions sit on a common time slice; the expansion at cutoff `k`
and separation `t` lives on the literal nearest-neighbour graph of the lattice, with the
two marks at the two insertion sites.  Then, for every separation below half the period,
the literal Wilson covariance obeys the exponential bound with mass `clusterMass η > 0`
and the volume-independent constant `c * clusterSeries 8 η`.  The geometric input is
proved; the only unproved ingredient is the source attachment `henv`. -/
theorem wilson_lattice_clustering_of_cluster_expansion
    {η c : ℝ} (hc : 0 ≤ c) (hη0 : 0 < η) (hη1 : η < 1) (hηΔ : 64 * η < 1)
    (size : ℕ → ℕ) (beta : ℕ → ℝ) (chi : Grp → ℝ)
    (x y : (k : ℕ) → Site (size k)) (p q : List Step)
    (hslice : ∀ k, x k timeDir = y k timeDir)
    {κ : Type*}
    (dom : (k t : ℕ) → Finset (Finset (Site (size k))))
    (terms : (k t : ℕ) → Finset (Site (size k)) → Finset κ)
    (wt : (k t : ℕ) → κ → (latticeGraph (size k)).Walk (x k) (y k + timeVec (size k) t))
    (amp term : ℕ → ℕ → κ → ℝ)
    (commonY : (k t : ℕ) → Finset (Site (size k)) → ℝ)
    (hamp : ∀ k t s, 0 ≤ amp k t s)
    (hne : ∀ k t, ∀ Y ∈ dom k t, (terms k t Y).Nonempty)
    (hsupp : ∀ k t, ∀ Y ∈ dom k t, ∀ s ∈ terms k t Y, (wt k t s).support.toFinset = Y)
    (hterm : ∀ k t, ∀ Y ∈ dom k t, ∀ s ∈ terms k t Y,
      |term k t s| ≤ amp k t s * (η * η) ^ (wt k t s).length)
    (hact : ∀ k t, ∀ Y ∈ dom k t, ∑ s ∈ terms k t Y, amp k t s ≤ c)
    (hcommon : ∀ k t, ∀ Y ∈ dom k t, commonY k t Y = ∑ s ∈ terms k t Y, term k t s)
    (henv : ∀ k t, ‖loopCov (size k) Grp (beta k) chi (x k) (y k) p q t‖
      ≤ |∑ Y ∈ dom k t, commonY k t Y|) :
    ∀ k t : ℕ, 2 * t < size k + 1 →
      ‖loopCov (size k) Grp (beta k) chi (x k) (y k) p q t‖
        ≤ (c * clusterSeries 8 η) * Real.exp (-(clusterMass η * t)) := by
  intro k t ht
  obtain ⟨hmass, hbound⟩ :=
    selected_boundary_exponential_clustering (latticeGraph (size k)) 8 (by norm_num)
      degree_le_eight (x k) (y k + timeVec (size k) t) η c hc hη0 hη1
      (by push_cast; linarith) (dom k t) (terms k t) (wt k t) (amp k t) (term k t)
      (commonY k t) (hamp k t) (hne k t) (hsupp k t) (hterm k t) (hact k t) (hcommon k t)
  have hconst : (0 : ℝ) ≤ c * clusterSeries 8 η :=
    mul_nonneg hc (clusterSeries_nonneg 8 η hη0.le)
  have hsep : (t : ℝ)
      ≤ ((latticeGraph (size k)).dist (x k) (y k + timeVec (size k) t) : ℝ) := by
    exact_mod_cast le_dist_timeVec_of_sameSlice (hslice k) ht
  have hmono : Real.exp (-(clusterMass η *
        (latticeGraph (size k)).dist (x k) (y k + timeVec (size k) t)))
      ≤ Real.exp (-(clusterMass η * t)) :=
    Real.exp_le_exp.mpr (by nlinarith [hmass.le])
  calc ‖loopCov (size k) Grp (beta k) chi (x k) (y k) p q t‖
      ≤ |∑ Y ∈ dom k t, commonY k t Y| := henv k t
    _ ≤ (c * clusterSeries 8 η) * Real.exp (-(clusterMass η *
          (latticeGraph (size k)).dist (x k) (y k + timeVec (size k) t))) := hbound
    _ ≤ (c * clusterSeries 8 η) * Real.exp (-(clusterMass η * t)) :=
        mul_le_mul_of_nonneg_left hmono hconst

/-- **The lattice cluster expansion produces continuum clustering.**  With the volumes
growing, the finite estimate above holds, at each fixed separation, for all large
cutoffs; the eventual-clustering capstone then gives a subsequence along which the three
literal Wilson expectations converge and the continuum connected covariance obeys the
same exponential bound, with a strictly positive mass. -/
theorem exists_subseq_wilson_lattice_continuum_clustering
    {η c : ℝ} (hc : 0 ≤ c) (hη0 : 0 < η) (hη1 : η < 1) (hηΔ : 64 * η < 1)
    (size : ℕ → ℕ) (hgrow : Tendsto size atTop atTop)
    (beta : ℕ → ℝ) (chi : Grp → ℝ) (hchi : Continuous chi)
    {M : ℝ} (hM : ∀ g : Grp, |chi g| ≤ M)
    (x y : (k : ℕ) → Site (size k)) (p q : List Step)
    (hslice : ∀ k, x k timeDir = y k timeDir)
    {κ : Type*}
    (dom : (k t : ℕ) → Finset (Finset (Site (size k))))
    (terms : (k t : ℕ) → Finset (Site (size k)) → Finset κ)
    (wt : (k t : ℕ) → κ → (latticeGraph (size k)).Walk (x k) (y k + timeVec (size k) t))
    (amp term : ℕ → ℕ → κ → ℝ)
    (commonY : (k t : ℕ) → Finset (Site (size k)) → ℝ)
    (hamp : ∀ k t s, 0 ≤ amp k t s)
    (hne : ∀ k t, ∀ Y ∈ dom k t, (terms k t Y).Nonempty)
    (hsupp : ∀ k t, ∀ Y ∈ dom k t, ∀ s ∈ terms k t Y, (wt k t s).support.toFinset = Y)
    (hterm : ∀ k t, ∀ Y ∈ dom k t, ∀ s ∈ terms k t Y,
      |term k t s| ≤ amp k t s * (η * η) ^ (wt k t s).length)
    (hact : ∀ k t, ∀ Y ∈ dom k t, ∑ s ∈ terms k t Y, amp k t s ≤ c)
    (hcommon : ∀ k t, ∀ Y ∈ dom k t, commonY k t Y = ∑ s ∈ terms k t Y, term k t s)
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
        ≤ (c * clusterSeries 8 η) * Real.exp (-(clusterMass η * t)) := by
  refine ⟨clusterMass_pos hη0 hη1, ?_⟩
  have hfin := wilson_lattice_clustering_of_cluster_expansion hc hη0 hη1 hηΔ size beta chi
    x y p q hslice dom terms wt amp term commonY hamp hne hsupp hterm hact hcommon henv
  refine exists_subseq_wilson_continuum_clustering_eventually size beta chi hchi hM x y p q
    (fun t => ?_)
  filter_upwards [hgrow.eventually_ge_atTop (2 * t)] with k hk
  exact hfin k t (by omega)

end RequestProject.YangMills.Cluster

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Cluster

#print axioms wilson_lattice_clustering_of_cluster_expansion
#print axioms exists_subseq_wilson_lattice_continuum_clustering

end Audit
