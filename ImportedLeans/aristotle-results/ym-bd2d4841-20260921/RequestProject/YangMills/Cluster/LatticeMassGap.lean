/-
# From the lattice cluster expansion to the Clay mass-gap conclusion

This file closes the Lean B-chain end to end, with the one-sided geometry proved rather
than assumed:

```
lattice cluster expansion data (support graph = the literal lattice)
      + proved entropy constant Δ = 8
      + proved one-sided geometry  t ≤ dist(x, y + timeVec t)
      + growing volumes
      ↓
finite-volume exponential clustering of the literal Wilson covariance
      ↓                                      (eventual in the cutoff: a torus
      ↓                                       cannot cluster past half its period)
continuum clustering of the connected covariance
      ↓                                      (S₅: the same-object spectral input)
Clay-form mass-gap conclusion for the Osterwalder–Schrader Hamiltonian
```

* `wilson_massGapConclusion_of_continuum_clustering` — the terminal step of Route `S`
  taking the continuum clustering estimate directly (the variant of
  `wilson_routeS_massGapConclusion` whose finite-volume half has already been done);
* `lattice_cluster_expansion_massGapConclusion` — the composite.

The hypotheses that remain unproved are exactly the physical ones: the source attachment
`henv` (the literal Bałaban differentiated estimate for the selected two-source Wilson
observable), convergence of the three literal Wilson expectations, and the same-object
spectral representation `hos` of the reconstructed Hamiltonian.  Everything geometric
and combinatorial between them is a theorem.
-/
import Mathlib
import RequestProject.YangMills.Cluster.WilsonLatticeBridge
import RequestProject.YangMills.RouteS.Assembly

namespace RequestProject.YangMills.Cluster

open Filter Topology MeasureTheory SimpleGraph
open RequestProject.YangMills.Lattice
open RequestProject.YangMills.RouteS
open RequestProject.YangMills.BIDI
open RequestProject.YangMills.Clay
open RequestProject.YangMills.Continuum
open scoped InnerProductSpace ComplexConjugate

/-- **The terminal Route-`S` step from a continuum clustering estimate.**  Given the
continuum exponential clustering of the selected pair at integer Euclidean separations
and the same-object spectral input for the reconstructed Hamiltonian, the Clay-form
mass-gap conclusion holds at the clustering rate. -/
theorem wilson_massGapConclusion_of_continuum_clustering
    {abI aI bI : ℕ → ℂ} {C alpha : ℝ} (halpha : 0 < alpha)
    (hclust : ∀ t : ℕ, ‖connected (abI t) (aI t) (bI t)‖ ≤ C * Real.exp (-(alpha * t)))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {H : E →ₗ.[ℂ] E} {vac : E} (spec : SpectralRepresentation H vac)
    (hos : ∀ psi : H.domain, ⟪vac, (psi : E)⟫_ℂ = 0 → ∀ k : ℕ,
      ∫ x, Real.exp (-((k : ℝ) * x)) ∂(spec.spectralMeasure psi)
        ≤ ‖(psi : E)‖ ^ 2 * ‖connected (abI k) (aI k) (bI k)‖)
    (hmem : vac ∈ H.domain) (hunit : ‖vac‖ = 1) (hground : H ⟨vac, hmem⟩ = 0)
    (hsa : IsSelfAdjoint H) :
    MassGapConclusion H vac alpha := by
  have hC0 : (0 : ℝ) ≤ C := by
    have h0 : ‖connected (abI 0) (aI 0) (bI 0)‖ ≤ C := by simpa using hclust 0
    exact le_trans (norm_nonneg _) h0
  have hnorm : ∀ (psi : H.domain) (k : ℕ),
      ‖((‖(psi : E)‖ ^ 2 : ℝ) : ℂ) * connected (abI k) (aI k) (bI k)‖
        = ‖(psi : E)‖ ^ 2 * ‖connected (abI k) (aI k) (bI k)‖ := by
    intro psi k
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine routeS_massGapConclusion
    (D := { spec := spec
            covInf := fun psi k =>
              ((‖(psi : E)‖ ^ 2 : ℝ) : ℂ) * connected (abI k) (aI k) (bI k)
            clusterConst := fun psi => ‖(psi : E)‖ ^ 2 * C
            clusterConst_nonneg := fun psi => by positivity
            alpha_pos := halpha
            os_same_object := by
              intro psi horth k
              rw [hnorm psi k]
              exact hos psi horth k
            clustering := by
              intro psi k
              rw [hnorm psi k, mul_assoc]
              exact mul_le_mul_of_nonneg_left (hclust k) (by positivity) })
    hmem hunit hground hsa

variable {Grp : Type*} [Group Grp] [TopologicalSpace Grp] [IsTopologicalGroup Grp]
  [CompactSpace Grp] [T2Space Grp] [MeasurableSpace Grp] [BorelSpace Grp]
  [SecondCountableTopology Grp]

/-- **The lattice cluster expansion yields the Clay mass-gap conclusion.**  The
localization domains of the expansion live on the literal nearest-neighbour graph of the
lattice, the two marks are the two literal Wilson-loop insertions on a common time slice,
and the volumes grow.  Then the reconstructed Osterwalder–Schrader Hamiltonian has no
spectrum in `(0, m)` on the vacuum complement, with `m = -log η > 0` the mass of the
expansion.

Unproved inputs: the source attachment `henv`, the convergence of the three literal
Wilson expectations, and the same-object spectral representation `hos`.  The entropy
constant, the tree localization, the domain summability and the one-sided time geometry
are all theorems. -/
theorem lattice_cluster_expansion_massGapConclusion
    {η c : ℝ} (hc : 0 ≤ c) (hη0 : 0 < η) (hη1 : η < 1) (hηΔ : 64 * η < 1)
    (size : ℕ → ℕ) (hgrow : Tendsto size atTop atTop)
    (beta : ℕ → ℝ) (chi : Grp → ℝ)
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
      ≤ |∑ Y ∈ dom k t, commonY k t Y|)
    {abI aI bI : ℕ → ℂ}
    (hab : ∀ t : ℕ, Tendsto (fun k => ∫ U, conj (loopObs chi (x k) p U) *
        loopObs chi (y k + timeVec (size k) t) q U ∂(gibbs (size k) Grp (beta k) chi))
      atTop (𝓝 (abI t)))
    (ha : ∀ t : ℕ, Tendsto (fun k => ∫ U, loopObs chi (x k) p U
        ∂(gibbs (size k) Grp (beta k) chi)) atTop (𝓝 (aI t)))
    (hb : ∀ t : ℕ, Tendsto (fun k => ∫ U, loopObs chi (y k + timeVec (size k) t) q U
        ∂(gibbs (size k) Grp (beta k) chi)) atTop (𝓝 (bI t)))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {H : E →ₗ.[ℂ] E} {vac : E} (spec : SpectralRepresentation H vac)
    (hos : ∀ psi : H.domain, ⟪vac, (psi : E)⟫_ℂ = 0 → ∀ k : ℕ,
      ∫ z, Real.exp (-((k : ℝ) * z)) ∂(spec.spectralMeasure psi)
        ≤ ‖(psi : E)‖ ^ 2 * ‖connected (abI k) (aI k) (bI k)‖)
    (hmem : vac ∈ H.domain) (hunit : ‖vac‖ = 1) (hground : H ⟨vac, hmem⟩ = 0)
    (hsa : IsSelfAdjoint H) :
    MassGapConclusion H vac (clusterMass η) := by
  have hfin := wilson_lattice_clustering_of_cluster_expansion hc hη0 hη1 hηΔ size beta chi
    x y p q hslice dom terms wt amp term commonY hamp hne hsupp hterm hact hcommon henv
  have hlim : ∀ t : ℕ, Tendsto (fun k => loopCov (size k) Grp (beta k) chi (x k) (y k) p q t)
      atTop (𝓝 (connected (abI t) (aI t) (bI t))) := by
    intro t
    have := tendsto_connected (hab t) (ha t) (hb t)
    refine this.congr fun k => ?_
    rw [loopCov_eq_connected]
  have hclust : ∀ t : ℕ, ‖connected (abI t) (aI t) (bI t)‖
      ≤ (c * clusterSeries 8 η) * Real.exp (-(clusterMass η * t)) := by
    refine RouteS.continuum_clustering_of_eventual_clustering hlim (fun t => ?_)
    filter_upwards [hgrow.eventually_ge_atTop (2 * t)] with k hk
    exact hfin k t (by omega)
  exact wilson_massGapConclusion_of_continuum_clustering (clusterMass_pos hη0 hη1) hclust
    spec hos hmem hunit hground hsa

end RequestProject.YangMills.Cluster

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Cluster

#print axioms wilson_massGapConclusion_of_continuum_clustering
#print axioms lattice_cluster_expansion_massGapConclusion

end Audit
