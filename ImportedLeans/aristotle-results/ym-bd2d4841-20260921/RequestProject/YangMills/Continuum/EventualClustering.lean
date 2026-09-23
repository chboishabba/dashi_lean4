/-
# Clustering that holds only eventually in the cutoff

A finite *periodic* volume cannot obey an exponential clustering bound at every
separation: beyond half the period the two insertions come back together around the
torus.  Any estimate proved from the finite geometry — for instance the one-sided
geometry of `Cluster/LatticeTimeSeparation.lean`, which needs `2t` below the period — is
therefore available only for the separations the volume can accommodate, i.e. for each
fixed separation only for all sufficiently large volumes.

This is not a defect of the estimate: it is exactly the infinite-volume limit.  The
continuum machinery of `Continuum/WilsonLimit.lean` demands the bound at every cutoff,
which is stronger than necessary, since the conclusion is about a limit.  This file
weakens the hypothesis to the honest one:

  for every separation `t`, the bound holds for all sufficiently large cutoffs.

The general transfer for a converging family is already available as
`RouteS.continuum_clustering_of_eventual_clustering`; what is added here is the literal
Wilson capstone `exists_subseq_wilson_continuum_clustering_eventually`, which produces
the converging subsequence itself and has the same conclusion as
`exists_subseq_wilson_continuum_clustering`.
-/
import Mathlib
import RequestProject.YangMills.Continuum.WilsonLimit

namespace RequestProject.YangMills.Continuum

open Filter Topology MeasureTheory
open RequestProject.YangMills.Lattice
open RequestProject.YangMills.RouteS
open scoped ComplexConjugate

variable {ι : Type*} {l : Filter ι}
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]

/-- **The literal Wilson capstone under eventual clustering.**  If for every Euclidean
separation the literal Wilson covariance obeys the exponential bound at all sufficiently
large cutoffs, then along a subsequence the three literal Wilson expectations converge
and the continuum connected covariance obeys the same bound, with the same constant and
rate. -/
theorem exists_subseq_wilson_continuum_clustering_eventually (size : ℕ → ℕ) (beta : ℕ → ℝ)
    (chi : G → ℝ) (hchi : Continuous chi) {M : ℝ} (hM : ∀ g : G, |chi g| ≤ M)
    (x y : (k : ℕ) → Site (size k)) (p q : List Step) {C alpha : ℝ}
    (hcluster : ∀ t : ℕ, ∀ᶠ k in atTop,
      ‖loopCov (size k) G (beta k) chi (x k) (y k) p q t‖ ≤ C * Real.exp (-(alpha * t))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ abInf aInf bInf : ℕ → ℂ,
      (∀ t, Tendsto (fun k => ∫ U, conj (loopObs chi (x (φ k)) p U) *
          loopObs chi (y (φ k) + timeVec (size (φ k)) t) q U
          ∂(gibbs (size (φ k)) G (beta (φ k)) chi)) atTop (𝓝 (abInf t))) ∧
      (∀ t, Tendsto (fun k => ∫ U, loopObs chi (x (φ k)) p U
          ∂(gibbs (size (φ k)) G (beta (φ k)) chi)) atTop (𝓝 (aInf t))) ∧
      (∀ t, Tendsto (fun k => ∫ U, loopObs chi (y (φ k) + timeVec (size (φ k)) t) q U
          ∂(gibbs (size (φ k)) G (beta (φ k)) chi)) atTop (𝓝 (bInf t))) ∧
      ∀ t, ‖connected (abInf t) (aInf t) (bInf t)‖ ≤ C * Real.exp (-(alpha * t)) := by
  set S := wilsonPairSchedule size beta chi hchi hM x y p q with hS
  obtain ⟨φ, hφ, L, hconv, -, -, -, -⟩ := exists_limit_functional S
  refine ⟨φ, hφ, fun t => L (Sum.inl t), fun t => L (Sum.inr (Sum.inl t)),
    fun t => L (Sum.inr (Sum.inr t)), fun t => hconv (Sum.inl t),
    fun t => hconv (Sum.inr (Sum.inl t)), fun t => hconv (Sum.inr (Sum.inr t)), ?_⟩
  intro t
  have hlim : Tendsto (fun k => connected (S.expect (φ k) (Sum.inl t))
      (S.expect (φ k) (Sum.inr (Sum.inl t))) (S.expect (φ k) (Sum.inr (Sum.inr t))))
      atTop (𝓝 (connected (L (Sum.inl t)) (L (Sum.inr (Sum.inl t)))
        (L (Sum.inr (Sum.inr t))))) :=
    tendsto_connected (hconv (Sum.inl t)) (hconv (Sum.inr (Sum.inl t)))
      (hconv (Sum.inr (Sum.inr t)))
  refine norm_le_of_tendsto_of_eventually_le hlim ?_
  filter_upwards [hφ.tendsto_atTop.eventually (hcluster t)] with k hk
  rw [hS, connected_expect_pair_eq_loopCov]
  exact hk

end RequestProject.YangMills.Continuum

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Continuum

#print axioms exists_subseq_wilson_continuum_clustering_eventually

end Audit
