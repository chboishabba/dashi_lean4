/-
# Full Euclidean invariance of the continuum limit functional (OS1)

`Continuum/LimitSymmetries.lean` proves the *translation* half of OS1 for the
subsequential Wilson limit functional and states explicitly that the
rotation/reflection half is not addressed there.  This file supplies it.

`Lattice/HypercubicLoop.lean` proves that the literal Wilson expectation of a
based loop is unchanged by every generator of the Euclidean group of the
periodic lattice — translations, permutations of the coordinate axes and
reflections in coordinate hyperplanes — and hence by every composition of them
(`integral_loopObs_euclidean`, on the inductively generated relation
`EuclideanRelated`).  Transporting that through the subsequential limit of
`Continuum/LimitState.lean` gives

* `exists_wilson_limit_euclidean_invariant` — along one subsequence of cutoffs
  all the selected literal Wilson expectations converge, and any two selected
  loops that are Euclidean related at every cutoff have the *same* limit.

This is OS1 for the limit functional on the literal Wilson sector, proved rather
than assumed.  It does not by itself provide the continuum measure: the limit is
still a subsequential limit of the expectation functional, exactly as in
`Continuum/LimitState.lean`.
-/
import Mathlib
import RequestProject.YangMills.Continuum.LimitSymmetries
import RequestProject.YangMills.Lattice.HypercubicLoop

namespace RequestProject.YangMills.Continuum

open Filter Topology MeasureTheory
open RequestProject.YangMills.Lattice
open RequestProject.YangMills.RouteS

variable {ι : Type*}
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]

/-- **Euclidean invariance of the continuum limit functional.**  Along a
subsequence of cutoffs all the selected literal Wilson expectations converge,
and two selected loops that are related by a lattice Euclidean transformation at
every cutoff have the same limit. -/
theorem exists_wilson_limit_euclidean_invariant [Countable ι] (size : ℕ → ℕ) (beta : ℕ → ℝ)
    (chi : G → ℝ) (hchi : Continuous chi) (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g)
    {M : ℝ} (hM : ∀ g : G, |chi g| ≤ M)
    (site : (k : ℕ) → ι → Site (size k)) (path : ℕ → ι → List Step) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L : ι → ℂ, (∀ j, ‖L j‖ ≤ M) ∧
      (∀ j, Tendsto
        (fun k => ∫ U, loopObs chi (site (φ k) j) (path (φ k) j) U
          ∂(gibbs (size (φ k)) G (beta (φ k)) chi)) atTop (𝓝 (L j))) ∧
      (∀ i j : ι,
        (∀ k, EuclideanRelated (size k) (site k i, path k i) (site k j, path k j)) →
        L i = L j) := by
  obtain ⟨φ, hφ, L, hbd, hconv⟩ :=
    exists_wilson_limit_functional size beta chi hchi hM site path
  refine ⟨φ, hφ, L, hbd, hconv, ?_⟩
  intro i j hrel
  refine limit_eq_of_forall_eq_seq (hconv i) (hconv j) fun k => ?_
  exact (integral_loopObs_euclidean hchi hconj (beta (φ k)) (hrel (φ k))).symm

end RequestProject.YangMills.Continuum

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Continuum

#print axioms exists_wilson_limit_euclidean_invariant

end Audit
