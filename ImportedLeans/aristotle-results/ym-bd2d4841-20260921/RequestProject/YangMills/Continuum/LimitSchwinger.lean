/-
# The continuum limit of the Wilson Schwinger functions is Euclidean invariant

`Continuum/LimitEuclidean.lean` treats one Wilson loop at a time.  The Schwinger
functions of the theory are the expectations of *products* of Wilson loops, and
Euclidean invariance for them means moving **all** the loops of a family by the
*same* lattice Euclidean transformation.  That is what this file provides.

`Lattice/SchwingerBounds.lean` proves, for the literal Wilson–Gibbs measure at
every cutoff,

* the cutoff-uniform bound `‖S‖ ≤ M ^ m` on the `m`-loop Schwinger function,
* invariance of `S` under any composition of translations, axis permutations and
  hyperplane reflections applied to the whole family (`moveSite`, `movePath`).

Extracting one subsequence of cutoffs by the compactness argument of
`Continuum/LimitState.lean` gives

* `exists_wilson_limit_schwinger_euclidean_invariant` — along one subsequence
  every selected `m`-loop Wilson Schwinger function converges, the limits obey
  the same bound `M ^ m`, and two selected families that are related by a
  lattice Euclidean transformation at every cutoff have the *same* limit.

As in `Continuum/LimitState.lean`, this is a statement about the limit
expectation functional on the Wilson sector: no continuum measure, no
uniqueness of the subsequence, no nontriviality is claimed.
-/
import Mathlib
import RequestProject.YangMills.Continuum.LimitEuclidean
import RequestProject.YangMills.Lattice.SchwingerBounds

namespace RequestProject.YangMills.Continuum

open Filter Topology MeasureTheory
open RequestProject.YangMills.Lattice
open RequestProject.YangMills.RouteS

variable {ι : Type*}
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]

/-- **Euclidean invariance of the continuum limit of the Wilson Schwinger
functions.**  Along one subsequence of cutoffs every selected `m`-loop Wilson
Schwinger function converges, with limits bounded by `M ^ m`; and if two
selected families of loops are carried one to the other by a lattice Euclidean
transformation at every cutoff, their limits agree. -/
theorem exists_wilson_limit_schwinger_euclidean_invariant [Countable ι] (m : ℕ)
    (size : ℕ → ℕ) (beta : ℕ → ℝ) (chi : G → ℝ) (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) {M : ℝ} (hM : ∀ g : G, |chi g| ≤ M)
    (site : (k : ℕ) → ι → Fin m → Site (size k)) (path : ℕ → ι → Fin m → List Step) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L : ι → ℂ, (∀ j, ‖L j‖ ≤ M ^ m) ∧
      (∀ j, Tendsto
        (fun k => ∫ U, (∏ i, loopObs chi (site (φ k) j i) (path (φ k) j i) U)
          ∂(gibbs (size (φ k)) G (beta (φ k)) chi)) atTop (𝓝 (L j))) ∧
      (∀ a b : ι,
        (∀ k, ∃ gs : List (LatticeMove (size k)),
          (∀ i, site k b i = moveSite gs (site k a i)) ∧
          (∀ i, path k b i = movePath gs (path k a i))) →
        L a = L b) := by
  set E : ℕ → ι → ℂ := fun k j =>
    ∫ U, (∏ i, loopObs chi (site k j i) (path k j i) U)
      ∂(gibbs (size k) G (beta k) chi) with hE
  have hbound : ∀ k j, ‖E k j‖ ≤ M ^ m := fun k j =>
    norm_integral_prod_loopObs_le hchi hM (beta k) (site k j) (path k j)
  obtain ⟨φ, hφ, L, hL, hconv⟩ := exists_subseq_tendsto_family E hbound
  refine ⟨φ, hφ, L, hL, hconv, ?_⟩
  intro a b hrel
  refine limit_eq_of_forall_eq_seq (hconv a) (hconv b) fun k => ?_
  obtain ⟨gs, hsite, hpath⟩ := hrel (φ k)
  have hEb : E (φ k) b
      = ∫ U, (∏ i, loopObs chi (moveSite gs (site (φ k) a i)) (movePath gs (path (φ k) a i)) U)
          ∂(gibbs (size (φ k)) G (beta (φ k)) chi) := by
    simp only [hE]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    exact Finset.prod_congr rfl fun i _ => by rw [hsite i, hpath i]
  rw [hEb]
  exact (integral_prod_loopObs_moves hchi hconj (beta (φ k)) gs (site (φ k) a)
    (path (φ k) a)).symm

end RequestProject.YangMills.Continuum

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Continuum

#print axioms exists_wilson_limit_schwinger_euclidean_invariant

end Audit
