/-
# Euclidean invariance of the continuum limit functional (OS1, translations)

The literal Wilson–Gibbs measure is invariant under the lattice translations
(`Lattice/Wilson.lean`), so the expectation of a Wilson loop does not depend on
the base point of the loop.  This file proves that and pushes it through the
subsequential continuum limit of `Continuum/LimitState.lean`:

* `integral_comp_translate` — invariance of the literal Wilson–Gibbs integral
  under a lattice translation of the configuration;
* `integral_loopObs_translate` — hence the literal Wilson expectation depends
  only on the *shape* of the loop, not on its base point, at every cutoff;
* `exists_wilson_limit_translation_invariant` — the limit functional of the
  literal Wilson loops is translation invariant: two selected loops of the same
  shape have the same limit, however their base points are chosen at each
  cutoff.

This is the translation half of OS1 for the limit functional, proved rather than
assumed.  The rotation/reflection half of the Euclidean group is not addressed
here.
-/
import Mathlib
import RequestProject.YangMills.Continuum.WilsonLimit

namespace RequestProject.YangMills.Continuum

open Filter Topology MeasureTheory
open RequestProject.YangMills.Lattice
open RequestProject.YangMills.RouteS
open scoped ComplexConjugate

variable {ι : Type*}
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]
variable {n : ℕ}

/-- **Translation invariance of the literal Wilson–Gibbs integral.** -/
theorem integral_comp_translate {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ)
    (v : Site n) {A : Conf n G → ℂ} (hA : AEStronglyMeasurable A (gibbs n G beta chi)) :
    ∫ U, A (translate v U) ∂(gibbs n G beta chi) = ∫ U, A U ∂(gibbs n G beta chi) := by
  have hmp := measurePreserving_translate_gibbs (n := n) (G := G) hchi beta v
  have hmap : Measure.map (translate (n := n) (G := G) v) (gibbs n G beta chi)
      = gibbs n G beta chi := hmp.map_eq
  have h := integral_map (μ := gibbs n G beta chi) (φ := translate (n := n) (G := G) v)
    (f := A) (measurable_translateConf v).aemeasurable (by rwa [hmap])
  rw [hmap] at h
  exact h.symm

/-- **The literal Wilson expectation depends only on the shape of the loop.**
Moving the base point of the loop does not change its Wilson–Gibbs
expectation. -/
theorem integral_loopObs_translate {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ)
    (x v : Site n) (p : List Step) :
    ∫ U, loopObs chi (x + v) p U ∂(gibbs n G beta chi)
      = ∫ U, loopObs chi x p U ∂(gibbs n G beta chi) := by
  have h : (fun U : Conf n G => loopObs chi x p (translate v U)) = loopObs chi (x + v) p := by
    funext U
    simp [loopObs, wilsonLoop_translate]
  rw [← h]
  exact integral_comp_translate hchi beta v
    (continuous_loopObs hchi x p).measurable.aestronglyMeasurable

/-- Two literal Wilson loops of the same shape have the same expectation at
every cutoff, whatever their base points. -/
theorem integral_loopObs_congr_shape {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ)
    (x y : Site n) (p : List Step) :
    ∫ U, loopObs chi x p U ∂(gibbs n G beta chi)
      = ∫ U, loopObs chi y p U ∂(gibbs n G beta chi) := by
  have hxy : y = x + (y - x) := by abel
  rw [hxy, integral_loopObs_translate hchi beta x (y - x) p]

/-- The trivial loop has expectation `chi 1` at every cutoff: the state is
normalised on the unit observable. -/
theorem integral_loopObs_nil {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ) (x : Site n) :
    ∫ U, loopObs chi x [] U ∂(gibbs n G beta chi) = (chi 1 : ℂ) := by
  haveI := isProbabilityMeasure_gibbs (n := n) (G := G) hchi beta
  simp [loopObs, wilsonLoop]

/-- Two sequences that agree term by term have the same limit. -/
theorem limit_eq_of_forall_eq_seq {f g : ℕ → ℂ} {Lf Lg : ℂ} (hf : Tendsto f atTop (𝓝 Lf))
    (hg : Tendsto g atTop (𝓝 Lg)) (h : ∀ k, f k = g k) : Lf = Lg := by
  refine tendsto_nhds_unique hf ?_
  rw [show f = g from funext h]
  exact hg

/-- **Translation invariance of the continuum limit functional.**  Along a
subsequence of cutoffs all the selected literal Wilson expectations converge,
and loops of the same shape — however their base points are chosen at each
cutoff — have the same limit. -/
theorem exists_wilson_limit_translation_invariant [Countable ι] (size : ℕ → ℕ) (beta : ℕ → ℝ)
    (chi : G → ℝ) (hchi : Continuous chi) {M : ℝ} (hM : ∀ g : G, |chi g| ≤ M)
    (site : (k : ℕ) → ι → Site (size k)) (path : ℕ → ι → List Step) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L : ι → ℂ, (∀ j, ‖L j‖ ≤ M) ∧
      (∀ j, Tendsto
        (fun k => ∫ U, loopObs chi (site (φ k) j) (path (φ k) j) U
          ∂(gibbs (size (φ k)) G (beta (φ k)) chi)) atTop (𝓝 (L j))) ∧
      (∀ i j : ι, (∀ k, path k i = path k j) → L i = L j) := by
  obtain ⟨φ, hφ, L, hbd, hconv⟩ :=
    exists_wilson_limit_functional size beta chi hchi hM site path
  refine ⟨φ, hφ, L, hbd, hconv, ?_⟩
  intro i j hshape
  refine limit_eq_of_forall_eq_seq (hconv i) (hconv j) fun k => ?_
  rw [hshape (φ k)]
  exact integral_loopObs_congr_shape hchi (beta (φ k)) _ _ _

end RequestProject.YangMills.Continuum

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Continuum

#print axioms integral_loopObs_translate
#print axioms exists_wilson_limit_translation_invariant

end Audit
