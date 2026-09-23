/-
# A literal inhabitant of the same-object limit package

`Continuum/LimitPackage.lean` proves the same-object statement for every
`WilsonLimitSchedule`.  This file exhibits one, built entirely from literal
objects: the lattices of even time extent `2(k+1)`, an arbitrary countable
family of literal Wilson loops, and the literal spatial plaquette on the
reflection plane as the half-space observable of
`Continuum/ReflectionWitness.lean`.

`exists_wilson_limit_package_plaquette` is the resulting unconditional
statement: for every compact gauge group, every continuous, conjugation
invariant, inversion symmetric, bounded class function, every sequence of
inverse couplings and every countable family of literal Wilson loops, one
subsequence of cutoffs carries a limit functional that is translation
invariant, reflection positive, and to which any cutoff-uniform clustering
estimate transfers.
-/
import Mathlib
import RequestProject.YangMills.Continuum.LimitPackage
import RequestProject.YangMills.Continuum.ReflectionWitness

namespace RequestProject.YangMills.Continuum

open Filter Topology MeasureTheory
open RequestProject.YangMills.Lattice
open RequestProject.YangMills.OS
open RequestProject.YangMills.RouteS
open scoped ComplexConjugate

variable {ι : Type*}
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]

/-- The literal same-object schedule: the lattices of even time extent
`2(k+1)`, a countable family of literal Wilson loops, and the literal spatial
plaquette on the reflection plane as the half-space observable. -/
noncomputable def plaquetteWilsonLimitSchedule (chi : G → ℝ) (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (hinv : ∀ g : G, chi g⁻¹ = chi g)
    {M : ℝ} (hM : ∀ g : G, |chi g| ≤ M) (beta : ℕ → ℝ)
    (site : (k : ℕ) → ι → Site (2 * (k + 1) - 1)) (path : ℕ → ι → List Step) :
    WilsonLimitSchedule ι 1 G where
  size := fun k => 2 * (k + 1) - 1
  half := fun k => k + 1
  even_extent := fun k => by omega
  beta := beta
  chi := chi
  continuous_chi := hchi
  conj_chi := hconj
  inv_chi := hinv
  chiBound := M
  norm_chi_le := hM
  site := site
  path := path
  F := fun _ _ => loopObs chi 0 (plaquettePath 1 2)
  fBound := M
  measurable_F := fun _ _ => (continuous_loopObs hchi _ _).measurable
  norm_F_le := fun _ _ U => norm_loopObs_le hM _ _ U
  local_F := fun k _ U V h =>
    loopObs_plaquette_local (L := k + 1) tval_zero (by decide) (by decide) U V h

/-- **The same-object limit package is inhabited by literal Wilson objects.** -/
theorem exists_wilson_limit_package_plaquette [Countable ι] (chi : G → ℝ)
    (hchi : Continuous chi) (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g)
    (hinv : ∀ g : G, chi g⁻¹ = chi g) {M : ℝ} (hM : ∀ g : G, |chi g| ≤ M) (beta : ℕ → ℝ)
    (site : (k : ℕ) → ι → Site (2 * (k + 1) - 1)) (path : ℕ → ι → List Step) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ (Lloop : ι → ℂ) (Lprod : ι → ι → ℂ) (Lrefl : Fin 1 → Fin 1 → ℂ),
        (∀ j, Tendsto (fun k =>
          (plaquetteWilsonLimitSchedule chi hchi hconj hinv hM beta site path).loopExpect
            (φ k) j) atTop (𝓝 (Lloop j))) ∧
        (∀ i j, Tendsto (fun k =>
          (plaquetteWilsonLimitSchedule chi hchi hconj hinv hM beta site path).prodExpect
            (φ k) i j) atTop (𝓝 (Lprod i j))) ∧
        (∀ r s, Tendsto (fun k =>
          (plaquetteWilsonLimitSchedule chi hchi hconj hinv hM beta site path).reflPairing
            (φ k) r s) atTop (𝓝 (Lrefl r s))) ∧
        (∀ j, ‖Lloop j‖ ≤ M) ∧
        (∀ i j : ι, (∀ k, path k i = path k j) → Lloop i = Lloop j) ∧
        (∀ j : ι, (∀ k, path k j = []) → Lloop j = (chi 1 : ℂ)) ∧
        (∀ c : Fin 1 → ℂ, 0 ≤ (∑ r, ∑ s, conj (c r) * c s * Lrefl r s).re) ∧
        (∀ (C alpha : ℝ) (a b : ℕ → ι),
          (∀ k t : ℕ, ‖connected
              ((plaquetteWilsonLimitSchedule chi hchi hconj hinv hM beta site path).prodExpect
                k (a t) (b t))
              ((plaquetteWilsonLimitSchedule chi hchi hconj hinv hM beta site path).loopExpect
                k (a t))
              ((plaquetteWilsonLimitSchedule chi hchi hconj hinv hM beta site path).loopExpect
                k (b t))‖ ≤ C * Real.exp (-(alpha * t))) →
          ∀ t : ℕ, ‖connected (Lprod (a t) (b t)) (Lloop (a t)) (Lloop (b t))‖
            ≤ C * Real.exp (-(alpha * t))) :=
  exists_wilson_limit_package (plaquetteWilsonLimitSchedule chi hchi hconj hinv hM beta site path)

end RequestProject.YangMills.Continuum

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Continuum

#print axioms exists_wilson_limit_package_plaquette

end Audit
