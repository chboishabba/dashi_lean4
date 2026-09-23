/-
# A literal inhabitant of the reflection-positive limit theorem

`Continuum/ReflectionPositiveLimit.lean` proves OS2 for the subsequential
continuum limit of the literal Wilson theory, for every `ReflectionSchedule`.
This file shows the statement is not empty: it builds a schedule out of a
**literal spatial plaquette Wilson loop sitting on the reflection plane**, for
an arbitrary compact gauge group and an arbitrary continuous, conjugation
invariant, inversion symmetric, bounded class function.

* `tval_add_spatial` — a spatial shift does not change the Euclidean time
  coordinate of a site;
* `loopObs_plaquette_local` — a spatial plaquette based at a site of time zero
  uses only links of the reflection plane, hence is a legitimate half-space
  observable;
* `plaquetteReflectionSchedule` — the resulting schedule on the lattices of
  even time extent `2(k+1)`;
* `exists_plaquette_reflection_positive_limit` — the instantiated theorem: along
  a subsequence of cutoffs the reflected self-pairing of the literal spatial
  plaquette converges, and its limit has nonnegative real part.
-/
import Mathlib
import RequestProject.YangMills.Continuum.ReflectionPositiveLimit
import RequestProject.YangMills.RouteS.UniformBounds

namespace RequestProject.YangMills.Continuum

open Filter Topology MeasureTheory
open RequestProject.YangMills.Lattice
open RequestProject.YangMills.OS
open RequestProject.YangMills.RouteS
open scoped ComplexConjugate

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]

variable {n : ℕ}

/-- A spatial shift does not change the Euclidean time coordinate. -/
theorem tval_add_spatial (x : Site n) {d : Fin 4} (hd : d ≠ 0) :
    tval (x + unitVec n d) = tval x := by
  have h : (unitVec n d) 0 = 0 := by simp [unitVec_apply, Ne.symm hd]
  simp [tval, h]

/-- The origin sits on the reflection plane `t = 0`. -/
@[simp] theorem tval_zero : tval (0 : Site n) = 0 := by simp [tval]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
/-- **A spatial plaquette on the time-zero plane is a half-space observable.**
Its four links are spatial links at time `0`, hence plane links, so the
observable only depends on the links of the closed positive half. -/
theorem loopObs_plaquette_local {L : ℕ} {chi : G → ℝ} {x : Site n} (hx : tval x = 0)
    {mu nu : Fin 4} (hmu : mu ≠ 0) (hnu : nu ≠ 0) (U V : Conf n G)
    (h : ∀ l : Link n, l ∈ planeLinks n L ∨ l ∈ posLinks n L → U l = V l) :
    loopObs chi x (plaquettePath mu nu) U = loopObs chi x (plaquettePath mu nu) V := by
  have hplane : ∀ (z : Site n) (d : Fin 4), d ≠ 0 → tval z = 0 → U (z, d) = V (z, d) := by
    intro z d hd hz
    exact h (z, d) (Or.inl (mem_planeLinks.2 ⟨hd, Or.inl hz⟩))
  have h1 : U (x, mu) = V (x, mu) := hplane x mu hmu hx
  have h2 : U (x + unitVec n mu, nu) = V (x + unitVec n mu, nu) :=
    hplane _ nu hnu (by rw [tval_add_spatial x hmu, hx])
  have h3 : U (x + unitVec n nu, mu) = V (x + unitVec n nu, mu) :=
    hplane _ mu hmu (by rw [tval_add_spatial x hnu, hx])
  have h4 : U (x, nu) = V (x, nu) := hplane x nu hnu hx
  simp only [loopObs, wilsonLoop, pathHol_plaquettePath, plaqHol, h1, h2, h3, h4]

/-- The reflection schedule of the literal spatial plaquette on the time-zero
plane, over the lattices of even time extent `2(k+1)`. -/
noncomputable def plaquetteReflectionSchedule (chi : G → ℝ) (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (hinv : ∀ g : G, chi g⁻¹ = chi g)
    {M : ℝ} (hM : ∀ g : G, |chi g| ≤ M) (beta : ℕ → ℝ) : ReflectionSchedule 1 G where
  size := fun k => 2 * (k + 1) - 1
  half := fun k => k + 1
  even_extent := fun k => by omega
  beta := beta
  chi := chi
  continuous_chi := hchi
  conj_chi := hconj
  inv_chi := hinv
  F := fun k _ => loopObs chi 0 (plaquettePath 1 2)
  bound := M
  measurable_F := fun _ _ => (continuous_loopObs hchi _ _).measurable
  norm_F_le := fun _ _ U => norm_loopObs_le hM _ _ U
  local_F := fun k _ U V h =>
    loopObs_plaquette_local (L := k + 1) tval_zero (by decide) (by decide) U V h

/-- **The reflection-positive limit theorem is inhabited by a literal Wilson
observable.**  For every compact gauge group and every continuous, conjugation
invariant, inversion symmetric, bounded class function, there is a subsequence
of the lattices of even time extent along which the reflected self-pairing of
the literal spatial plaquette on the reflection plane converges, and the limit
has nonnegative real part. -/
theorem exists_plaquette_reflection_positive_limit (chi : G → ℝ) (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (hinv : ∀ g : G, chi g⁻¹ = chi g)
    {M : ℝ} (hM : ∀ g : G, |chi g| ≤ M) (beta : ℕ → ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Lim : ℂ,
      Tendsto (fun k =>
        (plaquetteReflectionSchedule chi hchi hconj hinv hM beta).pairing (φ k) 0 0)
        atTop (𝓝 Lim) ∧ 0 ≤ Lim.re := by
  obtain ⟨φ, hφ, L, hconv, -, hpos⟩ :=
    exists_reflection_positive_limit (plaquetteReflectionSchedule chi hchi hconj hinv hM beta)
  refine ⟨φ, hφ, L 0 0, hconv 0 0, ?_⟩
  have := hpos (fun _ => 1)
  simpa using this

end RequestProject.YangMills.Continuum

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Continuum

#print axioms loopObs_plaquette_local
#print axioms exists_plaquette_reflection_positive_limit

end Audit
