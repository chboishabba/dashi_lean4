/-
# The vacuum vector and Wilson-loop states of the physical Hilbert space

`OS/WilsonOSHilbert.lean` constructs the Osterwalder–Schrader physical Hilbert
space `OSHilbert D` of the literal Wilson lattice gauge theory.  This file shows
that this Hilbert space is *not* a degenerate object:

* `oneObs` — the unit observable is an observable of the positive half, and its
  OS norm is `1` (`osForm_one_one`), because the Wilson–Gibbs measure is a
  probability measure;
* `osVacuum`, `norm_osVacuum`, `osVacuum_ne_zero`, `instNontrivialOSHilbert` —
  hence the physical Hilbert space carries a unit vector, the OS vacuum, and is
  nontrivial;
* `loopObs`, `osLoopState` — every literal Wilson loop whose links lie in the
  closed positive half `0 ≤ t ≤ L` defines a vector of the physical Hilbert
  space, whose OS inner products are the Wilson-loop correlators of the literal
  Wilson–Gibbs measure (`inner_osLoopState`).

Together with `OS/WilsonReflectionPositivity.lean` this is a complete, machine
checked Osterwalder–Schrader positivity and Hilbert-space reconstruction for the
literal four-dimensional Wilson theory at finite lattice cutoff.
-/
import Mathlib
import RequestProject.YangMills.OS.WilsonOSHilbert
import RequestProject.YangMills.OS.WilsonLoopPositivity

namespace RequestProject.YangMills.OS

open MeasureTheory Complex
open RequestProject.YangMills.Lattice

variable {n L : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

/-! ## The unit observable and the OS vacuum -/

variable (n L G) in
/-- The unit observable, trivially an observable of the closed positive half. -/
def oneObs : posObs n L G :=
  ⟨fun _ => 1, measurable_const, ⟨1, fun _ => by simp⟩, fun _ _ _ => rfl⟩

@[simp]
theorem oneObs_apply (U : Conf n G) : ((oneObs n L G : Conf n G → ℂ)) U = 1 := rfl

/-- The OS form of the unit observable with itself is `1`: the Wilson–Gibbs
measure is a probability measure and the reflection preserves it. -/
theorem osForm_one_one (D : OSData n L G) :
    osForm D.even_time D.beta D.chi (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) = 1 := by
  haveI := isProbabilityMeasure_gibbs (n := n) (G := G) D.chi_continuous D.beta
  simp [osForm]

/-- **The Osterwalder–Schrader vacuum** of the literal Wilson theory: the
physical vector of the unit observable. -/
noncomputable def osVacuum (D : OSData n L G) : OSHilbert D := osVector D (oneObs n L G)

/-- The vacuum is a unit vector for the OS inner product. -/
theorem inner_osVacuum_self (D : OSData n L G) :
    (inner ℂ (osVacuum D) (osVacuum D) : ℂ) = 1 := by
  rw [osVacuum, inner_osVector]
  exact osForm_one_one D

theorem norm_osVacuum (D : OSData n L G) : ‖osVacuum D‖ = 1 := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (osVacuum D)
  rw [inner_osVacuum_self] at h
  have h2 : ((‖osVacuum D‖ : ℂ)) ^ 2 = 1 := h.symm
  have h3 : (‖osVacuum D‖ : ℝ) ^ 2 = 1 := by exact_mod_cast h2
  nlinarith [norm_nonneg (osVacuum D)]

theorem osVacuum_ne_zero (D : OSData n L G) : osVacuum D ≠ 0 := by
  intro h
  have := norm_osVacuum D
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- **The physical Hilbert space of the literal Wilson theory is nontrivial.**
This rules out the degenerate reading in which the reconstruction produces the
zero Hilbert space. -/
instance instNontrivialOSHilbert (D : OSData n L G) : Nontrivial (OSHilbert D) :=
  ⟨⟨osVacuum D, 0, osVacuum_ne_zero D⟩⟩

/-! ## Wilson-loop states -/

/-- A literal Wilson loop supported in the closed positive half is an observable
of the positive half. -/
noncomputable def loopObs (D : OSData n L G) (x : Site n) (p : List Step)
    (hsupp : ∀ l ∈ pathLinks n x p, l ∈ planeLinks n L ∨ l ∈ posLinks n L) :
    posObs n L G := by
  refine ⟨fun U => ((wilsonLoop D.chi x p U : ℝ) : ℂ), ?_, ?_, ?_⟩
  · exact (Complex.continuous_ofReal.comp
      (continuous_wilsonLoop D.chi_continuous x p)).measurable
  · obtain ⟨U₀, -, hU₀⟩ :=
      (isCompact_univ (X := Conf n G)).exists_isMaxOn ⟨fun _ => 1, Set.mem_univ _⟩
        (Complex.continuous_ofReal.comp
          (continuous_wilsonLoop D.chi_continuous x p)).norm.continuousOn
    exact ⟨‖((wilsonLoop D.chi x p U₀ : ℝ) : ℂ)‖, fun U => hU₀ (Set.mem_univ U)⟩
  · intro U V hUV
    exact congrArg _ (wilsonLoop_local D.chi x p fun l hl => hUV l (hsupp l hl))

@[simp]
theorem loopObs_apply (D : OSData n L G) (x : Site n) (p : List Step)
    (hsupp : ∀ l ∈ pathLinks n x p, l ∈ planeLinks n L ∨ l ∈ posLinks n L) (U : Conf n G) :
    ((loopObs D x p hsupp : Conf n G → ℂ)) U = ((wilsonLoop D.chi x p U : ℝ) : ℂ) := rfl

/-- The physical state created from the vacuum by a literal Wilson loop of the
closed positive half. -/
noncomputable def osLoopState (D : OSData n L G) (x : Site n) (p : List Step)
    (hsupp : ∀ l ∈ pathLinks n x p, l ∈ planeLinks n L ∨ l ∈ posLinks n L) :
    OSHilbert D := osVector D (loopObs D x p hsupp)

/-- **The OS inner product of two Wilson-loop states is the reflected Wilson-loop
correlator of the literal Wilson–Gibbs measure.** -/
theorem inner_osLoopState (D : OSData n L G) (x y : Site n) (p q : List Step)
    (hp : ∀ l ∈ pathLinks n x p, l ∈ planeLinks n L ∨ l ∈ posLinks n L)
    (hq : ∀ l ∈ pathLinks n y q, l ∈ planeLinks n L ∨ l ∈ posLinks n L) :
    (inner ℂ (osLoopState D x p hp) (osLoopState D y q hq) : ℂ)
      = ∫ U, ((wilsonLoop D.chi x p (reflConf D.even_time U) : ℝ) : ℂ) *
          ((wilsonLoop D.chi y q U : ℝ) : ℂ) ∂(gibbs n G D.beta D.chi) := by
  rw [osLoopState, osLoopState, inner_osVector]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp

/-- The OS norm squared of a Wilson-loop state is the reflected self-correlator,
which is therefore nonnegative — reflection positivity for literal Wilson loops,
read off the Hilbert space. -/
theorem inner_osLoopState_self_re_nonneg (D : OSData n L G) (x : Site n) (p : List Step)
    (hp : ∀ l ∈ pathLinks n x p, l ∈ planeLinks n L ∨ l ∈ posLinks n L) :
    0 ≤ (∫ U, ((wilsonLoop D.chi x p (reflConf D.even_time U) : ℝ) : ℂ) *
        ((wilsonLoop D.chi x p U : ℝ) : ℂ) ∂(gibbs n G D.beta D.chi)).re := by
  rw [← inner_osLoopState D x x p p hp hp]
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
  simp [pow_two]
  positivity

end RequestProject.YangMills.OS

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.OS

#print axioms osForm_one_one
#print axioms norm_osVacuum
#print axioms instNontrivialOSHilbert
#print axioms inner_osLoopState

end Audit
