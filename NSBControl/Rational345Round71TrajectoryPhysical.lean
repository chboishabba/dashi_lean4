import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import NSBControl.Rational345RealRadius4Quadratic
import NSBControl.Rational345Round71RealityField
import NSBControl.Rational345Round71InitialPhysical
import NSBControl.Rational345Round71TransverseField

/-!
# Round71 physical invariants along the local real trajectory

The radius-four Galerkin field is globally equivariant under Fourier reality.
Since the field is C¹, Mathlib supplies a local Lipschitz neighborhood and ODE
uniqueness.  Therefore any local solution through the reality-fixed 3-4-5
initial state remains reality-fixed on a positive time neighborhood.

The divergence vector of all 729 modes is treated at once.  Its exact field
identity is the diagonal linear system

  D(Q(u))_k = -|k|² D(u)_k.

The initial divergence vector is zero, so finite-dimensional ODE uniqueness
forces it to remain zero on a positive neighborhood as well.
-/

open Set

namespace NSBControl
namespace Rational345Round71TrajectoryPhysical

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345RealRadius4Quadratic
open Rational345Round71RealityField
open Rational345Round71InitialPhysical
open Rational345Round71TransverseField

/-- The Fourier reality involution is real-linear on the ambient state space. -/
noncomputable def realityLinearMap : State →ₗ[ℝ] State where
  toFun := realityTransform
  map_add' := by
    intro u v
    funext k j
    simp [realityTransform, vecConj]
  map_smul' := by
    intro c u
    funext k j
    simp [realityTransform, vecConj]

/-- Finite dimensionality upgrades the reality involution to a continuous real
linear map. -/
noncomputable def realityCLM : State →L[ℝ] State :=
  ⟨realityLinearMap,
    LinearMap.continuous_of_finiteDimensional realityLinearMap⟩

@[simp] theorem realityCLM_apply (u : State) :
    realityCLM u = realityTransform u := rfl

/-- Applying Fourier reality to a Galerkin solution produces another solution
of the same ODE. -/
theorem reality_curve_hasDerivAt
    (u : ℝ → State) {ε t : ℝ}
    (hderiv : ∀ s ∈ Ioo (-ε) ε,
      HasDerivAt u (galerkinField (u s)) s)
    (ht : t ∈ Ioo (-ε) ε) :
    HasDerivAt
      (fun s => realityTransform (u s))
      (galerkinField (realityTransform (u t))) t := by
  have hcomp :=
    realityCLM.hasFDerivAt.comp_hasDerivAt t (hderiv t ht)
  rw [← galerkinField_reality_equivariant]
  simpa [Function.comp_def] using hcomp

/-- A local solution through the 3-4-5 datum is Fourier-real on a positive
neighborhood of time zero. -/
theorem trajectory_reality_radius
    (u : ℝ → State) {ε : ℝ}
    (hε : 0 < ε)
    (hu0 : u 0 = u₀)
    (hderiv : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt u (galerkinField (u t)) t) :
    ∃ ρ > 0, ∀ t : ℝ, |t| < ρ → realityTransform (u t) = u t := by
  obtain ⟨K, s, hs, hlip⟩ :=
    galerkinField_contDiff_real.contDiffAt.exists_lipschitzOnWith

  have hzeroI : (0 : ℝ) ∈ Ioo (-ε) ε := by
    constructor <;> linarith
  have huCont : ContinuousAt u 0 := (hderiv 0 hzeroI).continuousAt

  have hs0 : s ∈ 𝓝 (u 0) := by simpa [hu0] using hs
  have huMem : ∀ᶠ t in 𝓝 (0 : ℝ), u t ∈ s := huCont hs0

  have hI : Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith) (by linarith)

  let ru : ℝ → State := fun t => realityTransform (u t)

  have hru0 : ru 0 = u₀ := by
    simp [ru, hu0, initial_reality]

  have hruDeriv0 :
      HasDerivAt ru (galerkinField (ru 0)) 0 := by
    simpa [ru] using reality_curve_hasDerivAt u hderiv hzeroI
  have hruCont : ContinuousAt ru 0 := hruDeriv0.continuousAt
  have hrs0 : s ∈ 𝓝 (ru 0) := by simpa [hru0] using hs
  have hruMem : ∀ᶠ t in 𝓝 (0 : ℝ), ru t ∈ s := hruCont hrs0

  have hv :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        LipschitzOnWith K ((fun _ : ℝ => galerkinField) t)
          ((fun _ : ℝ => s) t) :=
    Filter.Eventually.of_forall (fun _ => hlip)

  have huSol :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        HasDerivAt u (galerkinField (u t)) t ∧ u t ∈ s := by
    filter_upwards [Filter.Eventually.of_mem hI, huMem] with t htI hts
    exact ⟨hderiv t htI, hts⟩

  have hruSol :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        HasDerivAt ru (galerkinField (ru t)) t ∧ ru t ∈ s := by
    filter_upwards [Filter.Eventually.of_mem hI, hruMem] with t htI hts
    exact ⟨by simpa [ru] using reality_curve_hasDerivAt u hderiv htI, hts⟩

  have hevent : u =ᶠ[𝓝 (0 : ℝ)] ru :=
    ODE_solution_unique_of_eventually
      (v := fun _ : ℝ => galerkinField)
      (s := fun _ : ℝ => s)
      hv huSol hruSol (by simp [ru, hu0, initial_reality])

  have hevent' : ∀ᶠ t in 𝓝 (0 : ℝ), realityTransform (u t) = u t :=
    hevent.mono (fun t ht => by simpa [ru] using ht.symm)

  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hevent'
  refine ⟨ρ, hρ, ?_⟩
  intro t ht
  apply hball t
  simpa [Real.dist_eq] using ht

------------------------------------------------------------------------
-- All-mode divergence vector and its exact diagonal ODE.
------------------------------------------------------------------------

abbrev DivergenceState := Mode → ℂ

def divergenceState (u : State) : DivergenceState := fun k =>
  bilinearDot (kComplex k) (u k)

def divergenceDecay (d : DivergenceState) : DivergenceState := fun k =>
  -(normSq k : ℂ) * d k

noncomputable def divergenceLinearMap : State →ₗ[ℝ] DivergenceState where
  toFun := divergenceState
  map_add' := by
    intro u v
    funext k
    simp [divergenceState, bilinearDot]
    ring
  map_smul' := by
    intro c u
    funext k
    simp [divergenceState, bilinearDot]
    ring

noncomputable def divergenceCLM : State →L[ℝ] DivergenceState :=
  ⟨divergenceLinearMap,
    LinearMap.continuous_of_finiteDimensional divergenceLinearMap⟩

noncomputable def divergenceDecayLinearMap :
    DivergenceState →ₗ[ℝ] DivergenceState where
  toFun := divergenceDecay
  map_add' := by
    intro d e
    funext k
    simp [divergenceDecay]
    ring
  map_smul' := by
    intro c d
    funext k
    simp [divergenceDecay]
    ring

noncomputable def divergenceDecayCLM :
    DivergenceState →L[ℝ] DivergenceState :=
  ⟨divergenceDecayLinearMap,
    LinearMap.continuous_of_finiteDimensional divergenceDecayLinearMap⟩

@[simp] theorem divergenceCLM_apply (u : State) :
    divergenceCLM u = divergenceState u := rfl

@[simp] theorem divergenceDecayCLM_apply (d : DivergenceState) :
    divergenceDecayCLM d = divergenceDecay d := rfl

/-- The full 729-component divergence vector intertwines the literal Galerkin
field with one fixed diagonal linear vector field. -/
theorem divergenceState_field (u : State) :
    divergenceState (galerkinField u) =
      divergenceDecay (divergenceState u) := by
  funext k
  exact divergence_field_identity u k

/-- Initial divergence is identically zero. -/
theorem divergenceState_u₀_zero : divergenceState u₀ = 0 := by
  funext k
  exact initial_transverse k

/-- Composing a Galerkin solution with the all-mode divergence map gives a
solution of the fixed diagonal divergence ODE. -/
theorem divergence_curve_hasDerivAt
    (u : ℝ → State) {ε t : ℝ}
    (hderiv : ∀ s ∈ Ioo (-ε) ε,
      HasDerivAt u (galerkinField (u s)) s)
    (ht : t ∈ Ioo (-ε) ε) :
    HasDerivAt
      (fun s => divergenceState (u s))
      (divergenceDecay (divergenceState (u t))) t := by
  have hcomp :=
    divergenceCLM.hasFDerivAt.comp_hasDerivAt t (hderiv t ht)
  rw [divergenceState_field]
  simpa [Function.comp_def] using hcomp

/-- The zero divergence curve solves the diagonal divergence ODE globally. -/
theorem zero_divergence_curve_hasDerivAt (t : ℝ) :
    HasDerivAt
      (fun _ : ℝ => (0 : DivergenceState))
      (divergenceDecay 0) t := by
  simpa [divergenceDecay] using
    (hasDerivAt_const t (0 : DivergenceState))

/-- A local solution through the transverse 3-4-5 datum is divergence-free on
a positive neighborhood of time zero, simultaneously for every Fourier mode. -/
theorem trajectory_transverse_radius
    (u : ℝ → State) {ε : ℝ}
    (hε : 0 < ε)
    (hu0 : u 0 = u₀)
    (hderiv : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt u (galerkinField (u t)) t) :
    ∃ ρ > 0, ∀ t : ℝ, |t| < ρ →
      ∀ k : Mode, bilinearDot (kComplex k) (u t k) = 0 := by
  let d : ℝ → DivergenceState := fun t => divergenceState (u t)
  let z : ℝ → DivergenceState := fun _ => 0
  let K : ℝ≥0 := ‖divergenceDecayCLM‖₊

  have hI : Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith) (by linarith)

  have hv :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        LipschitzOnWith K ((fun _ : ℝ => divergenceDecay) t)
          ((fun _ : ℝ => (Set.univ : Set DivergenceState)) t) := by
    apply Filter.Eventually.of_forall
    intro t
    exact (divergenceDecayCLM.lipschitzWith).lipschitzOnWith

  have hdSol :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        HasDerivAt d (divergenceDecay (d t)) t ∧ d t ∈ Set.univ := by
    filter_upwards [Filter.Eventually.of_mem hI] with t htI
    exact ⟨by simpa [d] using divergence_curve_hasDerivAt u hderiv htI,
      Set.mem_univ _⟩

  have hzSol :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        HasDerivAt z (divergenceDecay (z t)) t ∧ z t ∈ Set.univ := by
    apply Filter.Eventually.of_forall
    intro t
    exact ⟨by simpa [z] using zero_divergence_curve_hasDerivAt t,
      Set.mem_univ _⟩

  have hinit : d 0 = z 0 := by
    simp [d, z, hu0, divergenceState_u₀_zero]

  have hevent : d =ᶠ[𝓝 (0 : ℝ)] z :=
    ODE_solution_unique_of_eventually
      (v := fun _ : ℝ => divergenceDecay)
      (s := fun _ : ℝ => (Set.univ : Set DivergenceState))
      hv hdSol hzSol hinit

  have hevent' : ∀ᶠ t in 𝓝 (0 : ℝ), divergenceState (u t) = 0 := by
    simpa [d, z] using hevent

  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hevent'
  refine ⟨ρ, hρ, ?_⟩
  intro t ht k
  have hzero : divergenceState (u t) = 0 := by
    apply hball t
    simpa [Real.dist_eq] using ht
  exact congrFun hzero k

/-- Reality along the local trajectory is an explicit positive-radius
consequence of the literal field symmetry and standard uniqueness. -/
def trajectoryRealityLocallyClosed : Bool := true

/-- Divergence freedom along the local trajectory is an explicit positive-
radius consequence of the exact diagonal divergence equation. -/
def trajectoryTransverseLocallyClosed : Bool := true

end Rational345Round71TrajectoryPhysical
end NSBControl
