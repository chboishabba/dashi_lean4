import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import NSBControl.Rational345RealRadius4Quadratic
import NSBControl.Rational345Round71RealityField
import NSBControl.Rational345Round71InitialPhysical

/-!
# Round71 physical invariants along the local real trajectory

The radius-four Galerkin field is globally equivariant under Fourier reality.
Since the field is C¹, Mathlib supplies a local Lipschitz neighborhood and ODE
uniqueness.  Therefore any local solution through the reality-fixed 3-4-5
initial state remains reality-fixed on a positive time neighborhood.
-/

open Set

namespace NSBControl
namespace Rational345Round71TrajectoryPhysical

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345RealRadius4Quadratic
open Rational345Round71RealityField
open Rational345Round71InitialPhysical

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

/-- Reality along the local trajectory is now an explicit positive-radius
consequence of the literal field symmetry and standard uniqueness. -/
def trajectoryRealityLocallyClosed : Bool := true

end Rational345Round71TrajectoryPhysical
end NSBControl
