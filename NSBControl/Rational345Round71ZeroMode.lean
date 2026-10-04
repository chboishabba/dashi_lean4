import Mathlib.Analysis.ODE.ExistUnique
import NSBControl.Rational345RealRadius4Quadratic
import NSBControl.Rational345RealInitialState

/-!
# Round71 zero-mode invariant

The canonical Round71 physical carrier omits k=0.  On the ambient real
radius-four model the corresponding fact is an invariant: the literal
Galerkin field is identically zero at the unique zero mode, and the 3-4-5
initial datum has zero coefficient there.  Local ODE uniqueness therefore
keeps the zero mode zero on a positive neighborhood of t=0.
-/

open Set

namespace NSBControl
namespace Rational345Round71ZeroMode

open Rational345RealRadius4
open Rational345RealInitialState

/-- Unique centered radius-four zero wave number. -/
def zeroMode : Mode := ⟨4, 4, 4⟩

theorem zeroMode_is_zero : isZeroMode zeroMode := by
  intro j
  fin_cases j <;> norm_num [zeroMode, kInt, axisInt]

/-- The literal Galerkin vector field has no zero-mode evolution. -/
theorem galerkinField_zeroMode (u : State) :
    galerkinField u zeroMode = 0 := by
  simp [galerkinField, viscousLinear, projectedBilinear, zeroMode_is_zero]

/-- The selected 3-4-5 initial datum has zero mean. -/
theorem initial_zeroMode : u₀ zeroMode = 0 := by
  simp [u₀, zeroMode, k300, km300, k040, k0m40, k340, km3m40]

noncomputable def zeroModeEvalLinearMap : State →ₗ[ℝ] Vec3 where
  toFun := fun u => u zeroMode
  map_add' := by intro u v; rfl
  map_smul' := by intro c u; rfl

noncomputable def zeroModeEvalCLM : State →L[ℝ] Vec3 :=
  ⟨zeroModeEvalLinearMap,
    LinearMap.continuous_of_finiteDimensional zeroModeEvalLinearMap⟩

@[simp] theorem zeroModeEvalCLM_apply (u : State) :
    zeroModeEvalCLM u = u zeroMode := rfl

/-- Evaluation of a Galerkin solution at k=0 has zero derivative. -/
theorem zeroMode_curve_hasDerivAt
    (u : ℝ → State) {ε t : ℝ}
    (hderiv : ∀ s ∈ Ioo (-ε) ε,
      HasDerivAt u (galerkinField (u s)) s)
    (ht : t ∈ Ioo (-ε) ε) :
    HasDerivAt (fun s => u s zeroMode) 0 t := by
  have hcomp :=
    zeroModeEvalCLM.hasFDerivAt.comp_hasDerivAt t (hderiv t ht)
  rw [galerkinField_zeroMode] at hcomp
  simpa [Function.comp_def] using hcomp

/-- A local solution through the 3-4-5 datum keeps zero Fourier mean on a
positive neighborhood of t=0. -/
theorem trajectory_zeroMode_radius
    (u : ℝ → State) {ε : ℝ}
    (hε : 0 < ε)
    (hu0 : u 0 = u₀)
    (hderiv : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt u (galerkinField (u t)) t) :
    ∃ ρ > 0, ∀ t : ℝ, |t| < ρ → u t zeroMode = 0 := by
  let m : ℝ → Vec3 := fun t => u t zeroMode
  let z : ℝ → Vec3 := fun _ => 0
  let zeroCLM : Vec3 →L[ℝ] Vec3 := 0
  let K : ℝ≥0 := ‖zeroCLM‖₊

  have hI : Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith) (by linarith)

  have hv :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        LipschitzOnWith K ((fun _ : ℝ => fun _ : Vec3 => (0 : Vec3)) t)
          ((fun _ : ℝ => (Set.univ : Set Vec3)) t) := by
    apply Filter.Eventually.of_forall
    intro t
    have hz : LipschitzWith K (fun _ : Vec3 => (0 : Vec3)) := by
      simpa [K, zeroCLM] using (zeroCLM.lipschitzWith)
    exact hz.lipschitzOnWith

  have hmSol :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        HasDerivAt m 0 t ∧ m t ∈ Set.univ := by
    filter_upwards [Filter.Eventually.of_mem hI] with t htI
    exact ⟨by simpa [m] using zeroMode_curve_hasDerivAt u hderiv htI,
      Set.mem_univ _⟩

  have hzSol :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        HasDerivAt z 0 t ∧ z t ∈ Set.univ := by
    apply Filter.Eventually.of_forall
    intro t
    exact ⟨by simpa [z] using (hasDerivAt_const t (0 : Vec3)),
      Set.mem_univ _⟩

  have hinit : m 0 = z 0 := by
    simp [m, z, hu0, initial_zeroMode]

  have hevent : m =ᶠ[𝓝 (0 : ℝ)] z :=
    ODE_solution_unique_of_eventually
      (v := fun _ : ℝ => fun _ : Vec3 => (0 : Vec3))
      (s := fun _ : ℝ => (Set.univ : Set Vec3))
      hv hmSol hzSol hinit

  have hevent' : ∀ᶠ t in 𝓝 (0 : ℝ), u t zeroMode = 0 := by
    simpa [m, z] using hevent

  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hevent'
  refine ⟨ρ, hρ, ?_⟩
  intro t ht
  apply hball t
  simpa [Real.dist_eq] using ht

/-- Zero-mode exclusion is now a real trajectory invariant rather than a
hidden carrier assumption. -/
def trajectoryZeroModeLocallyClosed : Bool := true

end Rational345Round71ZeroMode
end NSBControl
