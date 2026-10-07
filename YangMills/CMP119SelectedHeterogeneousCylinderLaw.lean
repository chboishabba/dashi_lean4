import Mathlib
import YangMills.CMP119SelectedPhysicalCutoff
import YangMills.WilsonCylinderCompactification
import YangMills.WilsonDF2UnifiedSource

open MeasureTheory

/-!
# One common cylinder state for varying finite CMP119 cutoff carriers

The literal finite lattice carrier changes with the cutoff.  A continuum cutoff
family therefore should not pretend that every finite Gibbs law already lives
on one common raw configuration type.  What is common is the chosen countable
Wilson/cylinder coordinate system.

For cutoff `k`, map its actual selected Gibbs probability on
`SU2TorusLinks (2 * (k+1))` through its own measurable bounded coordinate map
into the single compact cube `[-1,1]^ℕ`.  All finite laws then literally share
one state space before any projective/weak-limit argument.

This removes a representation seam only.  The source-facing task remains to
supply the intended physical Wilson coordinates and prove they are the same
observables used by CMP119/OS reconstruction.
-/

namespace RequestProject.YangMills

/-- Common compact countable cylinder cube used by every cutoff. -/
abbrev HeterogeneousWilsonCylinderState := ℕ → WilsonUnitInterval

/-- Canonical continuous real coordinate on the common cube. -/
def heterogeneousWilsonCylinderCoordinate (i : ℕ) :
    C(HeterogeneousWilsonCylinderState, ℝ) where
  toFun := fun z => (z i).1
  continuous_toFun := by fun_prop

/-- The common cube coordinates separate points tautologically. -/
theorem heterogeneousWilsonCylinderCoordinateMap_injective :
    Function.Injective
      (fun z : HeterogeneousWilsonCylinderState =>
        fun i => heterogeneousWilsonCylinderCoordinate i z) := by
  intro x y hxy
  funext i
  apply Subtype.ext
  exact congrFun hxy i

/-- The common cylinder carrier has the merged D/F2 coordinate source by construction. -/
def heterogeneousWilsonCylinderDF2Source :
    CountableWilsonDF2Source HeterogeneousWilsonCylinderState where
  wilson := heterogeneousWilsonCylinderCoordinate
  coordinateMapInjective := heterogeneousWilsonCylinderCoordinateMap_injective

/-- Bounded coordinate map for one selected finite lattice cutoff. -/
def selectedCMP119CutoffTanhCubeMap
    (raw : ∀ k : ℕ, ℕ → SU2TorusLinks (2 * (k + 1)) → ℝ)
    (k : ℕ) :
    SU2TorusLinks (2 * (k + 1)) → HeterogeneousWilsonCylinderState :=
  fun links i =>
    ⟨Real.tanh (raw k i links), by
      constructor
      · exact le_of_lt (Real.neg_one_lt_tanh (raw k i links))
      · exact le_of_lt (Real.tanh_lt_one (raw k i links))⟩

/-- Coordinatewise measurable physical observables give a measurable cutoff-to-cube map. -/
theorem selectedCMP119CutoffTanhCubeMap_measurable
    (raw : ∀ k : ℕ, ℕ → SU2TorusLinks (2 * (k + 1)) → ℝ)
    (hMeas : ∀ k i, Measurable (raw k i))
    (k : ℕ) :
    Measurable (selectedCMP119CutoffTanhCubeMap raw k) := by
  apply measurable_pi_lambda
  intro i
  apply Measurable.subtype_mk
  have hi := hMeas k i
  fun_prop

/-- Push one selected physical cutoff law onto the common compact cylinder cube. -/
noncomputable def selectedCMP119HeterogeneousCylinderPushforward
    (cutoff : ∀ k : ℕ, CMP119SelectedPhysicalCutoff (k + 1))
    (raw : ∀ k : ℕ, ℕ → SU2TorusLinks (2 * (k + 1)) → ℝ)
    (hMeas : ∀ k i, Measurable (raw k i))
    (k : ℕ) :
    ProbabilityMeasure HeterogeneousWilsonCylinderState :=
  ⟨(((cutoff k).gibbsLaw :
      ProbabilityMeasure (SU2TorusLinks (2 * (k + 1)))) :
      Measure (SU2TorusLinks (2 * (k + 1)))).map
        (selectedCMP119CutoffTanhCubeMap raw k),
    (Measure.isProbabilityMeasure_map_iff
      (selectedCMP119CutoffTanhCubeMap_measurable raw hMeas k).aemeasurable).2
      inferInstance⟩

/--
The full varying-lattice CMP119 family now literally lives on one common compact
cylinder state.  There is no common-raw-carrier assumption.
-/
noncomputable def selectedCMP119HeterogeneousCylinderCutoffLaw
    (cutoff : ∀ k : ℕ, CMP119SelectedPhysicalCutoff (k + 1))
    (raw : ∀ k : ℕ, ℕ → SU2TorusLinks (2 * (k + 1)) → ℝ)
    (hMeas : ∀ k i, Measurable (raw k i)) :
    ℕ → ProbabilityMeasure HeterogeneousWilsonCylinderState :=
  fun k => selectedCMP119HeterogeneousCylinderPushforward cutoff raw hMeas k

end RequestProject.YangMills
