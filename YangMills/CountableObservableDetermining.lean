import Mathlib
import Mathlib.Analysis.SpecialFunctions.Artanh
import YangMills.CountableObservableCoordinateMoment

/-!
# Bounded countable determining observable families

The bounded-observable D3 route does not need coercive moments merely to obtain
a first continuum coordinate law.  The remaining physical/topological question
is whether the chosen countable coordinates determine the intended state.

A measurable embedding of the full coordinate map is a clean sufficient
criterion: mathlib's `MeasurableEmbedding.map_injective` then says equality of
all coordinate pushforward laws forces equality of the underlying measures.
This file also exposes the bounded injective `tanh` transform used by the D-F
route for otherwise unbounded smeared observables.
-/

open MeasureTheory

namespace RequestProject.YangMills

/-- Full countable coordinate map associated to a selected scalar family. -/
def countableObservableMap
    {Ω : Type*} [MeasurableSpace Ω]
    (observable : ℕ → Ω → ℝ) : Ω → (ℕ → ℝ) :=
  fun x i => observable i x

/-- Coordinatewise measurability gives measurability of the full countable map. -/
theorem countable_observable_map_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (observable : ℕ → Ω → ℝ)
    (hMeas : ∀ i, Measurable (observable i)) :
    Measurable (countableObservableMap observable) := by
  apply measurable_pi_lambda
  intro i
  exact hMeas i

/--
Bounded D3 source plus a measurable-embedding proof for the selected coordinate
map.  The latter is exactly the determining/separating obligation and is not
manufactured by boundedness.
-/
structure RealCountableObservableDeterminingSource
    (Ω : Type*) [MeasurableSpace Ω]
    extends RealCountableObservableUniformBoundSource Ω where
  coordinateMapEmbedding :
    MeasurableEmbedding (countableObservableMap observable)

namespace RealCountableObservableDeterminingSource

/-- The selected countable coordinate map. -/
def coordinateMap
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableDeterminingSource Ω) :
    Ω → (ℕ → ℝ) :=
  countableObservableMap source.observable

/-- The determining map is measurable. -/
theorem coordinateMap_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableDeterminingSource Ω) :
    Measurable source.coordinateMap :=
  source.coordinateMapEmbedding.measurable

/-- Equality of selected coordinate pushforwards determines the original measure. -/
theorem measure_eq_of_coordinate_map_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableDeterminingSource Ω)
    (μ ν : Measure Ω)
    (h : Measure.map source.coordinateMap μ =
      Measure.map source.coordinateMap ν) :
    μ = ν := by
  exact source.coordinateMapEmbedding.map_injective h

/-- The bounded determining source inherits the already-built D3 continuum coordinate law. -/
noncomputable def globalCoordinateMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableDeterminingSource Ω) :
    Measure (ℕ → ℝ) :=
  source.toRealCountableObservableUniformBoundSource.globalMeasure

instance globalCoordinateMeasureIsProbability
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableDeterminingSource Ω) :
    IsProbabilityMeasure source.globalCoordinateMeasure := by
  unfold globalCoordinateMeasure
  infer_instance

/-- Exact D physical producer: boundedness plus the determining embedding. -/
def ProducerExists
    {Ω : Type*} [MeasurableSpace Ω]
    (cutoffLaw : ℕ → ProbabilityMeasure Ω)
    (observable : ℕ → Ω → ℝ) : Prop :=
  ∃ source : RealCountableObservableDeterminingSource Ω,
    source.cutoffLaw = cutoffLaw ∧ source.observable = observable

end RealCountableObservableDeterminingSource

/-- Any real observable can be compressed injectively into `(-1,1)` using `tanh`. -/
def tanhBoundedObservable
    {Ω : Type*}
    (raw : Ω → ℝ) : Ω → ℝ :=
  fun x => Real.tanh (raw x)

/-- The tanh transform is uniformly bounded by one. -/
theorem tanh_bounded_observable_abs_le_one
    {Ω : Type*}
    (raw : Ω → ℝ) (x : Ω) :
    |tanhBoundedObservable raw x| ≤ 1 := by
  exact (Real.abs_tanh_lt_one (raw x)).le

/-- Tanh does not lose pointwise information. -/
theorem tanh_bounded_observable_injective_of_injective
    {Ω : Type*}
    (raw : Ω → ℝ)
    (hraw : Function.Injective raw) :
    Function.Injective (tanhBoundedObservable raw) := by
  intro x y hxy
  apply hraw
  exact Real.tanh_injective hxy

/--
Turn any measurable countable real family into a cutoff-uniformly bounded D3
source.  This removes moment growth from the *existence* step; whether the full
transformed coordinate map is determining remains a separate embedding proof.
-/
noncomputable def tanhBoundedObservableSource
    {Ω : Type*} [MeasurableSpace Ω]
    (cutoffLaw : ℕ → ProbabilityMeasure Ω)
    (raw : ℕ → Ω → ℝ)
    (hMeas : ∀ i, Measurable (raw i)) :
    RealCountableObservableUniformBoundSource Ω where
  cutoffLaw := cutoffLaw
  observable := fun i x => Real.tanh (raw i x)
  observableMeasurable := by
    intro i
    fun_prop
  coordinateBound := fun _ => 1
  coordinateBoundNonneg := by intro i; norm_num
  observableAbsLe := by
    intro i x
    exact (Real.abs_tanh_lt_one (raw i x)).le

/-- Coordinatewise tanh preserves injectivity of the full countable raw map. -/
theorem tanh_countable_observable_map_injective
    {Ω : Type*}
    (raw : ℕ → Ω → ℝ)
    (hraw : Function.Injective (countableObservableMap raw)) :
    Function.Injective
      (countableObservableMap (fun i x => Real.tanh (raw i x))) := by
  intro x y hxy
  apply hraw
  funext i
  exact Real.tanh_injective (congrFun hxy i)

/--
On a standard Borel state space, a countable measurable point-separating real
family becomes a measurable embedding after the coordinatewise bounded `tanh`
transform.  Thus boundedness does not add a second separation obligation.
-/
theorem tanh_countable_observable_map_measurableEmbedding
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (raw : ℕ → Ω → ℝ)
    (hMeas : ∀ i, Measurable (raw i))
    (hraw : Function.Injective (countableObservableMap raw)) :
    MeasurableEmbedding
      (countableObservableMap (fun i x => Real.tanh (raw i x))) := by
  apply Measurable.measurableEmbedding
  · apply countable_observable_map_measurable
    intro i
    have hi := hMeas i
    fun_prop
  · exact tanh_countable_observable_map_injective raw hraw

/--
Canonical D-F constructor: any countable measurable point-separating real
family on a standard Borel state space yields the exact bounded determining
source consumed by the projective continuum-measure machinery.
-/
noncomputable def tanhDeterminingObservableSource
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (cutoffLaw : ℕ → ProbabilityMeasure Ω)
    (raw : ℕ → Ω → ℝ)
    (hMeas : ∀ i, Measurable (raw i))
    (hraw : Function.Injective (countableObservableMap raw)) :
    RealCountableObservableDeterminingSource Ω where
  cutoffLaw := cutoffLaw
  observable := fun i x => Real.tanh (raw i x)
  observableMeasurable := by
    intro i
    have hi := hMeas i
    fun_prop
  coordinateBound := fun _ => 1
  coordinateBoundNonneg := by intro i; norm_num
  observableAbsLe := by
    intro i x
    exact (Real.abs_tanh_lt_one (raw i x)).le
  coordinateMapEmbedding :=
    tanh_countable_observable_map_measurableEmbedding raw hMeas hraw

/-- The canonical tanh constructor discharges the exact D producer proposition. -/
theorem tanh_determining_observable_producer_exists
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (cutoffLaw : ℕ → ProbabilityMeasure Ω)
    (raw : ℕ → Ω → ℝ)
    (hMeas : ∀ i, Measurable (raw i))
    (hraw : Function.Injective (countableObservableMap raw)) :
    RealCountableObservableDeterminingSource.ProducerExists
      cutoffLaw (fun i x => Real.tanh (raw i x)) := by
  refine ⟨tanhDeterminingObservableSource cutoffLaw raw hMeas hraw, ?_, ?_⟩
  · rfl
  · rfl

end RequestProject.YangMills
