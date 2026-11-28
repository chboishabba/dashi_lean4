import Mathlib
import YangMills.CountableObservableDetermining

/-!
# Canonical bounded determining source on the countable coordinate carrier

Once the continuum carrier itself is chosen to be the countable coordinate
space `ℕ → ℝ`, there is no further abstract separation theorem: coordinate
projections separate points, and coordinatewise `tanh` turns them into a
uniformly bounded measurable embedding.  The physical Yang--Mills obligation
is therefore only the same-object map from the intended gauge state into this
carrier (or a proof that the selected physical observable map is injective).
-/

namespace RequestProject.YangMills

/-- Raw coordinate projections on the countable real carrier. -/
def canonicalCountableRawObservable : ℕ → (ℕ → ℝ) → ℝ :=
  fun i x => x i

/-- Every canonical coordinate projection is measurable. -/
theorem canonicalCountableRawObservable_measurable (i : ℕ) :
    Measurable (canonicalCountableRawObservable i) := by
  exact measurable_pi_apply i

/-- The full raw coordinate map separates points exactly. -/
theorem canonicalCountableRawObservable_injective :
    Function.Injective
      (countableObservableMap canonicalCountableRawObservable) := by
  intro x y hxy
  funext i
  exact congrFun hxy i

/-- Coordinatewise tanh coordinates still separate all countable states. -/
theorem canonical_tanh_coordinates_separate
    (x y : ℕ → ℝ)
    (h : ∀ i, Real.tanh (x i) = Real.tanh (y i)) :
    x = y := by
  funext i
  exact Real.tanh_injective (h i)

/--
For any sequence of cutoff laws already represented on the canonical countable
coordinate carrier, the bounded determining D source exists with no moment or
additional topology hypothesis.
-/
noncomputable def canonicalCountableCoordinateDeterminingSource
    (cutoffLaw : ℕ → ProbabilityMeasure (ℕ → ℝ)) :
    RealCountableObservableDeterminingSource (ℕ → ℝ) :=
  tanhDeterminingObservableSource
    cutoffLaw
    canonicalCountableRawObservable
    canonicalCountableRawObservable_measurable
    canonicalCountableRawObservable_injective

/-- The canonical coordinate construction discharges the exact D producer. -/
theorem canonical_countable_coordinate_producer_exists
    (cutoffLaw : ℕ → ProbabilityMeasure (ℕ → ℝ)) :
    RealCountableObservableDeterminingSource.ProducerExists
      cutoffLaw
      (fun i x => Real.tanh (x i)) := by
  exact tanh_determining_observable_producer_exists
    cutoffLaw
    canonicalCountableRawObservable
    canonicalCountableRawObservable_measurable
    canonicalCountableRawObservable_injective

end RequestProject.YangMills
