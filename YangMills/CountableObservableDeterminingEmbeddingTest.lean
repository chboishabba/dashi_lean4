import Mathlib
import YangMills.CountableObservableDetermining

open MeasureTheory

namespace RequestProject.YangMills

example
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (cutoffLaw : ℕ → ProbabilityMeasure Ω)
    (raw : ℕ → Ω → ℝ)
    (hMeas : ∀ i, Measurable (raw i))
    (hSep : Function.Injective (countableObservableMap raw)) :
    RealCountableObservableDeterminingSource Ω :=
  tanhDeterminingObservableSource cutoffLaw raw hMeas hSep

example
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (raw : ℕ → Ω → ℝ)
    (hMeas : ∀ i, Measurable (raw i))
    (hSep : Function.Injective (countableObservableMap raw)) :
    MeasurableEmbedding
      (countableObservableMap (fun i x => Real.tanh (raw i x))) :=
  tanh_countable_observable_map_measurableEmbedding raw hMeas hSep

end RequestProject.YangMills
