import YangMills.CanonicalCountableCoordinateDetermining

namespace RequestProject.YangMills

example
    (cutoffLaw : ℕ → ProbabilityMeasure (ℕ → ℝ)) :
    RealCountableObservableDeterminingSource (ℕ → ℝ) :=
  canonicalCountableCoordinateDeterminingSource cutoffLaw

example
    (x y : ℕ → ℝ)
    (h : ∀ i, Real.tanh (x i) = Real.tanh (y i)) :
    x = y :=
  canonical_tanh_coordinates_separate x y h

end RequestProject.YangMills
