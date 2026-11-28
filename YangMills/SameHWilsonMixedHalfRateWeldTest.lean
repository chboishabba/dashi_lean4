import Mathlib
import YangMills.SameHWilsonMixedHalfRateWeld

namespace RequestProject.YangMills

example
    {State Obs H : Type*}
    [MeasurableSpace State] [TopologicalSpace State] [OpensMeasurableSpace State]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (weld : SameHWilsonMixedHalfRateWeld State Obs H)
    (left right : Obs) (time : ℕ) :
    |⟪weld.vector left, weld.transfer time (weld.vector right)⟫_ℝ| ≤
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ time :=
  weld.semigroup_mixed_half_rate left right time

example
    {Obs H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : ℕ → H →L[ℝ] H)
    (v : Obs → H)
    (hgen : ∀ i j, HalfRateMatrixBound T (v i) (v j))
    {left right : H}
    (hleft : left ∈ Submodule.span ℝ (Set.range v))
    (hright : right ∈ Submodule.span ℝ (Set.range v)) :
    HalfRateMatrixBound T left right :=
  halfRateMatrixBound_of_mem_span T v hgen hleft hright

example
    {State Obs H : Type*}
    [MeasurableSpace State] [TopologicalSpace State] [OpensMeasurableSpace State]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (weld : SameHDenseWilsonMixedHalfRateWeld State Obs H)
    (v : H) (hv : v ≠ 0) :
    ∃ w ∈ Submodule.span ℝ (Set.range weld.vector), ⟪w, v⟫_ℝ ≠ 0 :=
  weld.detects_nonzero v hv

end RequestProject.YangMills
