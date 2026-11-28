import YangMills.WilsonSpectralCompleteness

namespace RequestProject.YangMills

example
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (wilsonVectors : Set H) (hDense : Dense wilsonVectors)
    (v : H) (hv : v ≠ 0) :
    ∃ w ∈ wilsonVectors, ⟪w, v⟫_ℝ ≠ 0 :=
  dense_wilson_vectors_detect_nonzero wilsonVectors hDense v hv

end RequestProject.YangMills
