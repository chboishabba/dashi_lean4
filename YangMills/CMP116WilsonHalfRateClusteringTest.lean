import YangMills.CMP116WilsonHalfRateClustering

namespace RequestProject.YangMills

example
    {Ω Obs : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    (source : CMP116WilsonHalfRateClusteringSource Ω Obs)
    (hconv : Tendsto source.cutoffLaw atTop (𝓝 source.continuumLaw))
    (obs : Obs) (time : ℕ) :
    |probabilityCovariance source.continuumLaw
        (source.left obs time) (source.right obs time)| ≤
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ time :=
  source.continuum_half_rate hconv obs time

end RequestProject.YangMills
