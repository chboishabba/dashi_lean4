import YangMills.CMP116DirectClusteringCut

namespace RequestProject.YangMills

example
    {Ω Obs : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    (source : CMP116DirectClusteringSource Ω Obs)
    (hconv : Filter.Tendsto source.cutoffLaw Filter.atTop (𝓝 source.continuumLaw))
    (obs : Obs) (time : ℕ) :
    |probabilityCovariance source.continuumLaw
        (source.left obs time) (source.right obs time)| ≤
      source.amplitude * Real.exp (-source.massRate * time) :=
  source.continuum_exponential_clustering hconv obs time

end RequestProject.YangMills
