import YangMills.SameHWilsonHalfRateWeld

namespace RequestProject.YangMills

example
    {State Obs H : Type*}
    [MeasurableSpace State] [TopologicalSpace State] [OpensMeasurableSpace State]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (weld : SameHWilsonHalfRateWeld State Obs H)
    (obs : Obs) (time : ℕ) :
    |⟪weld.vector obs, weld.transfer time (weld.vector obs)⟫_ℝ| ≤
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ time :=
  weld.semigroup_half_rate obs time

end RequestProject.YangMills
