import Synthesis.RiemannG21WeightedHyperbolicCarrier

/-! RED-first regression contract for weighted hyperbolic symmetrized carriers. -/

namespace Synthesis

example {w : ℝ → ℝ} {a p u v : ℝ}
    (ha : 0 < a) (hap : a < p)
    (hu : 0 <= u) (hv : 0 <= v)
    (hwu : 0 <= w u) (hwv : 0 <= w v) :
    0 <= oddWeightedSymmCarrier w a p u v := by
  exact oddWeightedSymmCarrier_nonneg ha hap hu hv hwu hwv

example {w : ℝ → ℝ} {a p u v : ℝ}
    (ha : 0 < a) (hap : a < p)
    (hu : 0 < u) (huv : u < v)
    (hwu : 0 < w u) (hwv : 0 < w v) :
    0 < oddWeightedSymmCarrier w a p u v := by
  exact oddWeightedSymmCarrier_pos ha hap hu huv hwu hwv

example {w : ℝ → ℝ} {a p u v : ℝ}
    (ha : 0 < a) (hap : a < p)
    (hu : 0 <= u) (hv : 0 <= v)
    (hwu : 0 <= w u) (hwv : 0 <= w v) :
    0 <= evenWeightedSymmCarrier w a p u v := by
  exact evenWeightedSymmCarrier_nonneg ha hap hu hv hwu hwv

end Synthesis
