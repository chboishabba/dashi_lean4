import Synthesis.RiemannAdaptiveCutoffCrossingCompatibility

namespace Synthesis

example
    {Λ ε : ℝ} (hΛ : 0 < Λ) (hε : 0 < ε)
    {far : ℕ → ℝ}
    (hfar : Filter.Tendsto far Filter.atTop (nhds 0)) :
    ∃ J : ℕ, 1 ≤ J ∧ Real.pi / 2 < (J : ℝ) * Λ ∧ far J < ε :=
  exists_nat_cutoff_crossing_and_small hΛ hε hfar

end Synthesis
