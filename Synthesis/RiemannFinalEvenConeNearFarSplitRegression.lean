import Synthesis.RiemannFinalEvenConeNearFarSplit

namespace Synthesis

example {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (t s : ℝ) :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 ≤ C ∧
      (∀ J : ℕ, 1 ≤ J →
        |evenConeFunctional (offOrdVec (sampleFam g t s) t)
            - (1 / 2 : ℝ) * ∑ sigma ∈ finalNearOffFinset t J,
                finalPairTerm g t s sigma|
          ≤ (1 / 2 : ℝ) * (C * farShellBound A |t| J))
      ∧ Filter.Tendsto
          (fun J : ℕ => (1 / 2 : ℝ) * (C * farShellBound A |t| J))
          Filter.atTop (nhds 0) :=
  exists_finalEvenCone_near_far_split hgs hgc heven t s

end Synthesis
