import Integration.TeleodynamicsConsensusUniformFloor

namespace Integration.TeleodynamicsConsensusUniformFloorRegression

open Integration.TeleodynamicsConsensusUniformFloor

variable {ι : Type} [Fintype ι] [DecidableEq ι]

example (w : ι → ι → ℝ) (x : ι → ℝ) (m : ℝ)
    (h : ∀ i j, m ≤ w i j) :
    m * pairEnergy x ≤ weightedDissipation w x :=
  uniform_floor_gives_pair_gap h

example (w : ι → ι → ℝ) (x : ι → ℝ) (m : ℝ)
    (hm : 0 < m) (hP : 0 < pairEnergy x)
    (h : ∀ i j, m ≤ w i j) :
    0 < weightedDissipation w x :=
  positive_floor_positive_off_consensus hm hP h

end Integration.TeleodynamicsConsensusUniformFloorRegression
