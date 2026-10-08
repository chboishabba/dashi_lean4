import Mathlib

/-!
# Uniform-floor producer for weighted consensus dissipation

For a finite all-pairs coupling, a uniform lower bound `m <= w i j` immediately
produces a spectral-gap-style lower bound on the same pairwise disagreement
carrier:

  m * sum_{i,j} (x_i-x_j)^2 <= sum_{i,j} w_ij (x_i-x_j)^2.

This is purely algebraic and does not assume that Michels/LILA architecture
similarities actually satisfy the positivity floor.  That empirical/model
condition remains separate.
-/

namespace Integration.TeleodynamicsConsensusUniformFloor

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Unnormalised all-pairs disagreement. -/
def pairEnergy (x : ι → ℝ) : ℝ :=
  ∑ i : ι, ∑ j : ι, (x i - x j)^2

/-- Weighted all-pairs disagreement/dissipation carrier. -/
def weightedDissipation (w : ι → ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i : ι, ∑ j : ι, w i j * (x i - x j)^2

/-- A pointwise uniform weight floor is a same-carrier gap estimate. -/
theorem uniform_floor_gives_pair_gap
    {w : ι → ι → ℝ} {x : ι → ℝ} {m : ℝ}
    (hfloor : ∀ i j, m ≤ w i j) :
    m * pairEnergy x ≤ weightedDissipation w x := by
  simp only [pairEnergy, weightedDissipation, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_right (hfloor i j) (sq_nonneg (x i - x j))

/-- A strictly positive floor makes weighted dissipation strictly positive
whenever the pair-disagreement carrier is positive. -/
theorem positive_floor_positive_off_consensus
    {w : ι → ι → ℝ} {x : ι → ℝ} {m : ℝ}
    (hm : 0 < m)
    (hP : 0 < pairEnergy x)
    (hfloor : ∀ i j, m ≤ w i j) :
    0 < weightedDissipation w x := by
  have hgap := uniform_floor_gives_pair_gap (w := w) (x := x) hfloor
  exact lt_of_lt_of_le (mul_pos hm hP) hgap

/-- Explicit bridge shape into the scalar spectral-gap owner. -/
structure UniformFloorGapReceipt (w : ι → ι → ℝ) (x : ι → ℝ) where
  floor : ℝ
  floorPositive : 0 < floor
  pointwiseFloor : ∀ i j, floor ≤ w i j

/-- The receipt exposes the exact same-carrier inequality needed upstream. -/
theorem receipt_gives_gap
    {w : ι → ι → ℝ} {x : ι → ℝ}
    (r : UniformFloorGapReceipt w x) :
    r.floor * pairEnergy x ≤ weightedDissipation w x :=
  uniform_floor_gives_pair_gap r.pointwiseFloor

structure Boundary where
  finiteAllPairsGapDerived : Bool
  requiresUniformPositiveFloor : Bool
  architectureSimilarityAutomaticallyHasPositiveFloor : Bool
  symmetryAutomaticallyEstablished : Bool
  physicalCouplingEstablished : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  finiteAllPairsGapDerived := true
  requiresUniformPositiveFloor := true
  architectureSimilarityAutomaticallyHasPositiveFloor := false
  symmetryAutomaticallyEstablished := false
  physicalCouplingEstablished := false

end Integration.TeleodynamicsConsensusUniformFloor
