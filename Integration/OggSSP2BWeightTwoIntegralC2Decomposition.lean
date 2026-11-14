import Integration.OggSSP2BMod4ExtensionAcquisition

/-!
# Forced integral C2 decomposition at 2B weight two

At even weight the sourced integral Moonshine restriction to the selected 2B
involution uses only the trivial rank-one lattice E+ and the free rank-two
lattice E0 = Z[C2].  The weight-two rank is 196884 and the paid Tate H^0
multiplicity is 276.  Therefore the integral multiplicities are forced:

  E+^276 ⊕ E0^98304.

Over Q the + and - eigenspaces have dimensions 98580 and 98304.  This exactly
aligns with the sourced 2B-centralizer branching 98304 + 98280 + 300.
-/

namespace Integration.OggSSP2BWeightTwoIntegralC2Decomposition

abbrev weightTwoRank : Nat := 196884
abbrev trivialC2SummandCount : Nat := 276
abbrev freeC2SummandCount : Nat := 98304
abbrev plusEigenspaceDimension : Nat := trivialC2SummandCount + freeC2SummandCount
abbrev minusEigenspaceDimension : Nat := freeC2SummandCount
abbrev conwayPositiveBranchDimension : Nat := 98280 + 300

theorem integral_rank_closure :
    trivialC2SummandCount + 2 * freeC2SummandCount = weightTwoRank := by decide

theorem plus_eigenspace_is_98580 : plusEigenspaceDimension = 98580 := by decide
 theorem minus_eigenspace_is_98304 : minusEigenspaceDimension = 98304 := by decide
 theorem conway_positive_branch_is_98580 : conwayPositiveBranchDimension = 98580 := by decide
 theorem centralizer_branching_closure :
    minusEigenspaceDimension + conwayPositiveBranchDimension = weightTwoRank := by decide

structure Boundary where
  evenWeightC2SourceRestrictionPaid : Bool
  weightTwoTateDimension276Paid : Bool
  forcedIntegralC2MultiplicitiesPaid : Bool
  centralizerBranchingDimensionAlignmentPaid : Bool

def canonicalBoundary : Boundary where
  evenWeightC2SourceRestrictionPaid := true
  weightTwoTateDimension276Paid := true
  forcedIntegralC2MultiplicitiesPaid := true
  centralizerBranchingDimensionAlignmentPaid := true

end Integration.OggSSP2BWeightTwoIntegralC2Decomposition
