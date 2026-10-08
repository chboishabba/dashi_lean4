import Integration.OggSSP2BWeightTwoIntegralC2Decomposition

/-!
# Source-native Co1 split of the untwisted / plus weight-two sector

In the FLM Leech-lattice realization the 98580-dimensional untwisted invariant
weight-two sector is the direct sum

  paired norm-four orbit sector, dimension 98280,
  Sym^2(h), dimension 300,

with `dim h = 24`.  Both pieces are stable under Leech automorphisms, and the
central lattice involution acts trivially on the paired labels and on the
symmetric square, so the action factors through Co1.

This is the source-native target split used by the Tate-cokernel rank-rigidity
compiler.  It does not identify the actual norm image inside these sectors.
-/

namespace Integration.OggSSP2BCo1UntwistedSectorSplit

abbrev heisenbergDimension : Nat := 24
abbrev symmetricSquareDimension : Nat := 300
abbrev normFourVectorCount : Nat := 196560
abbrev pairedNormFourOrbitDimension : Nat := 98280
abbrev untwistedPlusDimension : Nat := pairedNormFourOrbitDimension + symmetricSquareDimension

theorem paired_orbit_double_count : 2 * pairedNormFourOrbitDimension = normFourVectorCount := by decide
 theorem untwisted_plus_dimension_is_98580 : untwistedPlusDimension = 98580 := by decide

structure Boundary where
  flmUntwistedSectorSourcePaid : Bool
  pairedNormFourSectorDimensionPaid : Bool
  symmetricSquareSectorDimensionPaid : Bool
  pairedNormFourSectorCo1Stable : Bool
  symmetricSquareSectorCo1Stable : Bool
  directSectorSplitPaid : Bool
  actualNormImagePlacementPaid : Bool

def canonicalBoundary : Boundary where
  flmUntwistedSectorSourcePaid := true
  pairedNormFourSectorDimensionPaid := true
  symmetricSquareSectorDimensionPaid := true
  pairedNormFourSectorCo1Stable := true
  symmetricSquareSectorCo1Stable := true
  directSectorSplitPaid := true
  actualNormImagePlacementPaid := false

theorem actual_norm_image_placement_still_open :
    canonicalBoundary.actualNormImagePlacementPaid = false := rfl

end Integration.OggSSP2BCo1UntwistedSectorSplit
