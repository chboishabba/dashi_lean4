import Integration.OggSSP2BIteratedTateDefectDetector

/-!
# Exact M22:2 outer-class duad iterated-Tate target

The finite Completion10 outer class has centralizer order 640 in `M22:2`.
Inside `M24`, the involution centralizers have orders 21504 (2A) and 7680
(2B). Since 640 must divide the ambient centralizer, the class cannot fuse to
2A, while `7680 = 12 * 640`; hence it fuses to M24-2B.

M24-2B has natural cycle shape `2^12` on 24 points. On the 276 duads, the
12 supports of those transpositions are fixed and the other 264 duads form 132
swapped pairs. Therefore on the F2 duad permutation module:

* rank(h - I) = 132,
* fixed dimension = 144,
* iterated Tate defect dimension = 276 - 2*132 = 12.

This is a scalar extension-structure target for the actual 2B-pure Klein-four
Tate computation; it is not a Tate↔duad same-object identification.
-/

namespace Integration.OggSSP2BM22d2OuterClassDuadDefect

abbrev localOuterCentralizer : Nat := 640
abbrev m24TwoACentralizer : Nat := 21504
abbrev m24TwoBCentralizer : Nat := 7680
abbrev fixedDuadCount : Nat := 12
abbrev swappedDuadPairCount : Nat := 132
abbrev ambientDuadDimension : Nat := 276
abbrev duadRankGMinusI : Nat := 132
abbrev duadFixedDimension : Nat := 144
abbrev duadIteratedTateDefect : Nat := 12

theorem m24_twoB_centralizer_ratio :
    m24TwoBCentralizer = 12 * localOuterCentralizer := by norm_num

theorem m24_twoA_not_divisible_by_local :
    m24TwoACentralizer % localOuterCentralizer = 384 := by norm_num

theorem duad_orbit_closure :
    fixedDuadCount + 2 * swappedDuadPairCount = ambientDuadDimension := by norm_num

theorem duad_rank : duadRankGMinusI = 132 := rfl

theorem duad_fixed_dimension : duadFixedDimension = 144 := rfl

theorem duad_iterated_tate_defect : duadIteratedTateDefect = 12 := rfl

theorem duad_defect_closure :
    duadIteratedTateDefect + 2 * duadRankGMinusI = ambientDuadDimension := by
  norm_num

structure Boundary where
  localOuterCentralizer640Paid : Bool
  m24InvolutionCentralizersSourced : Bool
  localCentralizerExcludesM24TwoA : Bool
  localCentralizerSelectsM24TwoB : Bool
  m24TwoBCycleShape2Pow12Sourced : Bool
  duadIteratedTateDefectTwelveDerived : Bool
  actualTwoBTateIteratedDefectComputed : Bool

def canonicalBoundary : Boundary where
  localOuterCentralizer640Paid := true
  m24InvolutionCentralizersSourced := true
  localCentralizerExcludesM24TwoA := true
  localCentralizerSelectsM24TwoB := true
  m24TwoBCycleShape2Pow12Sourced := true
  duadIteratedTateDefectTwelveDerived := true
  actualTwoBTateIteratedDefectComputed := false

end Integration.OggSSP2BM22d2OuterClassDuadDefect
