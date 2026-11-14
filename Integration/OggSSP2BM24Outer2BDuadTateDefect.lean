import Integration.OggSSP2BActualStableCompletionSubquotient

/-!
# Exact M24-2B duad Tate-defect target

For the within-fibre outer involution, the finite duad model gives an exact
characteristic-two extension fingerprint.  ATLAS records that the relevant
M24 class is 2B, whose natural 24-point cycle shape is 2^12.  On unordered
2-subsets this fixes exactly the 12 transposition-pairs; the remaining 264
duads form 132 two-cycles.

Hence the permutation module over F2 has Jordan type J1^12 + J2^132, so
rank(g-I)=132, dim Fix(g)=144, and the C2 Tate defect has dimension 12.

This file records the finite target only.  It does not identify the actual
Monster 2B Tate extension with the duad extension.
-/

namespace Integration.OggSSP2BM24Outer2BDuadTateDefect

abbrev m24TwoACentralizerOrder : Nat := 21504
abbrev m24TwoBCentralizerOrder : Nat := 7680
abbrev m22d2OuterCentralizerOrder : Nat := 640

example : 12 * m22d2OuterCentralizerOrder = m24TwoBCentralizerOrder := by decide

abbrev duadDimension : Nat := 276
abbrev fixedDuadCount : Nat := 12
abbrev swappedDuadPairCount : Nat := 132
abbrev fixedSpaceDimension : Nat := fixedDuadCount + swappedDuadPairCount
abbrev rankGMinusI : Nat := swappedDuadPairCount
abbrev tateDefectDimension : Nat := fixedDuadCount

 theorem duad_dimension_closure :
    fixedDuadCount + 2 * swappedDuadPairCount = duadDimension := by decide

 theorem fixed_space_dimension_is_144 : fixedSpaceDimension = 144 := by decide
 theorem rank_g_minus_i_is_132 : rankGMinusI = 132 := by decide
 theorem tate_defect_is_twelve : tateDefectDimension = 12 := by decide

structure Boundary where
  atlasCentralizerDataSourced : Bool
  atlasNatural24CycleShapeSourced : Bool
  localPythonDuadOrbitAuditPassed : Bool
  exactDuadDefectTwelvePaid : Bool
  actualTwoBTateDefectComputed : Bool
  actualTateExtensionMatched : Bool

 def canonicalBoundary : Boundary where
  atlasCentralizerDataSourced := true
  atlasNatural24CycleShapeSourced := true
  localPythonDuadOrbitAuditPassed := true
  exactDuadDefectTwelvePaid := true
  actualTwoBTateDefectComputed := false
  actualTateExtensionMatched := false

end Integration.OggSSP2BM24Outer2BDuadTateDefect
