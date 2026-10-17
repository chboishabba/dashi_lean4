import Integration.OggSSP2BM24Outer2BDuadTateDefect

/-!
# Mod-4 extension acquisition route

At p=2 the remaining obstruction is extension/Jordan data. Reduction mod 2 loses
sign information, so a stronger integral route keeps the C2-lattice modulo 4.
For the finite duad permutation lattice and the relevant M24-2B involution, the
integral C2 decomposition is exactly E+^12 ⊕ E0^132, with no sign E- summand.

This is an extension fingerprint for the finite target only. It does not identify
the actual Monster 2B Tate extension.
-/

namespace Integration.OggSSP2BMod4ExtensionAcquisition

abbrev trivialRankOneCount : Nat := 12
abbrev signRankOneCount : Nat := 0
abbrev regularRankTwoCount : Nat := 132
abbrev integralRank : Nat := trivialRankOneCount + signRankOneCount + 2 * regularRankTwoCount
abbrev mod2FixedDimension : Nat := trivialRankOneCount + regularRankTwoCount
abbrev mod2TateDefect : Nat := trivialRankOneCount + signRankOneCount

 theorem integral_rank_is_276 : integralRank = 276 := by decide
 theorem fixed_dimension_is_144 : mod2FixedDimension = 144 := by decide
 theorem tate_defect_is_twelve : mod2TateDefect = 12 := by decide

structure Boundary where
  modTwoSignLossProblemSourced : Bool
  modFourLatticeMethodSourced : Bool
  finiteDuadIntegralC2FingerprintPaid : Bool
  actualMoonshineCommutingPairClassProbeImplemented : Bool
  actualMoonshineModFourRestrictionComputed : Bool
  actualTateExtensionFingerprintMatched : Bool

 def canonicalBoundary : Boundary where
  modTwoSignLossProblemSourced := true
  modFourLatticeMethodSourced := true
  finiteDuadIntegralC2FingerprintPaid := true
  actualMoonshineCommutingPairClassProbeImplemented := true
  actualMoonshineModFourRestrictionComputed := false
  actualTateExtensionFingerprintMatched := false

end Integration.OggSSP2BMod4ExtensionAcquisition
