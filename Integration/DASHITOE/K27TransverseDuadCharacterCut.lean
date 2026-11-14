import Mathlib

/-!
# 26D string massless SO24 fields versus M24 degree-276 duads

Source owners: Agda LeechWeightTwo196608BridgeExact (299 trace-free Sym²)
and OggSSP2BM24DuadPair24AuthorityExact (ATLAS p276 duads).
Primary source: ATLAS M24 p24B0, p276B0 involution types 2A and 2B.
The geometric identity Λ²(R24) ≅ Λ²²(R24) is from ordinary transverse
Hodge star; this file proves only EXACT character / dimension arithmetic
for the externally sourced cycle types, not an actual M24 action, quantum
K27 module or the Cartan forms of the closed bosonic string.

Original application: a 276-dimensional space of UNORIENTED duad
coefficients carries a different M24 action from the ORIENTED two-form
space, whose pair-flip is signed. Thus a same-source M24 module
identification cannot follow from dimension.
-/

namespace DASHIK27Transverse

/-- Twenty-six-dimensional bosonic strings have 24 transverse directions. -/
theorem transverseDimension : 26 - 2 = 24 := by norm_num

theorem antisymmetricTwoFormPolarizations :
    Nat.choose 24 2 = 276 := by norm_num

theorem dualTwentyTwoFormPolarizations :
    Nat.choose 24 22 = 276 := by norm_num

theorem symmetricTracelessGravitonPolarizations :
    24 * (24 + 1) / 2 - 1 = 299 := by norm_num

theorem physicalClosedStateDecomposition :
    299 + 276 + 1 = 24 * 24 := by norm_num

/-- ATLAS M24 class 2A has cycle type 1^8 2^8.
    Its ordinary two-subset permutation action has C(8,2)+8 fixed duads. -/
theorem atlas2AUnorientedDuadTrace :
    Nat.choose 8 2 + 8 = 36 := by norm_num

/-- The same class on Λ² of the natural 24-point module takes
    the NEGATIVE orientation on the eight swapped duads. -/
theorem atlas2AOrientedWedgeTrace :
    (Nat.choose 8 2 : ℤ) - 8 = 20 := by norm_num

theorem atlas2ACharacterMismatch :
    (36 : ℤ) ≠ 20 := by norm_num

/-- ATLAS M24 class 2B has 12 transpositions and zero fixed points. -/
theorem atlas2BUnorientedDuadTrace :
    12 = Nat.choose 0 2 + 12 := by norm_num

theorem atlas2BOrientedWedgeTrace :
    (Nat.choose 0 2 : ℤ) - 12 = -12 := by norm_num

theorem atlas2BCharacterMismatch :
    (12 : ℤ) ≠ -12 := by norm_num

/-- For SO(24) little-group data, Sym²_0, Λ² and the scalar
    combine to the 24⊗24 massless closed-string tensor.
    These numbers reproduce the characteristic character at 2A/2B. -/
theorem atlas2AFullTensorCharacter :
    (43 : ℤ) + 20 + 1 = 8 * 8 := by norm_num

theorem atlas2BFullTensorCharacter :
    (11 : ℤ) + (-12) + 1 = 0 := by norm_num

/-- ATLAS character-data obstruction, CONDITIONAL on preserving the original
    M24 actions: an intertwiner would have to preserve character at 2A. -/
theorem noMatchingActionCharacter
    (sameCharacterAt2A : (36 : ℤ) = 20) : False :=
  atlas2ACharacterMismatch sameCharacterAt2A

end DASHIK27Transverse
