import Mathlib

/-!
# Monster-3B ATLAS compression -> selected GF(729) primitive same-object weld

The companion Agda/exact-executable lane imports the certified ATLAS
12-dimensional GF(3) Suzuki matrices and normalizes the unique alternating form
to the repository X6 + X6* polarization.

An earlier depth-five source word produced a degree-six generator beta=1-alpha
of multiplicative order 364.  Continuing the SAME source search to depth seven
found the stronger word

  g2^-1 g1 g2^-1 g1 g2 g1 g2^-1

whose X6 compression is conjugate, in the already-selected

  GF(729) = F3[alpha] / (alpha^6 + alpha^5 + alpha^4 + 1),

to multiplication by the explicit primitive element

  gamma = (0,2,0,1,2,0),    ord(gamma)=728.

The companion exact producer supplies literal T, M_gamma and an invertible Q
with Q*T=M_gamma*Q.  This file moves the SAME-ACTION matrix identity into Lean
on the literal six-dimensional F3 carrier, including an explicit two-sided
inverse for Q.  The multiplicative-order 728 / punctured-orbit 728 / trivial
stabilizer facts remain exact-producer authority in this owner unless separately
reproved in Lean; no cardinality shortcut is used to create the matrix weld.
-/

namespace Integration.Monster3BAtlasGF729SameObject

abbrev F3 := ZMod 3
abbrev Mat6 := Matrix (Fin 6) (Fin 6) F3

/-- Preferred primitive ATLAS-word X6 compression. -/
def compressionT : Mat6 := ![
  ![0, 0, 0, 2, 2, 2],
  ![2, 1, 0, 2, 0, 0],
  ![0, 2, 1, 0, 0, 2],
  ![1, 0, 1, 0, 2, 0],
  ![2, 0, 2, 2, 0, 1],
  ![0, 1, 1, 2, 0, 2]
]

/-- Multiplication by the selected primitive gamma in the chosen GF(729) basis. -/
def selectedMulGamma : Mat6 := ![
  ![0, 0, 1, 1, 1, 2],
  ![2, 0, 0, 1, 1, 1],
  ![0, 2, 0, 0, 1, 1],
  ![1, 0, 2, 0, 0, 1],
  ![2, 1, 1, 0, 1, 2],
  ![0, 2, 2, 2, 1, 0]
]

/-- Explicit same-object basis change supplied by the exact producer. -/
def intertwinerQ : Mat6 := ![
  ![1, 1, 1, 0, 2, 0],
  ![0, 0, 1, 2, 0, 0],
  ![0, 1, 0, 2, 1, 1],
  ![0, 1, 1, 1, 2, 2],
  ![0, 0, 2, 2, 0, 0],
  ![0, 2, 1, 0, 1, 0]
]

/-- Explicit inverse of Q over F3. -/
def intertwinerQInv : Mat6 := ![
  ![1, 2, 0, 0, 1, 1],
  ![0, 2, 2, 2, 1, 0],
  ![0, 2, 0, 0, 1, 0],
  ![0, 1, 0, 0, 1, 0],
  ![0, 0, 2, 2, 0, 1],
  ![0, 2, 0, 2, 0, 2]
]

/-- Literal same-action identity for the preferred primitive source word. -/
theorem compression_selected_action_intertwines :
    intertwinerQ * compressionT = selectedMulGamma * intertwinerQ := by
  native_decide

theorem intertwiner_left_inverse : intertwinerQInv * intertwinerQ = 1 := by
  native_decide

theorem intertwiner_right_inverse : intertwinerQ * intertwinerQInv = 1 := by
  native_decide

theorem compression_conjugate_to_selected_mul_gamma :
    compressionT = intertwinerQInv * selectedMulGamma * intertwinerQ := by
  native_decide

/-- Source/executable metadata. -/
def selectedSourceWord : String := "g2^-1 g1 g2^-1 g1 g2 g1 g2^-1"
def selectedCompressionCharacteristicPolynomial : String :=
  "x^6 - x^5 - x^4 - x^3 + x^2 - 1"
def selectedGF729Modulus : String := "a^6 + a^5 + a^4 + 1"
def selectedGammaCoordinates : List Nat := [0, 2, 0, 1, 2, 0]
def selectedGammaMultiplicativeOrder : Nat := 728
def selectedPuncturedOrbitSize : Nat := 728
def selectedPuncturedStabilizerSize : Nat := 1

def earlierDepthFiveSourceWord : String := "g2 g1 g2^-1 g1 g2^-1"
def earlierBetaMultiplicativeOrder : Nat := 364

structure Boundary where
  atlasMatricesVendoredOnCompanionAgda : Bool
  exactCompressionSearchPaidOnCompanionProducer : Bool
  compressionDegreeSixIrreducibilityProducerPaid : Bool
  explicitCompressionMatrixPaid : Bool
  explicitGF729ActionMatrixPaid : Bool
  explicitInvertibleIntertwinerPaid : Bool
  sameSelectedGF729ActionPaid : Bool
  primitiveOrder728PaidByExactProducer : Bool
  puncturedOrbit728PaidByExactProducer : Bool
  puncturedStabilizerTrivialPaidByExactProducer : Bool
  primitiveOrderReprovedInLeanHere : Bool
  fullMonsterOrbitSemanticsPaid : Bool
  physicalMonster3BRealizationPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  atlasMatricesVendoredOnCompanionAgda := true
  exactCompressionSearchPaidOnCompanionProducer := true
  compressionDegreeSixIrreducibilityProducerPaid := true
  explicitCompressionMatrixPaid := true
  explicitGF729ActionMatrixPaid := true
  explicitInvertibleIntertwinerPaid := true
  sameSelectedGF729ActionPaid := true
  primitiveOrder728PaidByExactProducer := true
  puncturedOrbit728PaidByExactProducer := true
  puncturedStabilizerTrivialPaidByExactProducer := true
  primitiveOrderReprovedInLeanHere := false
  fullMonsterOrbitSemanticsPaid := false
  physicalMonster3BRealizationPaid := false

end Integration.Monster3BAtlasGF729SameObject
