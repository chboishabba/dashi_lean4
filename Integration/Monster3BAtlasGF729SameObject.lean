import Mathlib

/-!
# Monster-3B ATLAS compression -> selected GF(729) same-object weld

The companion Agda/exact-executable lane has now imported the certified ATLAS
12-dimensional GF(3) Suzuki matrices, normalized their invariant alternating
form to the repository polarization, and found the outer word

  g2 g1 g2^-1 g1 g2^-1

whose X6 compression has irreducible degree-six characteristic polynomial

  x^6 - x^5 - x^3 + x^2 + 1.

The same executable receipt exhibits an explicit basis change Q to multiplication
by beta = 1-a in the selected polynomial presentation

  F3[a] / (a^6 + a^5 + a^4 + 1),

with

  Q * T = M_beta * Q.

This file moves the finite SAME-ACTION part of that receipt into Lean on literal
6x6 matrices over F3.  It proves the intertwining equation and an explicit
2-sided inverse for Q.  It deliberately does not infer Monster orbit semantics,
physical realization, or the irreducibility theorem merely from those matrix
identities; those remain separately attributed to the exact producer/source
lane.
-/

namespace Integration.Monster3BAtlasGF729SameObject

abbrev F3 := ZMod 3
abbrev Mat6 := Matrix (Fin 6) (Fin 6) F3

/-- The selected ATLAS-word X6 compression from the exact producer. -/
def compressionT : Mat6 := ![
  ![0, 2, 1, 0, 2, 1],
  ![2, 0, 2, 1, 2, 2],
  ![0, 0, 0, 0, 1, 2],
  ![2, 0, 1, 2, 1, 2],
  ![2, 0, 2, 2, 0, 2],
  ![1, 0, 1, 0, 2, 2]
]

/-- Multiplication by beta = 1-a in the selected GF(729) polynomial basis. -/
def selectedMulBeta : Mat6 := ![
  ![1, 0, 0, 0, 0, 1],
  ![2, 1, 0, 0, 0, 0],
  ![0, 2, 1, 0, 0, 0],
  ![0, 0, 2, 1, 0, 0],
  ![0, 0, 0, 2, 1, 1],
  ![0, 0, 0, 0, 2, 2]
]

/-- Explicit change of basis supplied by the exact same-object producer. -/
def intertwinerQ : Mat6 := ![
  ![1, 0, 0, 2, 1, 1],
  ![0, 0, 0, 2, 1, 2],
  ![0, 0, 2, 1, 0, 1],
  ![0, 0, 1, 1, 2, 0],
  ![0, 1, 1, 0, 1, 2],
  ![0, 2, 0, 1, 2, 2]
]

/-- Explicit inverse of Q over F3, independently reconstructed from the receipt. -/
def intertwinerQInv : Mat6 := ![
  ![1, 1, 1, 2, 2, 2],
  ![0, 1, 1, 2, 2, 1],
  ![0, 0, 1, 0, 2, 2],
  ![0, 1, 1, 1, 0, 0],
  ![0, 1, 2, 0, 2, 2],
  ![0, 2, 1, 2, 2, 2]
]

/-- Literal same-action identity: the source compression is conjugate to the
selected GF(729) multiplication operator. -/
theorem compression_selected_action_intertwines :
    intertwinerQ * compressionT = selectedMulBeta * intertwinerQ := by
  native_decide

/-- Q is injective/surjective on the same six-dimensional F3 carrier, witnessed
without an order or determinant argument. -/
theorem intertwiner_left_inverse : intertwinerQInv * intertwinerQ = 1 := by
  native_decide

theorem intertwiner_right_inverse : intertwinerQ * intertwinerQInv = 1 := by
  native_decide

/-- Conjugacy in the more familiar solved form. -/
theorem compression_conjugate_to_selected_mul_beta :
    compressionT = intertwinerQInv * selectedMulBeta * intertwinerQ := by
  calc
    compressionT = 1 * compressionT := by simp
    _ = (intertwinerQInv * intertwinerQ) * compressionT := by
      rw [intertwiner_left_inverse]
    _ = intertwinerQInv * (intertwinerQ * compressionT) := by
      simp [Matrix.mul_assoc]
    _ = intertwinerQInv * (selectedMulBeta * intertwinerQ) := by
      rw [compression_selected_action_intertwines]
    _ = intertwinerQInv * selectedMulBeta * intertwinerQ := by
      simp [Matrix.mul_assoc]

/-- Exact producer metadata retained as data, not promoted to a kernel proof of
polynomial irreducibility in this owner. -/
def selectedSourceWord : String := "g2 g1 g2^-1 g1 g2^-1"
def selectedCompressionCharacteristicPolynomial : String :=
  "x^6 - x^5 - x^3 + x^2 + 1"
def selectedGF729Modulus : String := "a^6 + a^5 + a^4 + 1"
def selectedAffineGeneratorChange : String := "beta = 1 - a"

structure Boundary where
  atlasMatricesVendoredOnCompanionAgda : Bool
  exactCompressionSearchPaidOnCompanionProducer : Bool
  compressionDegreeSixIrreducibilityProducerPaid : Bool
  explicitCompressionMatrixPaid : Bool
  explicitGF729ActionMatrixPaid : Bool
  explicitInvertibleIntertwinerPaid : Bool
  sameSelectedGF729ActionPaid : Bool
  irreducibilityReprovedInLeanHere : Bool
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
  irreducibilityReprovedInLeanHere := false
  fullMonsterOrbitSemanticsPaid := false
  physicalMonster3BRealizationPaid := false

end Integration.Monster3BAtlasGF729SameObject
