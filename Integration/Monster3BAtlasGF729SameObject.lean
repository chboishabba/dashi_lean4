import Mathlib

/-!
# Monster-3B ATLAS compression -> selected GF(729) center-preserving primitive weld

The companion Agda/exact-executable lane imports the certified ATLAS
12-dimensional GF(3) Suzuki matrices and normalizes the unique alternating form
to the repository X6 + X6* polarization.

Three source roles are now separated:

* depth 5, multiplier 1: first field-presentation weld, order 364;
* depth 7, multiplier 2: primitive order 728, center-inverting comparator;
* depth 8, multiplier 1: primitive order 728 and the preferred SAME-PHASE target.

This owner uses the depth-eight word

  g1 g2^-1 g1 g2 g1 g2^-1 g1 g2^-1

whose X6 compression is conjugate, in the already-selected

  GF(729) = F3[alpha] / (alpha^6 + alpha^5 + alpha^4 + 1),

to multiplication by

  delta = (0,1,0,1,1,0),    ord(delta)=728.

The companion exact producer supplies literal T, M_delta and invertible Q with
Q*T=M_delta*Q.  This file source-writes finite Lean proofs by `native_decide`
for the same-action identity, Q inverse, exact order 728, 728-state seed orbit,
and trivial stabilizer.  Because Lean is unavailable in the present execution
environment these remain SOURCE-WRITTEN theorem obligations until an exact-head
kernel receipt is observed.
-/

namespace Integration.Monster3BAtlasGF729SameObject

abbrev F3 := ZMod 3
abbrev Mat6 := Matrix (Fin 6) (Fin 6) F3
abbrev Vec6 := Fin 6 → F3

/-- Preferred strict-symplectic primitive source compression. -/
def compressionT : Mat6 := ![
  ![2, 2, 0, 1, 1, 2],
  ![0, 0, 0, 1, 1, 2],
  ![2, 1, 0, 0, 0, 0],
  ![1, 2, 0, 2, 2, 2],
  ![0, 0, 1, 1, 1, 2],
  ![0, 0, 1, 2, 1, 1]
]

/-- Multiplication by delta=(0,1,0,1,1,0) in the selected GF(729) basis. -/
def selectedMulDelta : Mat6 := ![
  ![0, 0, 2, 0, 1, 1],
  ![1, 0, 0, 2, 0, 1],
  ![0, 1, 0, 0, 2, 0],
  ![1, 0, 1, 0, 0, 2],
  ![1, 1, 2, 1, 1, 1],
  ![0, 1, 0, 2, 2, 2]
]

/-- Explicit same-object basis change. -/
def intertwinerQ : Mat6 := ![
  ![1, 1, 0, 1, 0, 0],
  ![0, 2, 0, 1, 2, 2],
  ![0, 0, 1, 1, 0, 1],
  ![0, 1, 1, 2, 0, 2],
  ![0, 2, 2, 0, 2, 2],
  ![0, 2, 2, 2, 2, 2]
]

/-- Explicit inverse of Q over F3. -/
def intertwinerQInv : Mat6 := ![
  ![1, 2, 2, 2, 1, 0],
  ![0, 1, 1, 1, 1, 1],
  ![0, 1, 0, 0, 1, 1],
  ![0, 0, 0, 0, 1, 2],
  ![0, 2, 1, 2, 2, 1],
  ![0, 2, 1, 0, 1, 0]
]

theorem compression_selected_action_intertwines :
    intertwinerQ * compressionT = selectedMulDelta * intertwinerQ := by
  native_decide

theorem intertwiner_left_inverse : intertwinerQInv * intertwinerQ = 1 := by
  native_decide

theorem intertwiner_right_inverse : intertwinerQ * intertwinerQInv = 1 := by
  native_decide

theorem compression_conjugate_to_selected_mul_delta :
    compressionT = intertwinerQInv * selectedMulDelta * intertwinerQ := by
  native_decide

------------------------------------------------------------------------
-- Primitive cyclic action on the SAME F3^6 carrier.
------------------------------------------------------------------------

def matrixApply (M : Mat6) (x : Vec6) : Vec6 :=
  fun i => ∑ j : Fin 6, M i j * x j

def primitiveSeed : Vec6 := fun i => if i = 0 then 1 else 0

theorem selected_mul_delta_pow_728 : selectedMulDelta ^ 728 = 1 := by
  native_decide

theorem selected_mul_delta_no_positive_power_below_728 :
    ∀ n : Fin 727, selectedMulDelta ^ (n.1 + 1) ≠ 1 := by
  native_decide

def primitiveOrbit : Finset Vec6 :=
  (Finset.range 728).image fun n => matrixApply (selectedMulDelta ^ n) primitiveSeed

theorem primitive_orbit_card : primitiveOrbit.card = 728 := by
  native_decide

def canonicalSeedStabilizer : Finset Nat :=
  (Finset.range 728).filter fun n =>
    matrixApply (selectedMulDelta ^ n) primitiveSeed = primitiveSeed

theorem canonical_seed_stabilizer_card : canonicalSeedStabilizer.card = 1 := by
  native_decide

------------------------------------------------------------------------
-- Source/executable metadata.
------------------------------------------------------------------------

def selectedSourceWord : String := "g1 g2^-1 g1 g2 g1 g2^-1 g1 g2^-1"
def selectedSourceWordLength : Nat := 8
def selectedSourceSimilitudeMultiplier : Nat := 1
def selectedCompressionCharacteristicPolynomial : String :=
  "x^6 - x^4 + x^2 - x - 1"
def selectedGF729Modulus : String := "a^6 + a^5 + a^4 + 1"
def selectedDeltaCoordinates : List Nat := [0, 1, 0, 1, 1, 0]
def selectedDeltaMultiplicativeOrder : Nat := 728
def selectedPuncturedOrbitSize : Nat := 728
def selectedPuncturedStabilizerSize : Nat := 1

def depthSevenPrimitiveInverterWord : String :=
  "g2^-1 g1 g2^-1 g1 g2 g1 g2^-1"
def depthSevenSimilitudeMultiplier : Nat := 2
def earlierDepthFiveSourceWord : String := "g2 g1 g2^-1 g1 g2^-1"
def earlierBetaMultiplicativeOrder : Nat := 364

structure Boundary where
  atlasMatricesVendoredOnCompanionAgda : Bool
  exactCompressionSearchPaidOnCompanionProducer : Bool
  centerPreservingPrimitiveSourceWordPaidByExactProducer : Bool
  compressionDegreeSixIrreducibilityProducerPaid : Bool
  explicitCompressionMatrixPaid : Bool
  explicitGF729ActionMatrixPaid : Bool
  explicitInvertibleIntertwinerPaid : Bool
  sameSelectedGF729ActionSourceWritten : Bool
  primitiveOrder728PaidByExactProducer : Bool
  puncturedOrbit728PaidByExactProducer : Bool
  puncturedStabilizerTrivialPaidByExactProducer : Bool
  primitiveOrder728LeanSourceWritten : Bool
  puncturedOrbit728LeanSourceWritten : Bool
  puncturedStabilizerTrivialLeanSourceWritten : Bool
  leanExactHeadKernelReceiptObserved : Bool
  fullMonsterSemanticActionRecognitionPaid : Bool
  physicalMonster3BRealizationPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  atlasMatricesVendoredOnCompanionAgda := true
  exactCompressionSearchPaidOnCompanionProducer := true
  centerPreservingPrimitiveSourceWordPaidByExactProducer := true
  compressionDegreeSixIrreducibilityProducerPaid := true
  explicitCompressionMatrixPaid := true
  explicitGF729ActionMatrixPaid := true
  explicitInvertibleIntertwinerPaid := true
  sameSelectedGF729ActionSourceWritten := true
  primitiveOrder728PaidByExactProducer := true
  puncturedOrbit728PaidByExactProducer := true
  puncturedStabilizerTrivialPaidByExactProducer := true
  primitiveOrder728LeanSourceWritten := true
  puncturedOrbit728LeanSourceWritten := true
  puncturedStabilizerTrivialLeanSourceWritten := true
  leanExactHeadKernelReceiptObserved := false
  fullMonsterSemanticActionRecognitionPaid := false
  physicalMonster3BRealizationPaid := false

end Integration.Monster3BAtlasGF729SameObject
