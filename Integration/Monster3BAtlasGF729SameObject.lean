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
on the literal six-dimensional F3 carrier and then independently kernel-checks
the finite primitive action: M_gamma has exact order 728, and the orbit of the
first standard basis vector has 728 distinct nonzero states with trivial
stabilizer inside the 728 powers.  No group order/cardinality coincidence is
used to create the same-action matrix weld.
-/

namespace Integration.Monster3BAtlasGF729SameObject

abbrev F3 := ZMod 3
abbrev Mat6 := Matrix (Fin 6) (Fin 6) F3
abbrev Vec6 := Fin 6 → F3

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

------------------------------------------------------------------------
-- Exact primitive cyclic action on the SAME F3^6 carrier.
------------------------------------------------------------------------

/-- Matrix action written directly to avoid introducing a second vector-space
carrier. -/
def matrixApply (M : Mat6) (x : Vec6) : Vec6 :=
  fun i => ∑ j : Fin 6, M i j * x j

/-- First standard basis vector; nonzero in the selected field chart. -/
def primitiveSeed : Vec6 := fun i => if i = 0 then 1 else 0

/-- The primitive matrix closes after exactly 728 powers. -/
theorem selected_mul_gamma_pow_728 : selectedMulGamma ^ 728 = 1 := by
  native_decide

/-- No positive exponent below 728 is the identity. -/
theorem selected_mul_gamma_no_positive_power_below_728 :
    ∀ n : Fin 727, selectedMulGamma ^ (n.1 + 1) ≠ 1 := by
  native_decide

/-- Orbit of the chosen nonzero seed under one complete 728-power cycle. -/
def primitiveOrbit : Finset Vec6 :=
  (Finset.range 728).image fun n => matrixApply (selectedMulGamma ^ n) primitiveSeed

/-- All 728 powers produce distinct states on this seed. -/
theorem primitive_orbit_card : primitiveOrbit.card = 728 := by
  native_decide

/-- Powers in one full cycle that fix the selected nonzero seed. -/
def canonicalSeedStabilizer : Finset Nat :=
  (Finset.range 728).filter fun n =>
    matrixApply (selectedMulGamma ^ n) primitiveSeed = primitiveSeed

/-- Only the identity power fixes the seed. -/
theorem canonical_seed_stabilizer_card : canonicalSeedStabilizer.card = 1 := by
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
  puncturedOrbit728ReprovedInLeanHere : Bool
  puncturedStabilizerTrivialReprovedInLeanHere : Bool
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
  primitiveOrderReprovedInLeanHere := true
  puncturedOrbit728ReprovedInLeanHere := true
  puncturedStabilizerTrivialReprovedInLeanHere := true
  fullMonsterOrbitSemanticsPaid := false
  physicalMonster3BRealizationPaid := false

end Integration.Monster3BAtlasGF729SameObject
