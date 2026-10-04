import Mathlib

/-!
# Balanced ternary hypercube antipodal orbit-count family

Lean mirror of the Agda target-count theorem.  This is a cardinality theorem,
not a generic quotient-groupoid construction.

Define the number of nonzero antipodal pairs recursively by

  P 0       = 0
  P (n + 1) = 1 + 3 * P n.

Then O n = 1 + P n is the number of global-sign orbits on a ternary n-cube,
with the unique all-zero fixed state separated from the paired nonzero states.
The primary division-free identities are

  3^n = 1 + 2 * P n
  2 * O n = 3^n + 1.
-/

namespace Integration.BalancedTernaryHypercubeAntipodalOrbitCount

def antipodalPairCount : Nat → Nat
  | 0 => 0
  | n + 1 => 1 + 3 * antipodalPairCount n

def antipodalOrbitCount (n : Nat) : Nat :=
  1 + antipodalPairCount n

def ternaryStateCount (n : Nat) : Nat :=
  3 ^ n

theorem ternary_state_split_exact (n : Nat) :
    ternaryStateCount n = 1 + 2 * antipodalPairCount n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [ternaryStateCount, Nat.pow_succ, antipodalPairCount] at ih ⊢
      omega

theorem double_orbit_count_exact (n : Nat) :
    2 * antipodalOrbitCount n = ternaryStateCount n + 1 := by
  rw [ternary_state_split_exact]
  simp [antipodalOrbitCount]
  omega

theorem pair_count_one : antipodalPairCount 1 = 1 := rfl
theorem pair_count_two : antipodalPairCount 2 = 4 := rfl
theorem pair_count_three : antipodalPairCount 3 = 13 := rfl

theorem orbit_count_one : antipodalOrbitCount 1 = 2 := rfl
theorem orbit_count_two : antipodalOrbitCount 2 = 5 := rfl
theorem orbit_count_three : antipodalOrbitCount 3 = 14 := rfl

theorem p3_target_count_pattern :
    antipodalOrbitCount 1 = 2 := orbit_count_one

theorem p2_five_orbit_base_pattern :
    antipodalOrbitCount 2 = 5 := orbit_count_two

theorem p2_retained_binary_sheet_pattern :
    2 * antipodalOrbitCount 2 = 10 := by decide

inductive PromotionError
  | countConstructsGenericActionGroupoid
  | countIdentifiesArithmeticResidualSource
  | fibonacciAdjacencyProvesArithmeticRecognition
  deriving DecidableEq, Repr

structure Boundary where
  fixedPlusPairedCountTheoremProved : Bool
  divisionFreeOrbitFormulaProved : Bool
  n1OrbitCountTwoProved : Bool
  n2OrbitCountFiveProved : Bool
  n3OrbitCountFourteenProved : Bool
  p2RetainedTwoTimesFiveCountProved : Bool
  genericActionGroupoidConstructedHere : Bool
  arithmeticResidualSourceIdentifiedHere : Bool
  fibonacciAdjacencyPromotedToArithmeticRecognition : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  fixedPlusPairedCountTheoremProved := true
  divisionFreeOrbitFormulaProved := true
  n1OrbitCountTwoProved := true
  n2OrbitCountFiveProved := true
  n3OrbitCountFourteenProved := true
  p2RetainedTwoTimesFiveCountProved := true
  genericActionGroupoidConstructedHere := false
  arithmeticResidualSourceIdentifiedHere := false
  fibonacciAdjacencyPromotedToArithmeticRecognition := false

end Integration.BalancedTernaryHypercubeAntipodalOrbitCount
