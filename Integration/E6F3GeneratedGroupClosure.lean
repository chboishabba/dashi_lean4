import Integration.E6F3OrbitTransitivity
import Mathlib

/-!
# Kernel-facing closure of the six E6 mod-3 generators

The preceding owners pay the six simple-reflection formulas, the Coxeter
relations, the global quotient/isometry intertwiner, and transitivity on the
80/90/72 quadratic strata.  Local exact enumeration also found 51,840 distinct
five-dimensional transformations, but that count was deliberately retained as
a diagnostic.

This owner moves that remaining finite computation into Lean.  A transformation
is represented by the images of the five standard basis vectors.  Starting at
the identity and closing under left multiplication by the six existing E6
simple generators reaches 51,840 distinct linear transformations; the next
closure round adds nothing.  Filtering this exact generated image by the
stabilizer of the selected Q=2 seed gives 720 transformations.

The order 720 is the expected root-stabilizer order `|W(A5)| = |S6|`, but this
file does not promote equality of orders to an abstract-group isomorphism.  A
literal S6 recognition still requires an explicit six-object action or another
same-action group equivalence.
-/

namespace Integration.E6F3GeneratedGroupClosure

open Integration.E6F3ExteriorSquare
open Integration.E6Mod3WeylAction
open Integration.E6PGSp4ExteriorSquare
open Integration.E6F3OrbitTransitivity

/-- A five-dimensional F3 linear transformation, stored as its 5x5 matrix. -/
abbrev Mat5 := Fin 5 → Fin 5 → F3

/-- Standard basis vector. -/
def basis5 (j : Fin 5) : V5 := fun i => if i = j then 1 else 0

/-- Apply a matrix to a five-vector. -/
def matrixApply (M : Mat5) (x : V5) : V5 :=
  fun i => ∑ j : Fin 5, M i j * x j

/-- Composition matrix `A ∘ B`. -/
def matrixComp (A B : Mat5) : Mat5 :=
  fun i j => ∑ k : Fin 5, A i k * B k j

/-- Identity matrix. -/
def identityMatrix : Mat5 :=
  fun i j => if i = j then 1 else 0

/-- Matrix of one of the six already-formalized E6 simple reflections. -/
def generatorMatrix (s : E6SimpleReflection) : Mat5 :=
  fun i j => reflectV5 s (basis5 j) i

/-- The matrix encoding agrees with the existing reflection action on every one
of the 243 vectors. -/
theorem generator_matrix_action_agrees :
    ∀ s x, matrixApply (generatorMatrix s) x = reflectV5 s x := by
  native_decide

/-- One closure step under left multiplication by all six E6 generators. -/
def expandMatrices (S : Finset Mat5) : Finset Mat5 :=
  S ∪ S.image (matrixComp (generatorMatrix .s0)) ∪
      S.image (matrixComp (generatorMatrix .s1)) ∪
      S.image (matrixComp (generatorMatrix .s2)) ∪
      S.image (matrixComp (generatorMatrix .s3)) ∪
      S.image (matrixComp (generatorMatrix .s4)) ∪
      S.image (matrixComp (generatorMatrix .s5))

/-- Bounded word closure from the identity. -/
def matrixOrbitN : Nat → Finset Mat5
  | 0 => {identityMatrix}
  | n + 1 => expandMatrices (matrixOrbitN n)

/-- Exact closure of the six-generator image.  Local preflight found maximal
word distance 36; Lean checks both the cardinality and the next-round fixed
point below. -/
def generatedMatrixSet : Finset Mat5 := matrixOrbitN 36

/-- The generated five-dimensional E6 image contains exactly 51,840 distinct
linear transformations. -/
theorem generated_matrix_set_card : generatedMatrixSet.card = 51840 := by
  native_decide

/-- Round 36 is already closed under another application of all six generators. -/
theorem generated_matrix_set_stable : matrixOrbitN 37 = generatedMatrixSet := by
  native_decide

/-- Re-express the fixed-point result directly in terms of the closure operator. -/
theorem generated_expand_fixed : expandMatrices generatedMatrixSet = generatedMatrixSet := by
  simpa [generatedMatrixSet, matrixOrbitN] using generated_matrix_set_stable

/-- Every simple generator preserves the exact generated set. -/
theorem generated_closed_under_simple_left_mul :
    ∀ s M, M ∈ generatedMatrixSet →
      matrixComp (generatorMatrix s) M ∈ generatedMatrixSet := by
  intro s M hM
  have hfix := generated_expand_fixed
  have himage : matrixComp (generatorMatrix s) M ∈ expandMatrices generatedMatrixSet := by
    cases s <;> simp [expandMatrices, hM]
  rw [hfix] at himage
  exact himage

/-- The selected norm-two/root seed used by the already-paid transitivity owner. -/
def q2SeedVector : V5 := q2Seed.1

/-- Exact stabilizer of that root inside the generated 51,840-element image. -/
def q2SeedStabilizer : Finset Mat5 :=
  generatedMatrixSet.filter fun M => matrixApply M q2SeedVector = q2SeedVector

/-- The selected E6 root stabilizer has order 720. -/
theorem q2_seed_stabilizer_card : q2SeedStabilizer.card = 720 := by
  native_decide

/-- Exact orbit-stabilizer checksum for the 72-root orbit. -/
theorem generated_order_eq_root_orbit_times_stabilizer :
    generatedMatrixSet.card = 72 * q2SeedStabilizer.card := by
  norm_num [generated_matrix_set_card, q2_seed_stabilizer_card]

/-- Order-level A5/S6 signature.  This deliberately records only the numerical
consequence until an explicit six-object action is supplied. -/
theorem q2_stabilizer_order_is_six_factorial :
    q2SeedStabilizer.card = Nat.factorial 6 := by
  norm_num [q2_seed_stabilizer_card, Nat.factorial]

inductive StabilizerIdentifiedAsS6ByOrderAlone : Prop
inductive FullPGSp4EqualsWE6PaidHere : Prop

 theorem stabilizer_not_promoted_to_s6_from_order_alone :
    ¬ StabilizerIdentifiedAsS6ByOrderAlone := by
  intro h
  cases h

 theorem full_pgsp4_equality_not_manufactured_here :
    ¬ FullPGSp4EqualsWE6PaidHere := by
  intro h
  cases h

structure Boundary where
  generatorMatricesTyped : Bool
  generatorActionAgreementAll243Paid : Bool
  generatedImageOrder51840Paid : Bool
  generatedImageClosureFixedPointPaid : Bool
  generatedImageClosedUnderSixGeneratorsPaid : Bool
  q2RootStabilizerOrder720Paid : Bool
  orbitStabilizerChecksumPaid : Bool
  stabilizerIdentifiedAsS6ByOrderAlone : Bool
  fullPGSp4EqualsWE6PaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  generatorMatricesTyped := true
  generatorActionAgreementAll243Paid := true
  generatedImageOrder51840Paid := true
  generatedImageClosureFixedPointPaid := true
  generatedImageClosedUnderSixGeneratorsPaid := true
  q2RootStabilizerOrder720Paid := true
  orbitStabilizerChecksumPaid := true
  stabilizerIdentifiedAsS6ByOrderAlone := false
  fullPGSp4EqualsWE6PaidHere := false

end Integration.E6F3GeneratedGroupClosure
