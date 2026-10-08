import Integration.E6RootStabilizerA5SixSet
import Integration.Ternary27A5SixFaceReorganisation
import Mathlib

/-!
# Selected Q2 matrix stabilizer <-> direct six-face S6 same-object weld

The preceding owners independently established:

* the generated E6 mod-3 image has order 51,840;
* the repository's selected Q=2 seed has matrix stabilizer of order 720;
* the A5 subsystem orthogonal to the simple root alpha0 acts on six faces as all S6;
* the same five A5 reflections act directly on the raw ternary-27 hypervoxel.

This owner closes the remaining equal-order firewall without choosing an arbitrary
720-element bijection.  It builds the five A5 reflection matrices from their
actual reduced roots and closes matrix/permutation PAIRS synchronously.  The
result has 720 pairs, with 720 distinct matrices and 720 distinct six-permutation
tables.  Its matrix projection is exactly the alpha0 stabilizer and its table
projection is exactly S6.

The older repository Q2 seed `(1,1,0,0,0)` is then transported to alpha0 by an
explicit five-simple-reflection matrix.  Conjugation by that transporter maps the
old selected stabilizer exactly onto the alpha0 stabilizer.  Thus the original
selected matrix stabilizer is same-object with the direct face-S6 action through
an explicit conjugacy plus the synchronized closure graph.
-/

namespace Integration.E6SelectedStabilizerFaceSameObject

open Integration.E6F3ExteriorSquare
open Integration.E6Mod3WeylAction
open Integration.E6F3GeneratedGroupClosure
open Integration.E6RootStabilizerA5SixSet
open Integration.Ternary27A5SixFaceReorganisation

/-- The standardized mod-3 image of the simple root alpha0. -/
def alpha0Vector : V5 := ![0,0,0,2,1]

theorem alpha0_has_qtwo : qStandard alpha0Vector = 2 := by native_decide

/-- Reflection matrix in a Q=2 root for the standard diagonal form.
Over F3, `s_r(x)=x-(x dot r)r` when `q(r)=2`. -/
def reflectionMatrixFromRoot (r : V5) : Mat5 :=
  fun i j => (if i = j then 1 else 0) - r j * r i

/-- The five A5 roots after the already-paid E6 radical quotient/isometry. -/
def a5RootV5 : A5Simple → V5
  | .beta => ![0,0,0,2,2]
  | .a1   => ![2,2,2,2,2]
  | .a3   => ![2,2,0,0,0]
  | .a4   => ![1,0,2,0,0]
  | .a5   => ![2,1,0,0,0]

/-- Matrix realization of those five A5 root reflections. -/
def a5Matrix (r : A5Simple) : Mat5 := reflectionMatrixFromRoot (a5RootV5 r)

/-- Four A5 generators are literal E6 simple generators; beta is the reflected
negative-highest-root generator.  All five belong to the already generated E6
matrix image. -/
theorem a5_matrices_lie_in_generated_image :
    ∀ r, a5Matrix r ∈ generatedMatrixSet := by
  native_decide

/-- The five matrices fix alpha0, as required for the root stabilizer. -/
theorem a5_matrices_fix_alpha0 :
    ∀ r, matrixApply (a5Matrix r) alpha0Vector = alpha0Vector := by
  native_decide

/-- Stabilizer of the actual alpha0 vector inside the already-paid 51,840 image. -/
def alpha0Stabilizer : Finset Mat5 :=
  generatedMatrixSet.filter fun M => matrixApply M alpha0Vector = alpha0Vector

theorem alpha0_stabilizer_card : alpha0Stabilizer.card = 720 := by
  native_decide

/-! ## Synchronized A5 closure: matrices and six-face tables are one graph. -/

abbrev SyncPair := Mat5 × Table6

def syncId : SyncPair := (identityMatrix, tableId)

def syncLeftMultiply (r : A5Simple) (x : SyncPair) : SyncPair :=
  (matrixComp (a5Matrix r) x.1, tableComp (a5FaceTable r) x.2)


def expandSync (S : Finset SyncPair) : Finset SyncPair :=
  S ∪ S.image (syncLeftMultiply .beta) ∪
      S.image (syncLeftMultiply .a1) ∪
      S.image (syncLeftMultiply .a3) ∪
      S.image (syncLeftMultiply .a4) ∪
      S.image (syncLeftMultiply .a5)


def syncOrbitN : Nat → Finset SyncPair
  | 0 => {syncId}
  | n + 1 => expandSync (syncOrbitN n)

/-- Maximal Coxeter length in S6 is 15, so this is the full synchronized graph. -/
def synchronizedA5Graph : Finset SyncPair := syncOrbitN 15


theorem synchronized_graph_card : synchronizedA5Graph.card = 720 := by
  native_decide

theorem synchronized_graph_stable : syncOrbitN 16 = synchronizedA5Graph := by
  native_decide


def synchronizedMatrices : Finset Mat5 := synchronizedA5Graph.image Prod.fst

def synchronizedTables : Finset Table6 := synchronizedA5Graph.image Prod.snd

/-- The synchronized matrix projection is not merely a 720-set: it is exactly
the alpha0 stabilizer cut out of the 51,840-element E6 image. -/
theorem synchronized_matrices_eq_alpha0_stabilizer :
    synchronizedMatrices = alpha0Stabilizer := by
  native_decide

/-- The synchronized table projection is exactly all six permutations. -/
theorem synchronized_tables_eq_sym6 : synchronizedTables = allSym6Tables := by
  native_decide

/-- No two synchronized pairs with the same matrix carry different face actions. -/
theorem synchronized_matrix_determines_table :
    ∀ a b, a ∈ synchronizedA5Graph → b ∈ synchronizedA5Graph →
      a.1 = b.1 → a.2 = b.2 := by
  native_decide

/-- Conversely the faithful six-face action determines the stabilizer matrix. -/
theorem synchronized_table_determines_matrix :
    ∀ a b, a ∈ synchronizedA5Graph → b ∈ synchronizedA5Graph →
      a.2 = b.2 → a.1 = b.1 := by
  native_decide

/-- Generator-level same-object checksum: each A5 matrix is paired with the
already-paid direct six-face permutation, not with a fitted lookup table. -/
theorem each_a5_generator_pair_occurs :
    ∀ r, (a5Matrix r, a5FaceTable r) ∈ synchronizedA5Graph := by
  native_decide

/-! ## Conjugate the repository's older q2 seed to alpha0. -/

/-- Explicit transporter found inside the generated image.  It is the matrix of
application word `s2,s0,s3,s2,s0` from the old q2 seed to alpha0. -/
def seedToAlpha0 : Mat5 :=
  ![ ![2,1,0,2,1],
     ![1,2,0,2,1],
     ![0,0,2,0,0],
     ![1,1,0,2,2],
     ![2,2,0,2,2] ]

/-- Orthogonal inverse, here written explicitly as the transpose. -/
def alpha0ToSeed : Mat5 := fun i j => seedToAlpha0 j i


theorem seed_to_alpha0_in_generated_image : seedToAlpha0 ∈ generatedMatrixSet := by
  native_decide

theorem transporter_maps_old_seed_to_alpha0 :
    matrixApply seedToAlpha0 q2SeedVector = alpha0Vector := by
  native_decide

theorem transporter_inverse_left :
    matrixComp alpha0ToSeed seedToAlpha0 = identityMatrix := by
  native_decide

theorem transporter_inverse_right :
    matrixComp seedToAlpha0 alpha0ToSeed = identityMatrix := by
  native_decide

/-- Conjugation sends the old selected-root stabilizer into the alpha0 chart. -/
def conjugateSeedToAlpha0 (M : Mat5) : Mat5 :=
  matrixComp seedToAlpha0 (matrixComp M alpha0ToSeed)

/-- This is the literal selected-stabilizer conjugacy, not an order argument. -/
theorem conjugated_old_stabilizer_eq_alpha0_stabilizer :
    q2SeedStabilizer.image conjugateSeedToAlpha0 = alpha0Stabilizer := by
  native_decide

/-- Final same-object relation between an old selected-stabilizer matrix and a
six-face permutation.  The bridge is explicit conjugation followed by membership
in the synchronized A5 graph. -/
def SelectedMatrixFaceRelated (M : Mat5) (p : Table6) : Prop :=
  M ∈ q2SeedStabilizer ∧
  p ∈ allSym6Tables ∧
  (conjugateSeedToAlpha0 M, p) ∈ synchronizedA5Graph

/-- Every selected Q2 stabilizer matrix has a unique direct six-face action. -/
theorem selected_matrix_has_unique_face_table :
    ∀ M, M ∈ q2SeedStabilizer → ∃! p, SelectedMatrixFaceRelated M p := by
  native_decide

/-- Every six-face permutation comes from a unique selected Q2 stabilizer matrix. -/
theorem every_face_table_has_unique_selected_matrix :
    ∀ p, p ∈ allSym6Tables → ∃! M, SelectedMatrixFaceRelated M p := by
  native_decide

structure Boundary where
  alpha0RootTyped : Bool
  a5RootMatricesTyped : Bool
  a5MatricesInsideGeneratedE6Paid : Bool
  alpha0StabilizerOrder720Paid : Bool
  synchronizedClosure720Paid : Bool
  synchronizedMatrixProjectionExactPaid : Bool
  synchronizedFaceProjectionExactPaid : Bool
  synchronizedGraphIsBijectiveBothWaysPaid : Bool
  oldSeedToAlpha0TransporterPaid : Bool
  oldSelectedStabilizerConjugacyPaid : Bool
  selectedMatrixFaceSameObjectPaid : Bool
  deriving Repr


def canonicalBoundary : Boundary where
  alpha0RootTyped := true
  a5RootMatricesTyped := true
  a5MatricesInsideGeneratedE6Paid := true
  alpha0StabilizerOrder720Paid := true
  synchronizedClosure720Paid := true
  synchronizedMatrixProjectionExactPaid := true
  synchronizedFaceProjectionExactPaid := true
  synchronizedGraphIsBijectiveBothWaysPaid := true
  oldSeedToAlpha0TransporterPaid := true
  oldSelectedStabilizerConjugacyPaid := true
  selectedMatrixFaceSameObjectPaid := true

end Integration.E6SelectedStabilizerFaceSameObject
