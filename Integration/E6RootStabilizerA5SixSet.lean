import Integration.E6F3GeneratedGroupClosure
import Integration.E6Minuscule27SchlafliRecognition
import Mathlib

/-!
# E6 root stabilizer: explicit A5 subsystem and six-object action

The generated five-dimensional E6 image already has order 51,840 and a selected
root stabilizer of order 720.  Order alone was deliberately not promoted to an
`S6` recognition.

This owner supplies the missing representation-theoretic mechanism on the E6
minuscule orbit.

Choose the simple root alpha0.  The roots orthogonal to alpha0 contain the A5
simple system

  beta -- alpha1 -- alpha3 -- alpha4 -- alpha5

where beta is the negative highest root with simple-root coefficients
`(-1,-2,-2,-3,-2,-1)` in the repository numbering.  The omega5 minuscule orbit
splits by alpha0 pairing as

  6 + 15 + 6.

On the +1 six-set, the five A5 root reflections are five transpositions forming
a path on six vertices.  Exact finite closure gives all 720 permutations of the
six-set.  This pays an explicit `W(A5) = S6` six-object action model rather than
inferring it from the number 720.

The final same-object identification with the *particular* matrix stabilizer of
the independently selected Q=2 seed remains a separate conjugacy/intertwiner
receipt; equal order is not used to manufacture that weld.
-/

namespace Integration.E6RootStabilizerA5SixSet

open Integration.E6Mod3WeylAction
open Integration.E6F3GeneratedGroupClosure
open Integration.E6Minuscule27LiteralRecognition
open Integration.E6Minuscule27SchlafliRecognition

abbrev RootCoeff := Fin 6 → Int

/-- Simple-root coefficient vector for the chosen alpha0. -/
def alpha0Coeff : RootCoeff := ![1,0,0,0,0,0]

inductive A5Simple
  | beta | a1 | a3 | a4 | a5
  deriving DecidableEq, Repr, Fintype

/-- A5 simple roots inside the E6 roots orthogonal to alpha0. -/
def a5RootCoeff : A5Simple → RootCoeff
  | .beta => ![-1,-2,-2,-3,-2,-1]
  | .a1 => ![0,1,0,0,0,0]
  | .a3 => ![0,0,0,1,0,0]
  | .a4 => ![0,0,0,0,1,0]
  | .a5 => ![0,0,0,0,0,1]

/-- E6 root inner product in simple-root coordinates. -/
def rootInner (x y : RootCoeff) : Int :=
  ∑ i : Fin 6, ∑ j : Fin 6, x i * cartanEntry i j * y j


def a5Adjacent : A5Simple → A5Simple → Bool
  | .beta, .a1 | .a1, .beta => true
  | .a1, .a3 | .a3, .a1 => true
  | .a3, .a4 | .a4, .a3 => true
  | .a4, .a5 | .a5, .a4 => true
  | _, _ => false

 theorem a5_cartan_gram :
    ∀ r s,
      rootInner (a5RootCoeff r) (a5RootCoeff s) =
        if r = s then 2 else if a5Adjacent r s then -1 else 0 := by
  native_decide

 theorem a5_roots_orthogonal_to_alpha0 :
    ∀ r, rootInner alpha0Coeff (a5RootCoeff r) = 0 := by
  native_decide

/-- Dynkin-label vector of a root from its simple-root coefficients. -/
def rootDynkinLabel (c : RootCoeff) : DynkinLabel :=
  fun j => ∑ i : Fin 6, c i * cartanEntry j i

/-- Pairing of a weight (Dynkin labels) with a simply-laced root. -/
def weightRootPairing (lambda : DynkinLabel) (c : RootCoeff) : Int :=
  ∑ i : Fin 6, c i * lambda i

/-- Reflection in an arbitrary E6 root, expressed on Dynkin labels. -/
def reflectAcrossRoot (c : RootCoeff) (lambda : DynkinLabel) : DynkinLabel :=
  fun j => lambda j - weightRootPairing lambda c * rootDynkinLabel c j

/-- The minuscule orbit decomposes as 6 + 15 + 6 by alpha0 pairing, which in
Dynkin coordinates is simply the zeroth label. -/
def Omega5Plus := {w : Omega5Weight // w.1 0 = 1}
def Omega5Zero := {w : Omega5Weight // w.1 0 = 0}
def Omega5Minus := {w : Omega5Weight // w.1 0 = -1}

instance : Fintype Omega5Plus := inferInstance
instance : Fintype Omega5Zero := inferInstance
instance : Fintype Omega5Minus := inferInstance

 theorem omega5_plus_card : Fintype.card Omega5Plus = 6 := by native_decide
 theorem omega5_zero_card : Fintype.card Omega5Zero = 15 := by native_decide
 theorem omega5_minus_card : Fintype.card Omega5Minus = 6 := by native_decide
 theorem omega5_six_fifteen_six :
    Fintype.card Omega5Plus + Fintype.card Omega5Zero + Fintype.card Omega5Minus = 27 := by
  norm_num [omega5_plus_card, omega5_zero_card, omega5_minus_card]

/-- Canonical enumeration of the +1 six-set. -/
def plusFaceWeight : Fin 6 → DynkinLabel :=
  ![ ![1,-1,-1,1,0,0],
     ![1,0,-1,0,0,0],
     ![1,0,0,-1,1,0],
     ![1,0,0,0,-1,1],
     ![1,0,0,0,0,-1],
     ![1,1,-1,0,0,0] ]

 theorem plus_face_weight_in_omega5 :
    ∀ i, plusFaceWeight i ∈ minusculeOmega5Set := by native_decide

 theorem plus_face_weight_coord : ∀ i, plusFaceWeight i 0 = 1 := by native_decide


def plusFace (i : Fin 6) : Omega5Plus :=
  ⟨⟨plusFaceWeight i, plus_face_weight_in_omega5 i⟩, plus_face_weight_coord i⟩

 theorem plus_face_bijective : Function.Bijective plusFace := by native_decide

/-- Five explicit transpositions induced by the A5 simple-root reflections on
the +1 six-set. -/
def swapTable (a b : Fin 6) (i : Fin 6) : Fin 6 :=
  if i = a then b else if i = b then a else i


def a5FaceTable : A5Simple → Fin 6 → Fin 6
  | .beta => swapTable 1 5
  | .a1 => swapTable 0 5
  | .a3 => swapTable 0 2
  | .a4 => swapTable 2 3
  | .a5 => swapTable 3 4

 theorem a5_reflections_act_by_the_six_face_tables :
    ∀ r i,
      reflectAcrossRoot (a5RootCoeff r) (plusFaceWeight i) =
        plusFaceWeight (a5FaceTable r i) := by
  native_decide

 theorem a5_reflections_preserve_alpha0_layer :
    ∀ r i,
      (reflectAcrossRoot (a5RootCoeff r) (plusFaceWeight i)) 0 = 1 := by
  native_decide

/-! ## Exact finite closure on the six-set -/

abbrev Table6 := Fin 6 → Fin 6


def tableId : Table6 := fun i => i

def tableComp (f g : Table6) : Table6 := fun i => f (g i)


def expandTables (S : Finset Table6) : Finset Table6 :=
  S ∪ S.image (tableComp (a5FaceTable .beta)) ∪
      S.image (tableComp (a5FaceTable .a1)) ∪
      S.image (tableComp (a5FaceTable .a3)) ∪
      S.image (tableComp (a5FaceTable .a4)) ∪
      S.image (tableComp (a5FaceTable .a5))


def tableOrbitN : Nat → Finset Table6
  | 0 => {tableId}
  | n + 1 => expandTables (tableOrbitN n)

/-- A path of five adjacent transpositions on six letters has maximal Coxeter
length 15, so round 15 reaches the full symmetric group. -/
def a5GeneratedTables : Finset Table6 := tableOrbitN 15

 theorem a5_generated_table_card : a5GeneratedTables.card = 720 := by
  native_decide

 theorem a5_generated_table_stable : tableOrbitN 16 = a5GeneratedTables := by
  native_decide

/-- Decidable table-level model of `Sym(6)`. -/
def isPermutationTable (f : Table6) : Bool :=
  decide (∀ i j, f i = f j → i = j)


def allSym6Tables : Finset Table6 :=
  Finset.univ.filter fun f => isPermutationTable f = true

 theorem all_sym6_table_card : allSym6Tables.card = 720 := by
  native_decide

 theorem a5_generated_tables_are_exactly_sym6 :
    a5GeneratedTables = allSym6Tables := by
  native_decide

/-- Existing independent matrix stabilizer has the same exact order.  This is a
checksum, not the missing same-object conjugacy map. -/
theorem q2_matrix_stabilizer_order_matches_sym6 :
    q2SeedStabilizer.card = allSym6Tables.card := by
  norm_num [q2_seed_stabilizer_card, all_sym6_table_card]

inductive SelectedQ2MatrixStabilizerSameObjectAsA5SixAction : Prop

theorem order_match_does_not_manufacture_selected_stabilizer_weld :
    ¬ SelectedQ2MatrixStabilizerSameObjectAsA5SixAction := by
  intro h
  cases h

structure Boundary where
  explicitA5SubsystemOrthogonalToRootPaid : Bool
  minusculeSixFifteenSixPaid : Bool
  fiveA5ReflectionsActOnSixSetPaid : Bool
  sixSetGeneratedActionOrder720Paid : Bool
  sixSetGeneratedActionEqualsAllSym6Paid : Bool
  independentQ2MatrixStabilizerOrder720Consumed : Bool
  selectedQ2MatrixStabilizerSameObjectWeldPaid : Bool
  deriving Repr


def canonicalBoundary : Boundary where
  explicitA5SubsystemOrthogonalToRootPaid := true
  minusculeSixFifteenSixPaid := true
  fiveA5ReflectionsActOnSixSetPaid := true
  sixSetGeneratedActionOrder720Paid := true
  sixSetGeneratedActionEqualsAllSym6Paid := true
  independentQ2MatrixStabilizerOrder720Consumed := true
  selectedQ2MatrixStabilizerSameObjectWeldPaid := false

end Integration.E6RootStabilizerA5SixSet
