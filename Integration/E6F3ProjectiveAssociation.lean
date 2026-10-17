import Integration.E6F3ExteriorSquare
import Mathlib

/-!
# Projective association geometry of the F3^5 quadratic strata

Choose one representative from each antipodal pair by requiring the first
nonzero coordinate to be 1.  This gives literal finite projective carriers of
sizes 40, 45 and 36 for Q=0,1,2 respectively.

Exhaustive kernel-facing finite checks pay the orthogonality graph parameters:

* Q=0: SRG(40,12,2,4)
* Q=1: SRG(45,12,3,3)
* Q=2: SRG(36,15,6,6)

The Q=2 graph is the E6 projective root-line graph after the already-proved
E6-root/Q=2 recognition.
-/

namespace Integration.E6F3ProjectiveAssociation

open Integration.E6F3ExteriorSquare

/-- Canonical representative of an antipodal projective point: the first
nonzero coordinate is 1 rather than 2=-1. -/
def canonicalProjective (z : V5) : Bool :=
  if z 0 = 0 then
    if z 1 = 0 then
      if z 2 = 0 then
        if z 3 = 0 then
          if z 4 = 0 then false else decide (z 4 = 1)
        else decide (z 3 = 1)
      else decide (z 2 = 1)
    else decide (z 1 = 1)
  else decide (z 0 = 1)

def NullLine := {z : V5 // qStandard z = 0 ∧ canonicalProjective z = true}
def Q1Line := {z : V5 // qStandard z = 1 ∧ canonicalProjective z = true}
def Q2Line := {z : V5 // qStandard z = 2 ∧ canonicalProjective z = true}

instance : Fintype NullLine := inferInstance
instance : Fintype Q1Line := inferInstance
instance : Fintype Q2Line := inferInstance

theorem nullLine_card : Fintype.card NullLine = 40 := by
  native_decide

theorem q1Line_card : Fintype.card Q1Line = 45 := by
  native_decide

theorem q2Line_card : Fintype.card Q2Line = 36 := by
  native_decide

theorem projective_partition_121 :
    Fintype.card NullLine + Fintype.card Q1Line + Fintype.card Q2Line = 121 := by
  norm_num [nullLine_card, q1Line_card, q2Line_card]

/-- Polar bilinear form of qStandard; in characteristic 3 this dot pairing is
nondegenerate and has the same zero relation as the polarization. -/
def dot5 (x y : V5) : F3 :=
  x 0*y 0 + x 1*y 1 + x 2*y 2 + x 3*y 3 + x 4*y 4

def nullAdjacent (x y : NullLine) : Bool :=
  decide (x ≠ y ∧ dot5 x.1 y.1 = 0)

def q1Adjacent (x y : Q1Line) : Bool :=
  decide (x ≠ y ∧ dot5 x.1 y.1 = 0)

def q2Adjacent (x y : Q2Line) : Bool :=
  decide (x ≠ y ∧ dot5 x.1 y.1 = 0)

def nullDegree (x : NullLine) : Nat :=
  (Finset.univ.filter fun y : NullLine => nullAdjacent x y = true).card

def q1Degree (x : Q1Line) : Nat :=
  (Finset.univ.filter fun y : Q1Line => q1Adjacent x y = true).card

def q2Degree (x : Q2Line) : Nat :=
  (Finset.univ.filter fun y : Q2Line => q2Adjacent x y = true).card

def nullCommon (x y : NullLine) : Nat :=
  (Finset.univ.filter fun z : NullLine =>
    (nullAdjacent x z && nullAdjacent y z) = true).card

def q1Common (x y : Q1Line) : Nat :=
  (Finset.univ.filter fun z : Q1Line =>
    (q1Adjacent x z && q1Adjacent y z) = true).card

def q2Common (x y : Q2Line) : Nat :=
  (Finset.univ.filter fun z : Q2Line =>
    (q2Adjacent x z && q2Adjacent y z) = true).card

/-! ## Q=0: SRG(40,12,2,4) -/

theorem null_degree_12 : ∀ x : NullLine, nullDegree x = 12 := by
  native_decide

theorem null_adjacent_common_2 :
    ∀ x y : NullLine, nullAdjacent x y = true → nullCommon x y = 2 := by
  native_decide

theorem null_nonadjacent_common_4 :
    ∀ x y : NullLine,
      x ≠ y → nullAdjacent x y = false → nullCommon x y = 4 := by
  native_decide

/-! ## Q=1: SRG(45,12,3,3) -/

theorem q1_degree_12 : ∀ x : Q1Line, q1Degree x = 12 := by
  native_decide

theorem q1_adjacent_common_3 :
    ∀ x y : Q1Line, q1Adjacent x y = true → q1Common x y = 3 := by
  native_decide

theorem q1_nonadjacent_common_3 :
    ∀ x y : Q1Line,
      x ≠ y → q1Adjacent x y = false → q1Common x y = 3 := by
  native_decide

/-! ## Q=2: SRG(36,15,6,6), the projective E6 root-line graph -/

theorem q2_degree_15 : ∀ x : Q2Line, q2Degree x = 15 := by
  native_decide

theorem q2_adjacent_common_6 :
    ∀ x y : Q2Line, q2Adjacent x y = true → q2Common x y = 6 := by
  native_decide

theorem q2_nonadjacent_common_6 :
    ∀ x y : Q2Line,
      x ≠ y → q2Adjacent x y = false → q2Common x y = 6 := by
  native_decide

structure Boundary where
  projectiveNullCount40Paid : Bool
  projectiveQ1Count45Paid : Bool
  projectiveQ2Count36Paid : Bool
  projectivePartition121Paid : Bool
  nullSRG401224Paid : Bool
  q1SRG451233Paid : Bool
  q2SRG361566Paid : Bool
  exceptionalRepresentationInferredFromGraphParameters : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  projectiveNullCount40Paid := true
  projectiveQ1Count45Paid := true
  projectiveQ2Count36Paid := true
  projectivePartition121Paid := true
  nullSRG401224Paid := true
  q1SRG451233Paid := true
  q2SRG361566Paid := true
  exceptionalRepresentationInferredFromGraphParameters := false

end Integration.E6F3ProjectiveAssociation
