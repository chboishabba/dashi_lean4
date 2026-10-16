import Integration.E6Mod3QuadraticBridge
import Integration.E6ProjectiveRootLineSRG
import Mathlib

/-!
# Projective quadratic strata in PG(4,3)

The standardized five-dimensional E6 mod-3 quadratic space has 243 affine
vectors, split as 1 + 80 + 90 + 72.  Projectivizing the three nonzero strata
by the canonical first-nonzero-coordinate-one convention yields

  40 + 45 + 36 = 121 = |PG(4,3)|.

This owner completes the association-graph layer for all three strata:

* Q=0: SRG(40,12,2,4)
* Q=1: SRG(45,12,3,3)
* Q=2: SRG(36,15,6,6), reusing the existing root-line owner.
-/

namespace DASHI.Integration.E6F3ProjectiveStrataSRG

open Integration.E6Mod3QuadraticBridge
open DASHI.Integration.E6ProjectiveRootLineSRG

/-- Canonical nonzero projective points on the Q=0 and Q=1 strata. -/
def QZeroLine := {z : F3Five // standardQuadratic z = 0 ∧ canonicalLineRep z}
def QOneLine := {z : F3Five // standardQuadratic z = 1 ∧ canonicalLineRep z}
abbrev QTwoLine := QTwoRootLine

instance : Fintype QZeroLine := Fintype.ofFinite _
instance : Fintype QOneLine := Fintype.ofFinite _
instance : DecidableEq QZeroLine := inferInstance
instance : DecidableEq QOneLine := inferInstance

theorem qzeroLine_card : Fintype.card QZeroLine = 40 := by
  native_decide

theorem qoneLine_card : Fintype.card QOneLine = 45 := by
  native_decide

theorem qtwoLine_card : Fintype.card QTwoLine = 36 := qtwoRootLine_card

/-- Exact projective partition of PG(4,3). -/
theorem projective_partition_121 :
    Fintype.card QZeroLine + Fintype.card QOneLine + Fintype.card QTwoLine = 121 := by
  norm_num [qzeroLine_card, qoneLine_card, qtwoLine_card]

/-- Orthogonality adjacency on each stratum. -/
def qzeroNeighbors (x : QZeroLine) : Finset QZeroLine :=
  Finset.univ.filter (fun y => y ≠ x ∧ dot5 x.1 y.1 = 0)

def qzeroCommon (x y : QZeroLine) : Finset QZeroLine :=
  Finset.univ.filter (fun z =>
    z ≠ x ∧ z ≠ y ∧ dot5 x.1 z.1 = 0 ∧ dot5 y.1 z.1 = 0)

def qoneNeighbors (x : QOneLine) : Finset QOneLine :=
  Finset.univ.filter (fun y => y ≠ x ∧ dot5 x.1 y.1 = 0)

def qoneCommon (x y : QOneLine) : Finset QOneLine :=
  Finset.univ.filter (fun z =>
    z ≠ x ∧ z ≠ y ∧ dot5 x.1 z.1 = 0 ∧ dot5 y.1 z.1 = 0)

/-- Q=0 projective graph: SRG(40,12,2,4). -/
theorem qzero_degree12 :
    ∀ x : QZeroLine, (qzeroNeighbors x).card = 12 := by
  native_decide

theorem qzero_adjacent_common2 :
    ∀ x y : QZeroLine,
      x ≠ y → dot5 x.1 y.1 = 0 → (qzeroCommon x y).card = 2 := by
  native_decide

theorem qzero_nonAdjacent_common4 :
    ∀ x y : QZeroLine,
      x ≠ y → dot5 x.1 y.1 ≠ 0 → (qzeroCommon x y).card = 4 := by
  native_decide

/-- Q=1 projective graph: SRG(45,12,3,3). -/
theorem qone_degree12 :
    ∀ x : QOneLine, (qoneNeighbors x).card = 12 := by
  native_decide

/-- Here lambda = mu = 3, so every pair of distinct vertices has three common
neighbors; adjacent/nonadjacent cases are immediate specializations. -/
theorem qone_common3 :
    ∀ x y : QOneLine, x ≠ y → (qoneCommon x y).card = 3 := by
  native_decide

theorem qone_adjacent_common3 :
    ∀ x y : QOneLine,
      x ≠ y → dot5 x.1 y.1 = 0 → (qoneCommon x y).card = 3 := by
  intro x y h _
  exact qone_common3 x y h

theorem qone_nonAdjacent_common3 :
    ∀ x y : QOneLine,
      x ≠ y → dot5 x.1 y.1 ≠ 0 → (qoneCommon x y).card = 3 := by
  intro x y h _
  exact qone_common3 x y h

structure StrataBoundary where
  projectivePartition404536Paid : Bool
  projectiveTotal121Paid : Bool
  qzeroSRG401224Paid : Bool
  qoneSRG451233Paid : Bool
  qtwoSRG361566Consumed : Bool
  qoneExceptionalRepresentationPromotedFromGraph : Bool
  deriving Repr

def strataBoundary : StrataBoundary where
  projectivePartition404536Paid := true
  projectiveTotal121Paid := true
  qzeroSRG401224Paid := true
  qoneSRG451233Paid := true
  qtwoSRG361566Consumed := true
  qoneExceptionalRepresentationPromotedFromGraph := false

end DASHI.Integration.E6F3ProjectiveStrataSRG
