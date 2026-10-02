import Mathlib
import Integration.RiemannSSP15DepthFiveRoleCodec

/-!
# Three distinct 15-way structures

This Lean mirror records the structural distinction among:
* RH/SSP15 finite indexing: 5 × 3;
* CM arithmetic partition: 5 + 9 + 1;
* Hecke/atom grammar: 7 + 7 + 1.

The latter two are authoritative Agda receipt structures; Lean mirrors their
count shapes only.  Equal total 15 does not imply same partition.
-/

namespace Integration.RiemannSSP15PartitionSeparation

open Integration.RiemannSSP15DepthFiveRoleCodec

inductive FifteenShapeKind
  | productFiveByThree
  | additiveFiveNineOne
  | additiveSevenSevenOne
  deriving DecidableEq, Repr

def rhCodecShape : FifteenShapeKind := .productFiveByThree
def cmShape : FifteenShapeKind := .additiveFiveNineOne
def heckeShape : FifteenShapeKind := .additiveSevenSevenOne

theorem rh_five_times_three_is_fifteen :
    5 * 3 = 15 := by norm_num

theorem cm_five_plus_nine_plus_one_is_fifteen :
    5 + 9 + 1 = 15 := by norm_num

theorem hecke_seven_plus_seven_plus_one_is_fifteen :
    7 + 7 + 1 = 15 := by norm_num

theorem shape_tags_pairwise_distinct :
    rhCodecShape ≠ cmShape ∧
    rhCodecShape ≠ heckeShape ∧
    cmShape ≠ heckeShape := by
  decide

inductive PromotionError
  | equalFifteenTotalsCreateSamePartition
  | rhCodecIsCMSplitting
  | rhCodecIsHeckeGrammar
  deriving DecidableEq, Repr

structure Boundary where
  rhFiveTimesThreeOwned : Bool
  cmFiveNineOneCountMirrored : Bool
  heckeSevenSevenOneCountMirrored : Bool
  shapeTagsPairwiseDistinct : Bool
  equalTotalPromotedToSamePartition : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  rhFiveTimesThreeOwned := true
  cmFiveNineOneCountMirrored := true
  heckeSevenSevenOneCountMirrored := true
  shapeTagsPairwiseDistinct := true
  equalTotalPromotedToSamePartition := false

end Integration.RiemannSSP15PartitionSeparation
