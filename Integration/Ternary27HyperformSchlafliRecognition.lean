import Integration.E6Minuscule27SameObject
import Mathlib

/-!
# Typed ternary-27 hypervoxel chart -> Schlaefli/minuscule 27

The additive `F3^3` Cayley no-go only forgets too much structure.  This owner
constructs an explicit *absolute* 27-point chart from the typed 3x3x3
hypervoxel anatomy used by the Agda hyperfabric owners.

The chart uses the canonical Schlaefli `6 + 15 + 6` presentation:

* six oriented cube faces;
* fifteen unordered pairs of those six faces;
* a second oriented six, interpreted as the dual/right face copy.

The raw ternary points are assigned by existing hypervoxel provenance:

* the six face-centres -> the left six;
* the twelve edge-centres -> the twelve non-opposite face pairs;
* the origin and the two named diagonal corners -> the three opposite pairs;
* the six remaining corners -> the right six, indexed by their unique minority
  signed coordinate.

Thus the only non-additive ingredient is absolute face/stratum provenance.  No
translation-invariant relation is used.

The resulting graph is kernel-facing finite data:

  SRG(27,16,10,8)

with complement

  SRG(27,10,1,5).

A second exact table identifies the `6+15+6` labels with the already-paid E6
omega5 minuscule weights, and the two adjacency relations agree pointwise.
Consequently the structured ternary 27 is relation-level same-object with the
E6 minuscule/Schlaefli 27.  This does NOT claim that the pre-existing additive
translation action is the E6 action, nor does it manufacture an Albert product,
cubic norm or F4 action.
-/

namespace Integration.Ternary27HyperformSchlafliRecognition

open Integration.E6Minuscule27LiteralRecognition
open Integration.E6Minuscule27SchlafliRecognition
open Integration.E6Minuscule27SameObject

inductive Trit
  | neg | zero | pos
  deriving DecidableEq, Repr, Fintype

structure Ternary27Point where
  x : Trit
  y : Trit
  z : Trit
  deriving DecidableEq, Repr, Fintype

inductive Face6
  | xNeg | xPos | yNeg | yPos | zNeg | zPos
  deriving DecidableEq, Repr, Fintype

abbrev Pair15 := Fin 15

/-- The 15 unordered pairs of the six oriented face labels.
The first three are the opposite-face pairs. -/
def pairEndpoints : Pair15 → Face6 × Face6 :=
  ![ (.xNeg,.xPos), (.yNeg,.yPos), (.zNeg,.zPos),
     (.xNeg,.yNeg), (.xNeg,.yPos), (.xPos,.yNeg), (.xPos,.yPos),
     (.xNeg,.zNeg), (.xNeg,.zPos), (.xPos,.zNeg), (.xPos,.zPos),
     (.yNeg,.zNeg), (.yNeg,.zPos), (.yPos,.zNeg), (.yPos,.zPos) ]

def pairContains (p : Pair15) (f : Face6) : Bool :=
  let e := pairEndpoints p
  decide (f = e.1 ∨ f = e.2)

def pairDisjoint (p q : Pair15) : Bool :=
  let a := pairEndpoints p
  let b := pairEndpoints q
  decide (a.1 ≠ b.1 ∧ a.1 ≠ b.2 ∧ a.2 ≠ b.1 ∧ a.2 ≠ b.2)

inductive SchlafliLabel
  | left : Face6 → SchlafliLabel
  | middle : Pair15 → SchlafliLabel
  | right : Face6 → SchlafliLabel
  deriving DecidableEq, Repr, Fintype

/-- Absolute typed hypervoxel chart.  Notice that it is not a homomorphism from
`F3^3`: it remembers face-centre / edge-centre / corner provenance. -/
def pointToLabel : Ternary27Point → SchlafliLabel
  | ⟨.neg, .neg, .neg⟩ => .middle 1
  | ⟨.neg, .neg, .zero⟩ => .middle 3
  | ⟨.neg, .neg, .pos⟩ => .right .zPos
  | ⟨.neg, .zero, .neg⟩ => .middle 7
  | ⟨.neg, .zero, .zero⟩ => .left .xNeg
  | ⟨.neg, .zero, .pos⟩ => .middle 8
  | ⟨.neg, .pos, .neg⟩ => .right .yPos
  | ⟨.neg, .pos, .zero⟩ => .middle 4
  | ⟨.neg, .pos, .pos⟩ => .right .xNeg
  | ⟨.zero, .neg, .neg⟩ => .middle 11
  | ⟨.zero, .neg, .zero⟩ => .left .yNeg
  | ⟨.zero, .neg, .pos⟩ => .middle 12
  | ⟨.zero, .zero, .neg⟩ => .left .zNeg
  | ⟨.zero, .zero, .zero⟩ => .middle 0
  | ⟨.zero, .zero, .pos⟩ => .left .zPos
  | ⟨.zero, .pos, .neg⟩ => .middle 13
  | ⟨.zero, .pos, .zero⟩ => .left .yPos
  | ⟨.zero, .pos, .pos⟩ => .middle 14
  | ⟨.pos, .neg, .neg⟩ => .right .xPos
  | ⟨.pos, .neg, .zero⟩ => .middle 5
  | ⟨.pos, .neg, .pos⟩ => .right .yNeg
  | ⟨.pos, .zero, .neg⟩ => .middle 9
  | ⟨.pos, .zero, .zero⟩ => .left .xPos
  | ⟨.pos, .zero, .pos⟩ => .middle 10
  | ⟨.pos, .pos, .neg⟩ => .right .zNeg
  | ⟨.pos, .pos, .zero⟩ => .middle 6
  | ⟨.pos, .pos, .pos⟩ => .middle 2


def leftPoint : Face6 → Ternary27Point
  | .xNeg => ⟨.neg,.zero,.zero⟩
  | .xPos => ⟨.pos,.zero,.zero⟩
  | .yNeg => ⟨.zero,.neg,.zero⟩
  | .yPos => ⟨.zero,.pos,.zero⟩
  | .zNeg => ⟨.zero,.zero,.neg⟩
  | .zPos => ⟨.zero,.zero,.pos⟩


def rightPoint : Face6 → Ternary27Point
  | .xNeg => ⟨.neg,.pos,.pos⟩
  | .xPos => ⟨.pos,.neg,.neg⟩
  | .yNeg => ⟨.pos,.neg,.pos⟩
  | .yPos => ⟨.neg,.pos,.neg⟩
  | .zNeg => ⟨.pos,.pos,.neg⟩
  | .zPos => ⟨.neg,.neg,.pos⟩


def middlePoint : Pair15 → Ternary27Point :=
  ![ ⟨.zero,.zero,.zero⟩,
     ⟨.neg,.neg,.neg⟩,
     ⟨.pos,.pos,.pos⟩,
     ⟨.neg,.neg,.zero⟩,
     ⟨.neg,.pos,.zero⟩,
     ⟨.pos,.neg,.zero⟩,
     ⟨.pos,.pos,.zero⟩,
     ⟨.neg,.zero,.neg⟩,
     ⟨.neg,.zero,.pos⟩,
     ⟨.pos,.zero,.neg⟩,
     ⟨.pos,.zero,.pos⟩,
     ⟨.zero,.neg,.neg⟩,
     ⟨.zero,.neg,.pos⟩,
     ⟨.zero,.pos,.neg⟩,
     ⟨.zero,.pos,.pos⟩ ]


def labelToPoint : SchlafliLabel → Ternary27Point
  | .left f => leftPoint f
  | .middle p => middlePoint p
  | .right f => rightPoint f

 theorem point_label_left : ∀ p, labelToPoint (pointToLabel p) = p := by
  native_decide

 theorem label_point_left : ∀ l, pointToLabel (labelToPoint l) = l := by
  native_decide


def pointEquivLabel : Ternary27Point ≃ SchlafliLabel where
  toFun := pointToLabel
  invFun := labelToPoint
  left_inv := point_label_left
  right_inv := label_point_left

 theorem ternary27_card : Fintype.card Ternary27Point = 27 := by native_decide
 theorem label27_card : Fintype.card SchlafliLabel = 27 := by native_decide

/-- Classical 27-line intersection relation in the `6+15+6` presentation. -/
def intersects : SchlafliLabel → SchlafliLabel → Bool
  | .left i, .right j => decide (i ≠ j)
  | .right i, .left j => decide (i ≠ j)
  | .left i, .middle p => pairContains p i
  | .middle p, .left i => pairContains p i
  | .right i, .middle p => pairContains p i
  | .middle p, .right i => pairContains p i
  | .middle p, .middle q => decide (p ≠ q) && pairDisjoint p q
  | _, _ => false

/-- Schlaefli adjacency is skewness: distinct labels that do not intersect. -/
def labelSchlafli (x y : SchlafliLabel) : Bool :=
  decide (x ≠ y) && !(intersects x y)

/-- Orthogonality/intersection complement relation. -/
def labelOrthogonal (x y : SchlafliLabel) : Bool :=
  decide (x ≠ y) && intersects x y


def pointSchlafli (x y : Ternary27Point) : Bool :=
  labelSchlafli (pointToLabel x) (pointToLabel y)


def pointOrthogonal (x y : Ternary27Point) : Bool :=
  labelOrthogonal (pointToLabel x) (pointToLabel y)


def pointDegree (adj : Ternary27Point → Ternary27Point → Bool)
    (x : Ternary27Point) : Nat :=
  (Finset.univ.filter fun y : Ternary27Point => adj x y = true).card


def pointCommon (adj : Ternary27Point → Ternary27Point → Bool)
    (x y : Ternary27Point) : Nat :=
  (Finset.univ.filter fun z : Ternary27Point =>
    (adj x z && adj y z) = true).card

 theorem typed_hypervoxel_schlafli_degree_16 :
    ∀ x, pointDegree pointSchlafli x = 16 := by native_decide

 theorem typed_hypervoxel_schlafli_adjacent_common_10 :
    ∀ x y, pointSchlafli x y = true → pointCommon pointSchlafli x y = 10 := by
  native_decide

 theorem typed_hypervoxel_schlafli_nonadjacent_common_8 :
    ∀ x y, x ≠ y → pointSchlafli x y = false →
      pointCommon pointSchlafli x y = 8 := by
  native_decide

 theorem typed_hypervoxel_orthogonal_degree_10 :
    ∀ x, pointDegree pointOrthogonal x = 10 := by native_decide

 theorem typed_hypervoxel_orthogonal_adjacent_common_1 :
    ∀ x y, pointOrthogonal x y = true →
      pointCommon pointOrthogonal x y = 1 := by native_decide

 theorem typed_hypervoxel_orthogonal_nonadjacent_common_5 :
    ∀ x y, x ≠ y → pointOrthogonal x y = false →
      pointCommon pointOrthogonal x y = 5 := by native_decide

/-! ## Exact minuscule-label recognition -/


def leftWeight : Face6 → DynkinLabel
  | .xNeg => ![1,-1,-1,1,0,0]
  | .xPos => ![1,0,-1,0,0,0]
  | .yNeg => ![1,0,0,-1,1,0]
  | .yPos => ![1,0,0,0,-1,1]
  | .zNeg => ![1,0,0,0,0,-1]
  | .zPos => ![1,1,-1,0,0,0]


def rightWeight : Face6 → DynkinLabel
  | .xNeg => ![-1,-1,0,1,0,0]
  | .xPos => ![-1,0,0,0,0,0]
  | .yNeg => ![-1,0,1,-1,1,0]
  | .yPos => ![-1,0,1,0,-1,1]
  | .zNeg => ![-1,0,1,0,0,-1]
  | .zPos => ![-1,1,0,0,0,0]


def middleWeight : Pair15 → DynkinLabel :=
  ![ ![0,1,1,-1,0,0],
     ![0,0,-1,1,0,-1],
     ![0,-1,0,0,0,1],
     ![0,1,0,0,-1,0],
     ![0,1,0,-1,1,-1],
     ![0,0,0,1,-1,0],
     ![0,0,0,0,1,-1],
     ![0,1,0,-1,0,1],
     ![0,0,1,-1,0,0],
     ![0,0,0,0,0,1],
     ![0,-1,1,0,0,0],
     ![0,0,-1,1,-1,1],
     ![0,-1,0,1,-1,0],
     ![0,0,-1,0,1,0],
     ![0,-1,0,0,1,-1] ]


def labelWeight : SchlafliLabel → DynkinLabel
  | .left f => leftWeight f
  | .middle p => middleWeight p
  | .right f => rightWeight f

 theorem label_weight_in_omega5 : ∀ l, labelWeight l ∈ minusculeOmega5Set := by
  native_decide


def labelToOmega5 (l : SchlafliLabel) : Omega5Weight :=
  ⟨labelWeight l, label_weight_in_omega5 l⟩

 theorem label_to_omega5_bijective : Function.Bijective labelToOmega5 := by
  native_decide


def pointToOmega5 (p : Ternary27Point) : Omega5Weight :=
  labelToOmega5 (pointToLabel p)

 theorem point_to_omega5_bijective : Function.Bijective pointToOmega5 := by
  native_decide

noncomputable def pointEquivOmega5 : Ternary27Point ≃ Omega5Weight :=
  Equiv.ofBijective pointToOmega5 point_to_omega5_bijective

 theorem label_schlafli_is_minuscule_pairing :
    ∀ x y : SchlafliLabel,
      labelSchlafli x y =
        minusculeAdjacent (fun w : Omega5Weight => w.1)
          (labelToOmega5 x) (labelToOmega5 y) := by
  native_decide

 theorem point_schlafli_is_minuscule_pairing :
    ∀ x y : Ternary27Point,
      pointSchlafli x y =
        minusculeAdjacent (fun w : Omega5Weight => w.1)
          (pointToOmega5 x) (pointToOmega5 y) := by
  native_decide

/-! ## Additive no-go is escaped, not contradicted -/


def tritAdd : Trit → Trit → Trit
  | .zero, b => b
  | a, .zero => a
  | .pos, .pos => .neg
  | .neg, .neg => .pos
  | .pos, .neg => .zero
  | .neg, .pos => .zero


def pointAdd (a b : Ternary27Point) : Ternary27Point :=
  ⟨tritAdd a.x b.x, tritAdd a.y b.y, tritAdd a.z b.z⟩

 theorem typed_schlafli_is_not_translation_invariant :
    ∃ x y t : Ternary27Point,
      pointSchlafli x y ≠ pointSchlafli (pointAdd x t) (pointAdd y t) := by
  refine ⟨⟨.neg,.neg,.neg⟩, ⟨.neg,.neg,.zero⟩, ⟨.neg,.neg,.neg⟩, ?_⟩
  native_decide

inductive TypedSchlafliRecognitionCreatesAlbertProduct : Prop
inductive TypedSchlafliRecognitionMakesAdditiveCayleyRouteValid : Prop
inductive TypedSchlafliRecognitionPaysIndependentE6ActionOnRawTernary : Prop

 theorem typed_schlafli_does_not_create_albert_product :
    ¬ TypedSchlafliRecognitionCreatesAlbertProduct := by intro h; cases h

 theorem typed_schlafli_does_not_restore_cayley_route :
    ¬ TypedSchlafliRecognitionMakesAdditiveCayleyRouteValid := by intro h; cases h

 theorem relation_recognition_does_not_pay_independent_raw_ternary_e6_action :
    ¬ TypedSchlafliRecognitionPaysIndependentE6ActionOnRawTernary := by intro h; cases h

structure Boundary where
  absoluteSixFaceChartTyped : Bool
  ternary27ToSixFifteenSixBijectionPaid : Bool
  schlafliSRG2716108Paid : Bool
  orthogonalSRG271015Paid : Bool
  omega5MinusculeRelationSameObjectPaid : Bool
  translationInvariantCayleyRelation : Bool
  independentPreexistingE6ActionOnRawTernaryPaid : Bool
  albertJordanProductPaid : Bool
  deriving Repr


def canonicalBoundary : Boundary where
  absoluteSixFaceChartTyped := true
  ternary27ToSixFifteenSixBijectionPaid := true
  schlafliSRG2716108Paid := true
  orthogonalSRG271015Paid := true
  omega5MinusculeRelationSameObjectPaid := true
  translationInvariantCayleyRelation := false
  independentPreexistingE6ActionOnRawTernaryPaid := false
  albertJordanProductPaid := false

end Integration.Ternary27HyperformSchlafliRecognition
