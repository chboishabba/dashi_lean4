import Mathlib
import CliffordUniversalProperty
import FiniteQuaternionStrictCover

/-!
# Lean mirror of `DASHI/Algebra/ConstructiveClifford.agda`

Concrete syntax, generated Clifford congruence, the explicit 16-blade basis,
parity/reversion tables, and the Pin/Spin word surfaces.  Completion authority
remains explicit structure data rather than an asserted theorem.
-/

namespace AgdaMirror.ConstructiveClifford

inductive Axis4 | timeAxis | xAxis | yAxis | zAxis
  deriving DecidableEq, Repr
inductive ScalarSign | negative | zero | positive
  deriving DecidableEq, Repr

open Axis4 ScalarSign

def metricSquare : Axis4 → ScalarSign
  | .timeAxis => .negative
  | .xAxis | .yAxis | .zAxis => .positive

inductive CliffordWord
  | scalarWord : ScalarSign → CliffordWord
  | generator : Axis4 → CliffordWord
  | mul : CliffordWord → CliffordWord → CliffordWord
  deriving DecidableEq, Repr

infixl:70 " ∙ " => CliffordWord.mul

inductive DistinctAxis : Axis4 → Axis4 → Prop
  | time_x : DistinctAxis .timeAxis .xAxis
  | time_y : DistinctAxis .timeAxis .yAxis
  | time_z : DistinctAxis .timeAxis .zAxis
  | x_time : DistinctAxis .xAxis .timeAxis
  | x_y : DistinctAxis .xAxis .yAxis
  | x_z : DistinctAxis .xAxis .zAxis
  | y_time : DistinctAxis .yAxis .timeAxis
  | y_x : DistinctAxis .yAxis .xAxis
  | y_z : DistinctAxis .yAxis .zAxis
  | z_time : DistinctAxis .zAxis .timeAxis
  | z_x : DistinctAxis .zAxis .xAxis
  | z_y : DistinctAxis .zAxis .yAxis

inductive CliffordRel : CliffordWord → CliffordWord → Prop
  | refl {word} : CliffordRel word word
  | symm {left right} : CliffordRel left right → CliffordRel right left
  | trans {left middle right} : CliffordRel left middle → CliffordRel middle right →
      CliffordRel left right
  | congLeft {left right suffix} : CliffordRel left right →
      CliffordRel (left ∙ suffix) (right ∙ suffix)
  | congRight {left right initial} : CliffordRel left right →
      CliffordRel (initial ∙ left) (initial ∙ right)
  | assoc (left middle right) : CliffordRel ((left ∙ middle) ∙ right)
      (left ∙ (middle ∙ right))
  | square (axis) : CliffordRel (.generator axis ∙ .generator axis)
      (.scalarWord (metricSquare axis))
  | anticommute {left right} : DistinctAxis left right →
      CliffordRel (.generator left ∙ .generator right)
        (.scalarWord .negative ∙ (.generator right ∙ .generator left))

infix:50 " ≈Cl " => CliffordRel

inductive CliffordBlade16
  | blade1 | bladeT | bladeX | bladeY | bladeZ
  | bladeTX | bladeTY | bladeTZ | bladeXY | bladeXZ | bladeYZ
  | bladeTXY | bladeTXZ | bladeTYZ | bladeXYZ | bladeTXYZ
  deriving DecidableEq, Repr

inductive Parity | even | odd
  deriving DecidableEq, Repr

def combineParity : Parity → Parity → Parity
  | .even, right => right
  | .odd, .even => .odd
  | .odd, .odd => .even

def wordParity : CliffordWord → Parity
  | .scalarWord _ => .even
  | .generator _ => .odd
  | .mul left right => combineParity (wordParity left) (wordParity right)

def bladeParity : CliffordBlade16 → Parity
  | .blade1 | .bladeTX | .bladeTY | .bladeTZ | .bladeXY | .bladeXZ | .bladeYZ
  | .bladeTXYZ => .even
  | _ => .odd

inductive ReversionSign | reversePositive | reverseNegative
  deriving DecidableEq, Repr

def reversionSign : CliffordBlade16 → ReversionSign
  | .blade1 | .bladeT | .bladeX | .bladeY | .bladeZ | .bladeTXYZ => .reversePositive
  | _ => .reverseNegative

structure EvenCliffordWord where
  word : CliffordWord
  parityProof : wordParity word = .even

def twoGeneratorEven (left right : Axis4) : EvenCliffordWord :=
  ⟨.generator left ∙ .generator right, rfl⟩

inductive UnitGenerator | unitT | unitX | unitY | unitZ
  deriving DecidableEq, Repr

def unitAxis : UnitGenerator → Axis4
  | .unitT => .timeAxis
  | .unitX => .xAxis
  | .unitY => .yAxis
  | .unitZ => .zAxis

def wordOfUnits : List UnitGenerator → CliffordWord
  | [] => .scalarWord .positive
  | unit :: rest => .generator (unitAxis unit) ∙ wordOfUnits rest

structure PinElement where generators : List UnitGenerator
structure SpinElement where
  pin : PinElement
  evenReceipt : wordParity (wordOfUnits pin.generators) = .even

def spinIdentity : SpinElement := ⟨⟨[]⟩, rfl⟩
def spinXYRotorWord : SpinElement := ⟨⟨[.unitX, .unitY]⟩, rfl⟩
def spinTZRotorWord : SpinElement := ⟨⟨[.unitT, .unitZ]⟩, rfl⟩

/-- Imported completion evidence: callers must provide the universal property. -/
structure CliffordQuotientCompletion where
  quotientCarrier : Type
  quotientMap : CliffordWord → quotientCarrier
  relationSound : ∀ {left right}, left ≈Cl right → quotientMap left = quotientMap right
  universalProperty : AgdaMirror.CliffordUniversalProperty.CliffordData
  universalPropertyWitness :
    AgdaMirror.CliffordUniversalProperty.CliffordUP universalProperty

/-- Imported global authority remains explicit in these fields. -/
structure ConstructiveSpinCompletion where
  cliffordQuotient : CliffordQuotientCompletion
  spinDoubleCover : AgdaMirror.FiniteQuaternionStrictCover.SpinDoubleCoverProof
  twistedAdjointPreservesMetric : Prop
  twistedAdjointPreservesMetricProof : twistedAdjointPreservesMetric
  evenSubalgebraClosedUnderProduct : Prop
  evenSubalgebraClosedUnderProductProof : evenSubalgebraClosedUnderProduct
  reversionSuppliesInverseOnSpin : Prop
  reversionSuppliesInverseOnSpinProof : reversionSuppliesInverseOnSpin

abbrev constructiveCliffordScope := CliffordBlade16

/-- No completion record is promoted merely by defining the concrete syntax. -/
def constructiveCompletionPromotion : Bool := false

end AgdaMirror.ConstructiveClifford
