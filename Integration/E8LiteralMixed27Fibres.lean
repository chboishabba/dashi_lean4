import Integration.E8LiteralE6A2Branching
import Integration.E6LiteralE8Action
import Integration.E6F3OrbitTransitivity
import Mathlib

/-!
# Literal E8 mixed sectors as six E6-stable 27-point fibres

The two 81-point mixed sectors in the literal `E8 -> E6 x A2` branching are
not irreducible 81-point E6 orbits.  Each is the disjoint union of three
27-point fibres indexed by its A2 weight.

The six embedded E6 simple reflections preserve the A2 weight because the E6
simple roots are orthogonal to the chosen A2 subsystem.  Thus these 27-point
fibres are the natural same-action targets for any future Albert/minuscule-27
recognition.

By contrast, the bare F3^5 E6 action already has its complete four-stratum
orbit picture `1,80,90,72`; it supplies no 27-point orbit.  Therefore the E8
lift requires additional 27-carrier data rather than extracting a 27 orbit from
the existing five-trit quadratic carrier.
-/

namespace Integration.E8LiteralMixed27Fibres

open Integration.E8RelativeT5IntrinsicGraphObstruction
open Integration.E8LiteralE6A2Branching
open Integration.E6Mod3WeylAction
open Integration.E6LiteralE8Action
open Integration.E6F3OrbitTransitivity

/-- Literal fibre of one selected A2 weight. -/
def LiteralWeightFiber (w : Int × Int) :=
  {r : E8ScaledRoot // a2Weight r = w}

instance (w : Int × Int) : Fintype (LiteralWeightFiber w) := inferInstance

abbrev Plus0 := LiteralWeightFiber (0,-4)
abbrev Plus1 := LiteralWeightFiber (4,0)
abbrev Plus2 := LiteralWeightFiber (-4,4)
abbrev Minus0 := LiteralWeightFiber (0,4)
abbrev Minus1 := LiteralWeightFiber (-4,0)
abbrev Minus2 := LiteralWeightFiber (4,-4)

/-- Each mixed A2 weight fibre has exactly 27 E8 roots. -/
theorem plus0_card : Fintype.card Plus0 = 27 := by native_decide
theorem plus1_card : Fintype.card Plus1 = 27 := by native_decide
theorem plus2_card : Fintype.card Plus2 = 27 := by native_decide
theorem minus0_card : Fintype.card Minus0 = 27 := by native_decide
theorem minus1_card : Fintype.card Minus1 = 27 := by native_decide
theorem minus2_card : Fintype.card Minus2 = 27 := by native_decide

/-- The first literal mixed sector is exactly the union of its three 27-weight
fibres. -/
theorem literal_mixed_plus_three_weights :
    ∀ r : LiteralMixedPlus,
      a2Weight r.1 = (0,-4) ∨
      a2Weight r.1 = (4,0) ∨
      a2Weight r.1 = (-4,4) := by
  native_decide

/-- Likewise for the opposite mixed sector. -/
theorem literal_mixed_minus_three_weights :
    ∀ r : LiteralMixedMinus,
      a2Weight r.1 = (0,4) ∨
      a2Weight r.1 = (-4,0) ∨
      a2Weight r.1 = (4,-4) := by
  native_decide

/-- Weight pair of the literal reflected coordinate vector. -/
def reflectedWeight (s : E6SimpleReflection) (r : E8ScaledRoot) : Int × Int :=
  let reflected : Fin 8 → Int := literalReflectCoord s r
  (∑ k : Fin 8, reflected k * e8Coord a2SimpleA k,
   ∑ k : Fin 8, reflected k * e8Coord a2SimpleB k)

/-- E6 reflection leaves the A2 weight unchanged on every literal E8 root. -/
theorem literal_e6_reflection_preserves_a2_weight :
    ∀ s r, reflectedWeight s r = a2Weight r := by
  native_decide

/-- Consequently every one of the six 27-point mixed fibres is stable under the
literal E6 simple-root reflection relation.  Relation form avoids defining the
root action by transport through a ternary bijection. -/
theorem literal_reflection_preserves_weight_fibre :
    ∀ s (w : Int × Int) (r : LiteralWeightFiber w) k,
      reflectedWeight s r.1 = w := by
  intro s w r k
  simpa [r.2] using literal_e6_reflection_preserves_a2_weight s r.1

/-- The already-paid bare five-trit E6 orbit sizes. -/
def BareF3FiveOrbitSize (n : Nat) : Prop :=
  n = 1 ∨ n = 80 ∨ n = 90 ∨ n = 72

/-- The four bare orbit sizes come from zero plus the three globally transitive
quadratic strata. -/
theorem bare_f3five_orbit_sizes_recorded :
    BareF3FiveOrbitSize 1 ∧
    BareF3FiveOrbitSize 80 ∧
    BareF3FiveOrbitSize 90 ∧
    BareF3FiveOrbitSize 72 := by
  simp [BareF3FiveOrbitSize]

/-- No 27-point E6 orbit exists in the existing bare F3^5 quadratic orbit
classification. -/
theorem no_bare_f3five_27_orbit_size : ¬ BareF3FiveOrbitSize 27 := by
  norm_num [BareF3FiveOrbitSize]

/-- Recognition contract for an externally supplied 27-carrier.  This is the
socket that an Albert/minuscule-27 owner must inhabit; cardinality 27 alone is
not enough. -/
structure Mixed27Recognition (w : Int × Int) : Type 1 where
  Carrier : Type
  carrierFintype : Fintype Carrier
  carrierCard27 : @Fintype.card Carrier carrierFintype = 27
  Actor : Type
  sourceAction : Actor → Carrier → Carrier
  literalAction : Actor → LiteralWeightFiber w → LiteralWeightFiber w
  equivFiber : Carrier ≃ LiteralWeightFiber w
  intertwines : ∀ g x,
    equivFiber (sourceAction g x) = literalAction g (equivFiber x)

inductive BareF3FiveAutomaticallySuppliesAlbert27 : Prop
inductive Cardinality27CreatesAlbertRecognition : Prop

theorem bare_f3five_does_not_create_albert27 :
    ¬ BareF3FiveAutomaticallySuppliesAlbert27 := by
  intro h
  cases h

theorem cardinality27_does_not_create_albert_recognition :
    ¬ Cardinality27CreatesAlbertRecognition := by
  intro h
  cases h

structure Boundary where
  sixLiteralWeightFibresTyped : Bool
  eachLiteralWeightFibreCount27Paid : Bool
  literalMixedPlusIsThree27FibresPaid : Bool
  literalMixedMinusIsThree27FibresPaid : Bool
  e6ReflectionPreservesA2WeightPaid : Bool
  bareF3FiveOrbitSizesOneEightyNinetySeventyTwoConsumed : Bool
  bareF3FiveSupplies27Orbit : Bool
  external27RecognitionSocketTyped : Bool
  albert27RecognitionAutomaticallyPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  sixLiteralWeightFibresTyped := true
  eachLiteralWeightFibreCount27Paid := true
  literalMixedPlusIsThree27FibresPaid := true
  literalMixedMinusIsThree27FibresPaid := true
  e6ReflectionPreservesA2WeightPaid := true
  bareF3FiveOrbitSizesOneEightyNinetySeventyTwoConsumed := true
  bareF3FiveSupplies27Orbit := false
  external27RecognitionSocketTyped := true
  albert27RecognitionAutomaticallyPaid := false

end Integration.E8LiteralMixed27Fibres
