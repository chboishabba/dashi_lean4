import Integration.T4ExteriorSquareE6GeneratorLift

/-!
# Projective E6 Coxeter relations on the four-trit lifts

The explicit T4 lifts of the E6 simple reflections are not involutions in
GSp4(3): each squares to the central scalar -I.  Their Coxeter relations hold
modulo the same central sign.  This is the finite projective quotient mechanism
expected for PGSp4(3), stated here without claiming the full generated-group
order or abstract group isomorphism.
-/

namespace Integration.T4ExteriorSquareE6ProjectiveCoxeter

open Integration.T4SymplecticExteriorSquareE6Bridge
open Integration.E6Mod3WeylAction
open Integration.T4ExteriorSquareE6GeneratorLift

/-- Central scalar -I on the four-trit carrier. -/
def negT4 (x : T4) : T4 :=
  ⟨-x.x1,-x.x2,-x.x3,-x.x4⟩

/-- The central sign is an involution. -/
theorem negT4_involutive : ∀ x, negT4 (negT4 x) = x := by
  native_decide

/-- Every lifted simple reflection squares to the central sign. -/
theorem liftSimple_square_is_central_neg :
    ∀ s x, liftSimple s (liftSimple s x) = negT4 x := by
  native_decide

/-- Pointwise equality modulo the central sign. -/
def projectivelyEqual (x y : T4) : Prop := x = y ∨ x = negT4 y

instance (x y : T4) : Decidable (projectivelyEqual x y) := inferInstance

/-- Adjacent E6 braid relations hold modulo ±I. -/
theorem lifted_adjacent_braid_projectively :
    ∀ i j,
      coxeterAdjacent i j = true →
      ∀ x,
        projectivelyEqual
          (liftSimple i (liftSimple j (liftSimple i x)))
          (liftSimple j (liftSimple i (liftSimple j x))) := by
  native_decide

/-- Nonadjacent E6 generators commute modulo ±I. -/
theorem lifted_nonadjacent_commute_projectively :
    ∀ i j,
      i ≠ j → coxeterAdjacent i j = false →
      ∀ x,
        projectivelyEqual
          (liftSimple i (liftSimple j x))
          (liftSimple j (liftSimple i x)) := by
  native_decide

/-- The central sign disappears under the primitive exterior-square chart. -/
theorem central_neg_invisible_on_wedge :
    ∀ u v,
      wedge6 (negT4 u) (negT4 v) = wedge6 u v := by
  native_decide

/-- Therefore the projective defect is exactly invisible to the five-dimensional
exterior-square representation, explaining why the E6 generators there satisfy
ordinary Coxeter relations. -/
theorem central_neg_invisible_on_isotropicPairStandard :
    ∀ u v,
      isotropicPairStandard (negT4 u) (negT4 v) = isotropicPairStandard u v := by
  native_decide

structure Boundary where
  centralSignTyped : Bool
  liftedGeneratorsSquareToCentralSign : Bool
  adjacentBraidProjective : Bool
  nonadjacentCommuteProjective : Bool
  centralSignKilledByExteriorSquare : Bool
  quotientGroupOrder51840KernelPaidHere : Bool
  pgsp4AbstractIsoWeylE6KernelPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  centralSignTyped := true
  liftedGeneratorsSquareToCentralSign := true
  adjacentBraidProjective := true
  nonadjacentCommuteProjective := true
  centralSignKilledByExteriorSquare := true
  quotientGroupOrder51840KernelPaidHere := false
  pgsp4AbstractIsoWeylE6KernelPaidHere := false

end Integration.T4ExteriorSquareE6ProjectiveCoxeter
