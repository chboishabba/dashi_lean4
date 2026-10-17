import Integration.E6Mod3WeylAction
import Mathlib

/-!
# Global E6 mod-3 reflection intertwiner

The earlier finite exploration briefly reported a partial reflection match from
a Gram-based root lookup.  The actual lattice quotient is linear, so that
partial result should not survive once both sides are expressed through the
same global map.

This owner pays the stronger statement on all 3^6 = 729 mod-3 lattice points:

* the six simple reflections preserve the E6 Cartan quadratic form;
* they preserve each coset of the one-dimensional Cartan radical;
* quotienting the radical and applying the explicit five-dimensional isometry
  commutes exactly with each standardized five-dimensional reflection.

Thus the quotient/isometry is a genuine global action intertwiner; no nonlinear
repair is needed for the E6 mod-3 reflection action.
-/

namespace Integration.E6Mod3ReflectionIntertwiner

open Integration.E6Mod3QuadraticBridge
open Integration.E6Mod3WeylAction

/-- Simple E6 reflection on the six simple-root coefficients over F3.
For simply-laced E6, only the selected coefficient changes:
`c_i ↦ -c_i + Σ_{j~i} c_j`. -/
def reflectF3Six : E6SimpleReflection → F3Six → F3Six
  | .s0, x =>
      ⟨-x.x0 + x.x2, x.x1, x.x2, x.x3, x.x4, x.x5⟩
  | .s1, x =>
      ⟨x.x0, -x.x1 + x.x3, x.x2, x.x3, x.x4, x.x5⟩
  | .s2, x =>
      ⟨x.x0, x.x1, -x.x2 + x.x0 + x.x3, x.x3, x.x4, x.x5⟩
  | .s3, x =>
      ⟨x.x0, x.x1, x.x2, -x.x3 + x.x1 + x.x2 + x.x4, x.x4, x.x5⟩
  | .s4, x =>
      ⟨x.x0, x.x1, x.x2, x.x3, -x.x4 + x.x3 + x.x5, x.x5⟩
  | .s5, x =>
      ⟨x.x0, x.x1, x.x2, x.x3, x.x4, -x.x5 + x.x4⟩

/-- The six coefficient reflections are involutions on the full 729-point
mod-3 lattice carrier. -/
theorem reflection_involutive :
    ∀ s x, reflectF3Six s (reflectF3Six s x) = x := by
  native_decide

/-- They preserve the reduced E6 Cartan quadratic form globally. -/
theorem reflection_preserves_cartan_quadratic :
    ∀ s x, e6Mod3Quadratic (reflectF3Six s x) = e6Mod3Quadratic x := by
  native_decide

/-- The mod-3 radical line is fixed pointwise by each simple reflection. -/
theorem reflection_commutes_radical_translation :
    ∀ s a x,
      reflectF3Six s (radicalTranslate a x) =
        radicalTranslate a (reflectF3Six s x) := by
  native_decide

/-- Therefore the concrete quotient coordinates are independent of the chosen
representative after reflection as well as before it. -/
theorem reflected_radical_representatives_have_same_quotient :
    ∀ s a x,
      quotientCoordinates (reflectF3Six s (radicalTranslate a x)) =
        quotientCoordinates (reflectF3Six s x) := by
  native_decide

/-- Main theorem: the literal radical quotient followed by the explicit
standardizing isometry intertwines every simple reflection on every one of the
729 six-coordinate inputs. -/
theorem quotient_isometry_intertwines_reflection :
    ∀ s x,
      quotientToStandard (quotientCoordinates (reflectF3Six s x)) =
        reflectStandard s
          (quotientToStandard (quotientCoordinates x)) := by
  native_decide

/-- The same statement before the final standardizing change of basis, packaged
as a commutative-square predicate for downstream consumers. -/
def ReflectionIntertwiningSquare (s : E6SimpleReflection) : Prop :=
  ∀ x,
    quotientToStandard (quotientCoordinates (reflectF3Six s x)) =
      reflectStandard s (quotientToStandard (quotientCoordinates x))

theorem every_simple_reflection_has_intertwining_square :
    ∀ s, ReflectionIntertwiningSquare s := by
  intro s x
  exact quotient_isometry_intertwines_reflection s x

/-- Root images are a restriction of the global theorem, not a separately fit
lookup table. -/
theorem root_mod3_intertwining :
    ∀ s root,
      quotientToStandard
          (quotientCoordinates (reflectF3Six s (rootMod3 root))) =
        reflectStandard s
          (quotientToStandard (e6QuotientCoordinates root)) := by
  intro s root
  simpa [e6QuotientCoordinates] using
    quotient_isometry_intertwines_reflection s (rootMod3 root)

inductive PartialGramLookupRequiresNonlinearRepair : Prop

theorem no_nonlinear_repair_from_partial_lookup :
    ¬ PartialGramLookupRequiresNonlinearRepair := by
  intro h
  cases h

structure Boundary where
  sixCoefficientReflectionsTyped : Bool
  reflectionInvolutionsAll729Paid : Bool
  cartanQuadraticPreservationAll729Paid : Bool
  radicalCosetCompatibilityAll729Paid : Bool
  globalIntertwiningAll729Paid : Bool
  rootRestrictionIntertwiningPaid : Bool
  oldPartialIntertwiningInterpretationRetained : Bool
  nonlinearExceptionalRepairRequiredHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  sixCoefficientReflectionsTyped := true
  reflectionInvolutionsAll729Paid := true
  cartanQuadraticPreservationAll729Paid := true
  radicalCosetCompatibilityAll729Paid := true
  globalIntertwiningAll729Paid := true
  rootRestrictionIntertwiningPaid := true
  oldPartialIntertwiningInterpretationRetained := false
  nonlinearExceptionalRepairRequiredHere := false

end Integration.E6Mod3ReflectionIntertwiner
