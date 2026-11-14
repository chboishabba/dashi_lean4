import Synthesis.MillenniumHodgeCycleIsoPushforwardExact
import Synthesis.MillenniumHodgeRealAlgebraicCycleMultiplicityExact
import Mathlib.Tactic

/-!
# Hodge: genuine algebraic point-cycle transport along scheme isomorphisms

PR #40 already owns:
* the ACTUAL Mathlib AlgebraicCycle X ℤ carrier;
* its literal pointCycle x and rulingDifferenceCycle x y;
* actualCyclePushforward e.hom with genuine residue-field-degree weights;
* actualCyclePushforward_iso_apply, reindexing coefficients by e.inv.

This module proves, with NO synthetic cycle carrier and NO new
correspondence-action premise:
  f_*[x] = [f x]
and
  f_*([x]-[y]) = [f x]-[f y]
for EVERY actual scheme isomorphism f. When f exchanges two selected
scheme points, the actual difference cycle is anti-invariant.

This is a real cycle-side naturality theorem, NOT yet the
cohomological cycle-class map, codimension-one ruling fundamental
cycles on P¹×P¹, or universal Hodge conjecture.
Local pinned Lean kernel acceptance is pending.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory
open AlgebraicGeometry

section IsoPoint

variable {X Y : Scheme} [DecidableEq X] [DecidableEq Y]

/-- Pushforward of an ACTUAL Mathlib point cycle along a genuine
scheme isomorphism equals the actual point cycle of its image.
Residue-degree multiplicity one is provided by the imported
Mathlib cycle-isomorphism donor, not inserted as a new axiom. -/
theorem actualCyclePushforward_iso_pointCycle
    (e : X ≅ Y) (x : X) :
    actualCyclePushforward e.hom (pointCycle x) =
      pointCycle (e.hom x) := by
  ext y
  rw [actualCyclePushforward_iso_apply]
  by_cases h : e.inv y = x
  · have hy : y = e.hom x := by
      calc
        y = e.hom (e.inv y) := (e.hom_inv_id_apply y).symm
        _ = e.hom x := congrArg e.hom h
    simp [pointCycle, h, hy]
  · have hy : y ≠ e.hom x := by
      intro heq
      apply h
      calc
        e.inv y = e.inv (e.hom x) := congrArg e.inv heq
        _ = x := e.inv_hom_id_apply x
    simp [pointCycle, h, hy]

/-- Literal source difference-cycle transport along an actual scheme
isomorphism; this is not merely an equation of abstract Z² lattices. -/
theorem actualCyclePushforward_iso_pointDifference
    (e : X ≅ Y) (x₁ x₂ : X) :
    actualCyclePushforward e.hom (rulingDifferenceCycle x₁ x₂) =
      rulingDifferenceCycle (e.hom x₁) (e.hom x₂) := by
  calc
    actualCyclePushforward e.hom (rulingDifferenceCycle x₁ x₂) =
        actualCyclePushforward e.hom (pointCycle x₁) -
          actualCyclePushforward e.hom (pointCycle x₂) := by
            ext y
            simp [rulingDifferenceCycle,
              actualCyclePushforward_iso_apply]
    _ = rulingDifferenceCycle (e.hom x₁) (e.hom x₂) := by
      simp [actualCyclePushforward_iso_pointCycle,
        rulingDifferenceCycle]

end IsoPoint

section Involution

variable {X : Scheme} [DecidableEq X]

/-- A genuine scheme automorphism exchanging actual points gives an
anti-invariant ACTUAL algebraic-cycle difference; no conditional
P1QRulingCycleExchange premise is needed once the point action
is established. This is not yet the divisor ruling exchange. -/
theorem actualIsoSwap_pointDifference_antiInvariant
    (e : X ≅ X) (x₁ x₂ : X)
    (h₁₂ : e.hom x₁ = x₂)
    (h₂₁ : e.hom x₂ = x₁) :
    actualCyclePushforward e.hom
      (rulingDifferenceCycle x₁ x₂) =
        -(rulingDifferenceCycle x₁ x₂) := by
  rw [actualCyclePushforward_iso_pointDifference, h₁₂, h₂₁]
  unfold rulingDifferenceCycle
  abel

end Involution

end Synthesis.Millennium.Hodge
