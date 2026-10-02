import Synthesis.MillenniumHodgeRealAlgebraicCycleMultiplicityExact
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic

/-!
# Hodge max-cut: genuine correspondence action on Mathlib algebraic cycles

The previous donor moved the programme from a permissive synthetic cycle
record to Mathlib's actual scheme-level `AlgebraicCycle`.

This module adds the next reusable geometric layer: pushforward along an actual
quasicompact scheme morphism.  The weight is deliberately constant here, so
the construction is the literal cycle pushforward with residue-field degree
multiplicities and no unproved codimension transport assumption.

For an actual scheme automorphism (eventually the factor swap on P¹×P¹), this
is the cycle-side action that a correspondence implementation must use.

No singular/de Rham cohomology action or cycle-class compatibility is claimed.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicCycle

universe u

section Pushforward

variable {X Y : Scheme.{u}}

/-- Genuine algebraic-cycle pushforward along a quasicompact scheme morphism,
using constant weights.  Multiplicity is Mathlib's residue degree. -/
noncomputable def actualCyclePushforward
    (f : X ⟶ Y) [QuasiCompact f]
    (D : AlgebraicCycle X ℤ) :
    AlgebraicCycle Y ℤ :=
  AlgebraicCycle.map f (fun _ : X => ()) (fun _ : Y => ()) D

/-- The identity correspondence acts literally as the identity on the genuine
scheme-level algebraic-cycle carrier. -/
@[simp] theorem actualCyclePushforward_id
    (D : AlgebraicCycle X ℤ) :
    actualCyclePushforward (𝟙 X) D = D := by
  simpa [actualCyclePushforward] using
    (AlgebraicCycle.map_id
      (X := X) (R := ℤ)
      (fun _ : X => ()) D)

/-- Package the pushforward action of a genuine scheme automorphism.  The
quasicompactness hypothesis is explicit rather than smuggled into a synthetic
correspondence record. -/
noncomputable def actualCycleAutomorphismAction
    (e : X ≅ X) [QuasiCompact e.hom]
    (D : AlgebraicCycle X ℤ) :
    AlgebraicCycle X ℤ :=
  actualCyclePushforward e.hom D

@[simp] theorem actualCycleAutomorphismAction_refl
    (D : AlgebraicCycle X ℤ) :
    actualCycleAutomorphismAction (Iso.refl X) D = D := by
  simpa [actualCycleAutomorphismAction]

end Pushforward

section ExistingDonorWeld

variable {X : Scheme.{u}} [DecidableEq X]

/-- The existing genuine point cycle is fixed by the identity correspondence. -/
@[simp] theorem pointCycle_identityCorrespondence
    (x : X) :
    actualCyclePushforward (𝟙 X) (pointCycle x) = pointCycle x := by
  simp

/-- The genuine multiplicity-two point cycle is fixed as a whole cycle, so
the multiplicity coefficient is transported on the actual carrier rather than
only in the local polynomial model. -/
@[simp] theorem doublePointCycle_identityCorrespondence
    (x : X) :
    actualCyclePushforward (𝟙 X) (doublePointCycle x) =
      doublePointCycle x := by
  simp

/-- The nonzero ruling-difference cycle from the P¹×P¹ regression donor is
also an actual cycle-side correspondence input. -/
@[simp] theorem rulingDifferenceCycle_identityCorrespondence
    (h₁ h₂ : X) :
    actualCyclePushforward (𝟙 X) (rulingDifferenceCycle h₁ h₂) =
      rulingDifferenceCycle h₁ h₂ := by
  simp

end ExistingDonorWeld

/-!
MAX-CUT STATUS

PAID:
* actual Mathlib AlgebraicCycle carrier;
* actual scheme-morphism pushforward, with residue-degree multiplicity;
* actual scheme-automorphism cycle action;
* identity correspondence law on arbitrary genuine cycles;
* existing point/double-point/ruling-difference donors enter that real action.

OPEN:
* construct the selected P¹ scheme as Proj on the exact homogeneous ring;
* construct P¹×P¹ and its two actual ruling divisors;
* construct the factor-swap scheme automorphism and evaluate this action on
  those divisors;
* construct graph correspondences and the cohomological action;
* prove cycle-class compatibility;
* move from the regression surface to genuinely difficult primitive Hodge
  classes.
-/

end Synthesis.Millennium.Hodge
