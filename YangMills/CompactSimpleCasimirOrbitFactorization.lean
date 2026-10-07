import Mathlib

/-!
# Compact-simple Casimir factorization compiler

The group-independent part of the current Agda all-group route is algebraic.
Once the physical one-loop Wilson/ghost/Haar colour expression for a compact
simple gauge group is identified as `C_A` times one universal four-orbit scalar,
there is no reason to repeat the finite orbit calculation group by group.

This file mirrors that theorem-bearing transport in Lean.  It deliberately does
not prove the remaining physical colour-contraction/Haar/ghost identity or the
strict positivity of `C_A` for a selected compact simple group.
-/

namespace RequestProject.YangMills

/-- Universal four-orbit scalar before applying a group-specific Casimir scale. -/
structure FourOrbitScalar where
  oneOuter : ℝ
  twoOuter : ℝ
  threeOuter : ℝ
  fourOuter : ℝ

namespace FourOrbitScalar

/-- Total universal one-loop scalar. -/
def total (orbit : FourOrbitScalar) : ℝ :=
  orbit.oneOuter + orbit.twoOuter + orbit.threeOuter + orbit.fourOuter

/-- Apply one group-specific adjoint-Casimir scale to every orbit contribution. -/
def scale (C : ℝ) (orbit : FourOrbitScalar) : FourOrbitScalar where
  oneOuter := C * orbit.oneOuter
  twoOuter := C * orbit.twoOuter
  threeOuter := C * orbit.threeOuter
  fourOuter := C * orbit.fourOuter

/-- Applying the Casimir per orbit equals applying it once to the universal sum. -/
theorem total_scale (C : ℝ) (orbit : FourOrbitScalar) :
    (orbit.scale C).total = C * orbit.total := by
  simp [total, scale]
  ring

end FourOrbitScalar

/-- Elementary four-orbit distributivity, exposed for frontier tests. -/
theorem casimir_scale_distributes_four_orbits
    (C a b c d : ℝ) :
    C * (a + b + c + d) = C * a + C * b + C * c + C * d := by
  ring

/-- Nonnegative Casimir scaling transports every certified universal lower bound. -/
theorem casimir_scale_transports_lower_bound
    (C lower total : ℝ)
    (hC : 0 ≤ C)
    (hLower : lower ≤ total) :
    C * lower ≤ C * total :=
  mul_le_mul_of_nonneg_left hLower hC

/-- Minimal group-specific carrier needed by the group-independent compiler. -/
structure CompactSimpleCasimirCarrier (GaugeGroup : Type*) where
  adjointCasimir : GaugeGroup → ℝ
  adjointCasimirNonnegative : ∀ group, 0 ≤ adjointCasimir group

/-- Universal four-orbit lower-bound certificate. -/
structure UniversalFourOrbitLowerBound (orbit : FourOrbitScalar) where
  lower : ℝ
  lowerSound : lower ≤ orbit.total

/-- Group-scaled one-loop coefficient after physical `C_A` factorization. -/
def groupScaledOneLoopCoefficient
    {GaugeGroup : Type*}
    (carrier : CompactSimpleCasimirCarrier GaugeGroup)
    (group : GaugeGroup)
    (orbit : FourOrbitScalar) : ℝ :=
  carrier.adjointCasimir group * orbit.total

/-- Exact reuse of a universal lower bound for every nonnegative Casimir carrier. -/
theorem compact_simple_casimir_transports_universal_lower_bound
    {GaugeGroup : Type*}
    (carrier : CompactSimpleCasimirCarrier GaugeGroup)
    (group : GaugeGroup)
    (orbit : FourOrbitScalar)
    (bound : UniversalFourOrbitLowerBound orbit) :
    carrier.adjointCasimir group * bound.lower ≤
      groupScaledOneLoopCoefficient carrier group orbit := by
  exact casimir_scale_transports_lower_bound
    (carrier.adjointCasimir group)
    bound.lower orbit.total
    (carrier.adjointCasimirNonnegative group)
    bound.lowerSound

/--
The generic all-group transport is compiler-owned.  The remaining physical
producer is the actual compact-simple Wilson/ghost/Haar colour algebra proving
that the selected one-loop expression has this `C_A × universal` form.
-/
structure CompactSimplePhysicalCasimirFactorization
    (GaugeGroup : Type*) where
  carrier : CompactSimpleCasimirCarrier GaugeGroup
  universalOrbit : FourOrbitScalar
  physicalOneLoopCoefficient : GaugeGroup → ℝ
  samePhysicalCoefficient :
    ∀ group,
      physicalOneLoopCoefficient group =
        groupScaledOneLoopCoefficient carrier group universalOrbit

end RequestProject.YangMills
