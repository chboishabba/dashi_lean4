import Integration.T4SymplecticExteriorSquareE6Bridge
import Integration.E6Mod3WeylAction

/-!
# Explicit T4 similitude lifts of the six E6 simple reflections

The matrices below were recovered by exact exhaustive F3 computation from the
primitive exterior-square representation.  This file makes the high-value part
kernel-facing: each lift multiplies the symplectic form by 2=-1 in F3 and,
on isotropic pairs, its primitive exterior-square action is exactly the existing
`E6Mod3WeylAction.reflectStandard` generator.

This is a generator-level same-action theorem.  It does not yet kernel-enumerate
the full generated PGSp4(3) group or prove its order 51840.
-/

namespace Integration.T4ExteriorSquareE6GeneratorLift

open Integration.T4SymplecticExteriorSquareE6Bridge
open Integration.E6Mod3QuadraticBridge
open Integration.E6Mod3WeylAction

/-- Embed this file's standard five-coordinate structure into the pre-existing
E6 mod-3 quotient owner's five-coordinate type. -/
def toE6Five (z : Standard5) : F3Five :=
  ⟨z.z1,z.z2,z.z3,z.z4,z.z5⟩

theorem standardQ_matches_existing (z : Standard5) :
    standardQ z = standardQuadratic (toE6Five z) := by
  rfl

/-- Six explicit anti-symplectic similitude lifts.  Coefficient 2 is -1 in F3. -/
def liftSimple : E6SimpleReflection → T4 → T4
  | .s0, x =>
      ⟨x.x1 + x.x3 + x.x4,
       x.x2 + x.x3 + 2*x.x4,
       2*x.x1 + 2*x.x2 + 2*x.x3,
       2*x.x1 + x.x2 + 2*x.x4⟩
  | .s1, x =>
      ⟨2*x.x1 + 2*x.x3,
       2*x.x2 + x.x3 + 2*x.x4,
       2*x.x1 + x.x3,
       2*x.x1 + 2*x.x2 + x.x4⟩
  | .s2, x =>
      ⟨2*x.x1 + x.x3,
       2*x.x2 + 2*x.x3 + x.x4,
       x.x1 + x.x3,
       x.x1 + x.x2 + x.x4⟩
  | .s3, x =>
      ⟨2*x.x3 + x.x4,
       2*x.x3 + 2*x.x4,
       2*x.x1 + 2*x.x2,
       x.x1 + 2*x.x2⟩
  | .s4, x =>
      ⟨2*x.x4,
       2*x.x3 + x.x4,
       x.x1 + x.x2,
       x.x1⟩
  | .s5, x =>
      ⟨2*x.x3 + 2*x.x4,
       x.x3 + 2*x.x4,
       2*x.x1 + x.x2,
       2*x.x1 + 2*x.x2⟩

/-- Every simple-reflection lift is a symplectic similitude of multiplier
2=-1. -/
theorem liftSimple_multiplier :
    ∀ s u v, omega (liftSimple s u) (liftSimple s v) = 2 * omega u v := by
  native_decide

/-- Isotropic pairs remain isotropic under every lifted generator. -/
theorem liftSimple_preserves_isotropy
    (s : E6SimpleReflection) (u v : T4) (h : omega u v = 0) :
    omega (liftSimple s u) (liftSimple s v) = 0 := by
  rw [liftSimple_multiplier, h]
  simp

/-- The primitive exterior-square chart of an isotropic pair. -/
def isotropicPairStandard (u v : T4) : F3Five :=
  toE6Five (primitiveToStandard (forgetP34 (wedge6 u v)))

/-- Exact generator-level intertwining with the existing E6 mod-3 action. -/
theorem lifted_generator_intertwines :
    ∀ s u v,
      omega u v = 0 →
      isotropicPairStandard (liftSimple s u) (liftSimple s v) =
        reflectStandard s (isotropicPairStandard u v) := by
  native_decide

/-- Hence the quadratic value of an isotropic pair's image is preserved by the
lifted generator, via the already-proved E6 reflection action. -/
theorem lifted_generator_preserves_standard_quadratic
    (s : E6SimpleReflection) (u v : T4) (h : omega u v = 0) :
    standardQuadratic (isotropicPairStandard (liftSimple s u) (liftSimple s v)) =
      standardQuadratic (isotropicPairStandard u v) := by
  rw [lifted_generator_intertwines s u v h]
  exact simple_reflections_preserve_quadratic s (isotropicPairStandard u v)

structure Boundary where
  sixExplicitT4LiftsDefined : Bool
  multiplierMinusOnePaid : Bool
  isotropyPreservationPaid : Bool
  generatorIntertwiningWithExistingE6Paid : Bool
  fullGeneratedGroupOrder51840PaidHere : Bool
  fullPGSp4WeylGroupEquivalencePaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  sixExplicitT4LiftsDefined := true
  multiplierMinusOnePaid := true
  isotropyPreservationPaid := true
  generatorIntertwiningWithExistingE6Paid := true
  fullGeneratedGroupOrder51840PaidHere := false
  fullPGSp4WeylGroupEquivalencePaidHere := false

end Integration.T4ExteriorSquareE6GeneratorLift
