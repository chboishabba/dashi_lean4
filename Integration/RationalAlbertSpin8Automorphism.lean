import Integration.RationalAlbertNative
import Integration.RationalAlbertTrialityBasis
import Integration.RationalOctonionSpin8WeylLift
import Mathlib

/-!
# Native Spin(8) Weyl lifts as actual rational Albert automorphisms

The four explicit triality triples from `RationalOctonionSpin8WeylLift` act on
the three off-diagonal octonion slots of the repo-native rational Albert
carrier, fixing the three diagonal scalars.  Local exact-rational Python
preflight checks arbitrary randomized inputs for:

* each component preserving the octonion norm;
* preservation of the standard Albert cubic;
* preservation of the full coordinate Jordan product.

This owner source-writes those polynomial obligations directly.  No appeal to
group order or dimension is used.
-/

namespace Integration.RationalAlbertSpin8Automorphism

open Integration.RationalCayleyDicksonOctonion
open Integration.RationalAlbertNative
open Integration.RationalAlbertTrialityBasis
open Integration.RationalOctonionTriality192
open Integration.RationalOctonionSpin8WeylLift
open Integration.F4D4StandardTrialityRecognition
open RationalQuaternion RationalOctonion RationalAlbertNative.RationalAlbert

abbrev O8 := RationalOctonion
abbrev A27 := RationalAlbertNative.RationalAlbert

/-- Literal eight rational coordinates. -/
def octCoord (x : O8) : Fin 8 → ℚ :=
  ![x.first.q0,x.first.q1,x.first.q2,x.first.q3,
    x.second.q0,x.second.q1,x.second.q2,x.second.q3]

/-- Reconstruct an octonion from eight coordinates. -/
def octOfCoord (f : Fin 8 → ℚ) : O8 :=
  ⟨⟨f 0,f 1,f 2,f 3⟩,⟨f 4,f 5,f 6,f 7⟩⟩

@[simp] theorem octOfCoord_octCoord (x : O8) : octOfCoord (octCoord x) = x := by
  rcases x with ⟨⟨a0,a1,a2,a3⟩,⟨a4,a5,a6,a7⟩⟩
  rfl

/-- Linear signed-permutation action.  The finite Spin-lift maps are genuine
permutations, so exactly one input contributes to every output coordinate. -/
def actSigned (g : SignedBasisMap) (x : O8) : O8 :=
  octOfCoord fun j =>
    ∑ i : Fin 8, if g.perm i = j then signQ g i * octCoord x i else 0

/-- On literal basis vectors this realizes the defining signed permutation. -/
theorem actSigned_octBasis (g : SignedBasisMap)
    (hg : Function.Bijective g.perm) (i : Fin 8) :
    actSigned g (octBasis i) = signQ g i • octBasis (g.perm i) := by
  apply RationalOctonion.ext <;> apply RationalQuaternion.ext <;>
    simp [actSigned, octOfCoord, octCoord, octBasis, signQ] <;>
    aesop

/-- The four Spin lifts have permutation components. -/
theorem spin_component_bijective :
    ∀ s,
      Function.Bijective (spinLift s).left.perm ∧
      Function.Bijective (spinLift s).middle.perm ∧
      Function.Bijective (spinLift s).right.perm := by
  native_decide

/-- Every component of every selected Spin lift preserves the native octonion
quadratic norm. -/
theorem spin_components_preserve_norm :
    ∀ s x,
      RationalOctonion.normSq (actSigned (spinLift s).left x) = RationalOctonion.normSq x ∧
      RationalOctonion.normSq (actSigned (spinLift s).middle x) = RationalOctonion.normSq x ∧
      RationalOctonion.normSq (actSigned (spinLift s).right x) = RationalOctonion.normSq x := by
  intro s x
  rcases x with ⟨⟨a0,a1,a2,a3⟩,⟨a4,a5,a6,a7⟩⟩
  fin_cases s <;>
    simp [actSigned, octOfCoord, octCoord, spinLift, liftCenter, liftOuter0,
      liftOuter1, liftOuter2, signQ, RationalOctonion.normSq,
      RationalQuaternion.normSq] <;> ring

/-- Albert action of one Spin lift: diagonal coordinates fixed, three
triality components acting on `(off12,off20,off01)` in the same order as the
native cubic `Re((off12*off20)*off01)`. -/
def spinAlbertAction (s : D4Simple) (X : A27) : A27 :=
  ⟨X.diagonal0,X.diagonal1,X.diagonal2,
   actSigned (spinLift s).left X.off12,
   actSigned (spinLift s).middle X.off20,
   actSigned (spinLift s).right X.off01⟩

@[simp] theorem spin_albert_fixes_unit :
    ∀ s, spinAlbertAction s unit = unit := by
  intro s
  fin_cases s <;>
    rfl

@[simp] theorem spin_albert_preserves_trace :
    ∀ s X, trace (spinAlbertAction s X) = trace X := by
  intro s X
  rfl

/-- Exact standard-cubic preservation.  This is the native rational Albert
cubic, not the quarantined external-donor determinant candidate. -/
theorem spin_albert_preserves_cubic :
    ∀ s X, cubic (spinAlbertAction s X) = cubic X := by
  intro s X
  rcases X with ⟨a,b,c,
    ⟨⟨x0,x1,x2,x3⟩,⟨x4,x5,x6,x7⟩⟩,
    ⟨⟨y0,y1,y2,y3⟩,⟨y4,y5,y6,y7⟩⟩,
    ⟨⟨z0,z1,z2,z3⟩,⟨z4,z5,z6,z7⟩⟩⟩
  fin_cases s <;>
    simp [spinAlbertAction, actSigned, octOfCoord, octCoord, spinLift,
      liftCenter, liftOuter0, liftOuter1, liftOuter2, signQ,
      cubic, RationalOctonion.normSq, RationalOctonion.realPart,
      RationalOctonion.mul, RationalQuaternion.mul, RationalQuaternion.conj] <;>
    ring

/-- Direct coordinate proof that the same four lifts preserve the exceptional
Jordan product.  This is stronger than cubic preservation alone and therefore
does not depend on the still-general cubic-rigidity interface. -/
theorem spin_albert_preserves_jordan_product :
    ∀ s X Y,
      spinAlbertAction s (jordanProduct X Y) =
        jordanProduct (spinAlbertAction s X) (spinAlbertAction s Y) := by
  intro s X Y
  rcases X with ⟨a,b,c,
    ⟨⟨x0,x1,x2,x3⟩,⟨x4,x5,x6,x7⟩⟩,
    ⟨⟨y0,y1,y2,y3⟩,⟨y4,y5,y6,y7⟩⟩,
    ⟨⟨z0,z1,z2,z3⟩,⟨z4,z5,z6,z7⟩⟩⟩
  rcases Y with ⟨d,e,f,
    ⟨⟨u0,u1,u2,u3⟩,⟨u4,u5,u6,u7⟩⟩,
    ⟨⟨v0,v1,v2,v3⟩,⟨v4,v5,v6,v7⟩⟩,
    ⟨⟨w0,w1,w2,w3⟩,⟨w4,w5,w6,w7⟩⟩⟩
  fin_cases s <;>
    apply RationalAlbert.ext <;>
    try { apply RationalOctonion.ext <;> apply RationalQuaternion.ext } <;>
    simp [spinAlbertAction, actSigned, octOfCoord, octCoord, spinLift,
      liftCenter, liftOuter0, liftOuter1, liftOuter2, signQ,
      jordanProduct, innerO, halfO,
      RationalOctonion.mul, RationalOctonion.conj, RationalOctonion.realPart,
      RationalQuaternion.mul, RationalQuaternion.conj] <;>
    ring

/-- Exact finite automorphism receipt for the four D4 simple lifts. -/
structure NativeSpinAlbertAutomorphism (s : D4Simple) where
  map : A27 → A27
  map_eq : map = spinAlbertAction s
  fixesUnit : map unit = unit
  preservesTrace : ∀ X, trace (map X) = trace X
  preservesCubic : ∀ X, cubic (map X) = cubic X
  preservesJordan : ∀ X Y, map (jordanProduct X Y) = jordanProduct (map X) (map Y)


def nativeSpinAutomorphism (s : D4Simple) : NativeSpinAlbertAutomorphism s where
  map := spinAlbertAction s
  map_eq := rfl
  fixesUnit := spin_albert_fixes_unit s
  preservesTrace := spin_albert_preserves_trace s
  preservesCubic := spin_albert_preserves_cubic s
  preservesJordan := spin_albert_preserves_jordan_product s

inductive FourSpinAlbertAutomorphismsCreateFullF4 : Prop

theorem four_spin_automorphisms_do_not_create_full_f4 :
    ¬ FourSpinAlbertAutomorphismsCreateFullF4 := by intro h; cases h

structure Boundary where
  signedOctonionActionTyped : Bool
  fourSpinComponentsNormPreserving : Bool
  fourNativeAlbertUnitPreserving : Bool
  fourNativeAlbertTracePreserving : Bool
  fourNativeAlbertCubicPreserving : Bool
  fourNativeAlbertJordanPreserving : Bool
  fourNativeD4SpinAlbertAutomorphismsPaid : Bool
  fullF4Paid : Bool
  deriving Repr


def canonicalBoundary : Boundary where
  signedOctonionActionTyped := true
  fourSpinComponentsNormPreserving := true
  fourNativeAlbertUnitPreserving := true
  fourNativeAlbertTracePreserving := true
  fourNativeAlbertCubicPreserving := true
  fourNativeAlbertJordanPreserving := true
  fourNativeD4SpinAlbertAutomorphismsPaid := true
  fullF4Paid := false

end Integration.RationalAlbertSpin8Automorphism
