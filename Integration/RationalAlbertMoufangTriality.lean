import Integration.RationalAlbertNative
import Integration.AlbertTrialityCubicCompiler
import Mathlib

/-!
# Native rational Moufang triality on the Albert algebra

For the unit imaginary octonion `u=e1`, alternativity gives the Moufang identity

  (u*x) * (y*u) = u * (x*y) * u.

Thus the three maps

  L_u(x)=u*x,  R_u(y)=y*u,  M_u(z)=(u*z)*u

form an explicit triality triple.  Acting by these maps on the three octonion
slots of the native rational Albert carrier preserves both the coordinate Jordan
product and the standard cubic norm.  This is a concrete non-diagonal triality
automorphism on the same algebra used by the F4 max-cut.
-/

namespace Integration.RationalAlbertMoufangTriality

open Integration.RationalCayleyDicksonOctonion
open Integration.RationalAlbertNative
open RationalQuaternion RationalOctonion RationalAlbertNative.RationalAlbert

abbrev O8 := RationalOctonion
abbrev A27 := RationalAlbertNative.RationalAlbert

/-- Selected unit imaginary basis octonion. -/
def u : O8 := ⟨⟨0,1,0,0⟩,0⟩

def leftU (x : O8) : O8 := u * x
def rightU (x : O8) : O8 := x * u
def middleU (x : O8) : O8 := (u * x) * u

/-- The selected Moufang triality identity, proved directly in the repository's
Cayley-Dickson convention. -/
theorem selected_moufang_triality (x y : O8) :
    leftU x * rightU y = middleU (x * y) := by
  rcases x with ⟨a,b⟩; rcases y with ⟨c,d⟩
  rcases a with ⟨a0,a1,a2,a3⟩; rcases b with ⟨b0,b1,b2,b3⟩
  rcases c with ⟨c0,c1,c2,c3⟩; rcases d with ⟨d0,d1,d2,d3⟩
  ext <;> apply RationalQuaternion.ext <;>
    simp [leftU, rightU, middleU, u, HMul.hMul, Mul.mul,
      RationalOctonion.mul, RationalQuaternion.mul, RationalQuaternion.conj] <;> ring

/-- Native Albert transformation attached to the selected triality triple. -/
def trialityA (X : A27) : A27 :=
  ⟨X.diagonal0, X.diagonal1, X.diagonal2,
   leftU X.off12, rightU X.off20, middleU X.off01⟩

/-- The transformation fixes the distinguished Albert unit. -/
@[simp] theorem triality_unit : trialityA unit = unit := by
  ext <;> simp [trialityA, unit, leftU, rightU, middleU, u,
    HMul.hMul, Mul.mul, RationalOctonion.mul, RationalQuaternion.mul,
    RationalQuaternion.conj]

/-- Exact preservation of the native Jordan product. -/
theorem triality_preserves_product (X Y : A27) :
    trialityA (jordanProduct X Y) = jordanProduct (trialityA X) (trialityA Y) := by
  rcases X with ⟨a,b,c,x,y,z⟩; rcases Y with ⟨d,e,f,p,q,r⟩
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩; rcases z with ⟨z1,z2⟩
  rcases p with ⟨p1,p2⟩; rcases q with ⟨q1,q2⟩; rcases r with ⟨r1,r2⟩
  ext <;> try { apply RationalOctonion.ext <;> apply RationalQuaternion.ext } <;>
    simp [trialityA, leftU, rightU, middleU, u, jordanProduct, innerO, halfO,
      HMul.hMul, Mul.mul, RationalOctonion.mul, RationalOctonion.conj,
      RationalOctonion.realPart, RationalQuaternion.mul, RationalQuaternion.conj] <;> ring

/-- Exact preservation of the standard Albert cubic. -/
theorem triality_preserves_cubic (X : A27) : cubic (trialityA X) = cubic X := by
  rcases X with ⟨a,b,c,x,y,z⟩
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩; rcases z with ⟨z1,z2⟩
  simp [trialityA, leftU, rightU, middleU, u, cubic,
    RationalOctonion.normSq, RationalOctonion.realPart,
    HMul.hMul, Mul.mul, RationalOctonion.mul, RationalQuaternion.mul,
    RationalQuaternion.normSq, RationalQuaternion.conj]
  ring

/-- The selected monomial triality generator has order dividing four. -/
theorem triality_fourth_power (X : A27) :
    trialityA (trialityA (trialityA (trialityA X))) = X := by
  rcases X with ⟨a,b,c,x,y,z⟩
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩; rcases z with ⟨z1,z2⟩
  ext <;> try { apply RationalOctonion.ext <;> apply RationalQuaternion.ext } <;>
    simp [trialityA, leftU, rightU, middleU, u,
      HMul.hMul, Mul.mul, RationalOctonion.mul, RationalQuaternion.mul,
      RationalQuaternion.conj] <;> ring

structure Boundary where
  selectedMoufangIdentityPaid : Bool
  nativeTrialityMapPaid : Bool
  nativeTrialityFixesUnitPaid : Bool
  nativeTrialityProductPreservationPaid : Bool
  nativeTrialityCubicPreservationPaid : Bool
  nativeTrialityFiniteOrderPaid : Bool
  fullD4TrialityActionPaidHere : Bool
  fullF4PaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  selectedMoufangIdentityPaid := true
  nativeTrialityMapPaid := true
  nativeTrialityFixesUnitPaid := true
  nativeTrialityProductPreservationPaid := true
  nativeTrialityCubicPreservationPaid := true
  nativeTrialityFiniteOrderPaid := true
  fullD4TrialityActionPaidHere := false
  fullF4PaidHere := false

end Integration.RationalAlbertMoufangTriality
