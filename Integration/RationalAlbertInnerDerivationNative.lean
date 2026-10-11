import Integration.RationalAlbertNative
import Mathlib

/-!
# Arbitrary inner derivations of the native rational Albert algebra

For the literal rational Albert Jordan product define

  D_{a,b}(x) = a ∘ (b ∘ x) - b ∘ (a ∘ x).

The companion Agda owner proves the derivation law by exact rational polynomial
exhaustion.  This Lean mirror does the same directly from the native coordinate
formula; it is strictly stronger than checking only the 351 coordinate-basis
pairs.
-/

namespace Integration.RationalAlbertInnerDerivationNative

open Integration.RationalCayleyDicksonOctonion
open Integration.RationalAlbertNative
open RationalQuaternion RationalOctonion RationalAlbertNative.RationalAlbert

abbrev A27 := RationalAlbertNative.RationalAlbert

def subA (x y : A27) : A27 := x + (-y)

def leftJordan (x : A27) : A27 → A27 := fun y => jordanProduct x y

def innerDerivation (a b x : A27) : A27 :=
  subA (jordanProduct a (jordanProduct b x))
    (jordanProduct b (jordanProduct a x))

def DerivationLaw (D : A27 → A27) : Prop :=
  ∀ x y,
    D (jordanProduct x y) =
      jordanProduct (D x) y + jordanProduct x (D y)

/-- Every commutator of left Jordan multiplications is a derivation on the
actual rational Albert product.  This is an arbitrary-element theorem, not a
basis-only diagnostic. -/
theorem inner_derivation_law (a b : A27) :
    DerivationLaw (innerDerivation a b) := by
  intro x y
  rcases a with ⟨a0,a1,a2,ax,ay,az⟩
  rcases b with ⟨b0,b1,b2,bx,by,bz⟩
  rcases x with ⟨x0,x1,x2,xx,xy,xz⟩
  rcases y with ⟨y0,y1,y2,yx,yy,yz⟩
  rcases ax with ⟨ax1,ax2⟩; rcases ay with ⟨ay1,ay2⟩; rcases az with ⟨az1,az2⟩
  rcases bx with ⟨bx1,bx2⟩; rcases by with ⟨by1,by2⟩; rcases bz with ⟨bz1,bz2⟩
  rcases xx with ⟨xx1,xx2⟩; rcases xy with ⟨xy1,xy2⟩; rcases xz with ⟨xz1,xz2⟩
  rcases yx with ⟨yx1,yx2⟩; rcases yy with ⟨yy1,yy2⟩; rcases yz with ⟨yz1,yz2⟩
  ext <;>
    try { apply RationalOctonion.ext <;> apply RationalQuaternion.ext } <;>
    simp [innerDerivation, leftJordan, subA, jordanProduct, innerO, halfO,
      RationalOctonion.mul, RationalOctonion.conj, RationalOctonion.realPart,
      RationalQuaternion.mul, RationalQuaternion.conj] <;> ring

/-- Commutator antisymmetry is literal. -/
theorem inner_derivation_swap (a b x : A27) :
    innerDerivation b a x = -(innerDerivation a b x) := by
  rcases a with ⟨a0,a1,a2,ax,ay,az⟩
  rcases b with ⟨b0,b1,b2,bx,by,bz⟩
  rcases x with ⟨x0,x1,x2,xx,xy,xz⟩
  ext <;> simp [innerDerivation, subA, jordanProduct] <;> ring

structure Boundary where
  literalInnerDerivationPaid : Bool
  arbitraryDerivationLawPaid : Bool
  basisOnlyHypothesisRemoved : Bool
  rank52KernelProofPaidHere : Bool
  f4LieRecognitionPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  literalInnerDerivationPaid := true
  arbitraryDerivationLawPaid := true
  basisOnlyHypothesisRemoved := true
  rank52KernelProofPaidHere := false
  f4LieRecognitionPaidHere := false

end Integration.RationalAlbertInnerDerivationNative
