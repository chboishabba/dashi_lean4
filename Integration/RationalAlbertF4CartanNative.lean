import Integration.RationalAlbertInnerDerivationNative
import Integration.RationalAlbertTrialityBasis
import Mathlib

/-!
# Native Cartan/triality operators for the rational Albert derivation algebra

Lean same-object mirror of the explicit Cartan selected independently on the
Agda/exact-producer side.  The four operators are literal Albert inner
derivations

  [L_x0,L_x1], [L_x2,L_x3], [L_x4,L_x5], [L_x6,L_x7]

inside the first octonion slot.  This file pays the operators and their exact
triality action directly on the native RationalAlbert carrier.  It deliberately
stops before the Q(i) spectral-projector/root-space decomposition, which remains
an exact executable receipt on the companion Agda branch.
-/

namespace Integration.RationalAlbertF4CartanNative

open Integration.RationalAlbertNative
open Integration.RationalAlbertInnerDerivationNative
open Integration.RationalAlbertTrialityBasis
open RationalAlbertNative.RationalAlbert

abbrev A27 := RationalAlbertNative.RationalAlbert

/-- The four orthogonal coordinate-plane Cartan generators. -/
def cartanDerivation : Fin 4 → A27 → A27
  | 0 => innerDerivation (slotBasis 0 0) (slotBasis 0 1)
  | 1 => innerDerivation (slotBasis 0 2) (slotBasis 0 3)
  | 2 => innerDerivation (slotBasis 0 4) (slotBasis 0 5)
  | 3 => innerDerivation (slotBasis 0 6) (slotBasis 0 7)

/-- Every selected Cartan operator is an actual derivation of the same Albert
Jordan product. -/
theorem cartan_derivation_law (k : Fin 4) :
    DerivationLaw (cartanDerivation k) := by
  fin_cases k <;> exact inner_derivation_law _ _

/-- The four selected Albert inner derivations commute on arbitrary elements. -/
theorem cartan_commute (i j : Fin 4) (X : A27) :
    cartanDerivation i (cartanDerivation j X) =
      cartanDerivation j (cartanDerivation i X) := by
  fin_cases i <;> fin_cases j <;>
    rcases X with ⟨a,b,c,x,y,z⟩ <;>
    rcases x with ⟨x1,x2⟩ <;> rcases y with ⟨y1,y2⟩ <;> rcases z with ⟨z1,z2⟩ <;>
    ext <;> try { apply RationalOctonion.ext <;> apply RationalQuaternion.ext } <;>
    simp [cartanDerivation, innerDerivation, subA, slotBasis, octBasis,
      jordanProduct, innerO, halfO, RationalOctonion.mul,
      RationalOctonion.conj, RationalOctonion.realPart,
      RationalQuaternion.mul, RationalQuaternion.conj] <;> ring

/-- Expected vector-representation plane rotation on the first octonion slot. -/
def vectorExpected : Fin 4 → Fin 8 → A27
  | 0 => ![-slotBasis 0 1, slotBasis 0 0, 0, 0, 0, 0, 0, 0]
  | 1 => ![0, 0, -slotBasis 0 3, slotBasis 0 2, 0, 0, 0, 0]
  | 2 => ![0, 0, 0, 0, -slotBasis 0 5, slotBasis 0 4, 0, 0]
  | 3 => ![0, 0, 0, 0, 0, 0, -slotBasis 0 7, slotBasis 0 6]

/-- On the literal x-slot basis the Cartan is exactly four orthogonal plane
rotations. -/
theorem cartan_vector_plane_rotation :
    ∀ k i, cartanDerivation k (slotBasis 0 i) = vectorExpected k i := by
  native_decide

/-- On both half-spin slots every Cartan generator squares to -1/4. -/
theorem cartan_spin_square_minus_quarter :
    (∀ k i, cartanDerivation k (cartanDerivation k (slotBasis 1 i)) =
      (-1/4 : ℚ) • slotBasis 1 i) ∧
    (∀ k i, cartanDerivation k (cartanDerivation k (slotBasis 2 i)) =
      (-1/4 : ℚ) • slotBasis 2 i) := by
  native_decide

/-- Twice a Cartan generator, convenient for the chirality product. -/
def twiceCartan (k : Fin 4) (X : A27) : A27 := 2 • cartanDerivation k X

/-- Product of the four `2H_k` operators. -/
def chiralityOperator (X : A27) : A27 :=
  twiceCartan 3 (twiceCartan 2 (twiceCartan 1 (twiceCartan 0 X)))

/-- The two native half-spin slots have opposite chirality. -/
theorem cartan_spin_chirality :
    (∀ i, chiralityOperator (slotBasis 1 i) = slotBasis 1 i) ∧
    (∀ i, chiralityOperator (slotBasis 2 i) = -slotBasis 2 i) := by
  native_decide

structure Boundary where
  explicitFourCartanDerivationsPaid : Bool
  allFourAreDerivationsPaid : Bool
  cartanCommutationPaid : Bool
  vectorPlaneRotationPatternPaid : Bool
  spinSquarePatternPaid : Bool
  spinChiralityPatternPaid : Bool
  exactQISpectralProjectorsPaidHere : Bool
  splitF4RootDatumClassificationPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  explicitFourCartanDerivationsPaid := true
  allFourAreDerivationsPaid := true
  cartanCommutationPaid := true
  vectorPlaneRotationPatternPaid := true
  spinSquarePatternPaid := true
  spinChiralityPatternPaid := true
  exactQISpectralProjectorsPaidHere := false
  splitF4RootDatumClassificationPaidHere := false

end Integration.RationalAlbertF4CartanNative
