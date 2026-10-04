import Mathlib
import Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
import Integration.OggSSPP2F4FrobeniusCandidateNoGo

/-!
# Banerjee Galois sheet vs raw F4-orbit Frobenius: exact mismatch

There are two different C2-looking structures in the current p=2 lane:

1. the source-native Gal(F4/F2) sheet on Banerjee's universal deformation;
2. the raw F4/F2 Frobenius orbit classifier with zeroFixed, oneFixed,
   and conjugatePair strata.

They must not be silently identified.

The natural Galois involution toggles the Banerjee sheet. Under the current
ten-state rechart, this swaps the two centre states and therefore swaps
zeroFixed and oneFixed; on every noncentral inertia sector both sheets lie
over conjugatePair, so the coarse orbit is preserved there.

Hence the natural Banerjee Galois action cannot directly inhabit a source
contract that requires the current F4-orbit classifier to be invariant for all
states. The mismatch is exactly centre-local.
-/

namespace Integration.OggSSPP2BanerjeeGaloisVsF4OrbitNoGo

namespace Banerjee := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace F4 := Integration.OggSSPP2F4FrobeniusCandidateNoGo
namespace Target := Integration.OggSSPP2F4AntipodalStratifiedRefinement

def galoisInvolution :
    Banerjee.GaloisInertiaState → Banerjee.GaloisInertiaState
  | (.identity, inertia) => (.frobenius, inertia)
  | (.frobenius, inertia) => (.identity, inertia)

theorem galois_involution_involutive
    (s : Banerjee.GaloisInertiaState) :
    galoisInvolution (galoisInvolution s) = s := by
  rcases s with ⟨sheet, inertia⟩
  cases sheet <;> rfl

def coarseOrbit (s : Banerjee.GaloisInertiaState) : F4.F4Orbit :=
  Target.stratumOf (Banerjee.toTarget s)

theorem identity_centre_orbit :
    coarseOrbit (.identity, .identity) = .zeroFixed := rfl

theorem frobenius_centre_orbit :
    coarseOrbit (.frobenius, .identity) = .oneFixed := rfl

theorem centre_orbit_changes_under_galois :
    coarseOrbit (galoisInvolution (.identity, .identity)) ≠
      coarseOrbit (.identity, .identity) := by
  decide

theorem noncentral_orbit_preserved_centralMinusOne
    (sheet : Banerjee.GaloisSheet) :
    coarseOrbit (galoisInvolution (sheet, .centralMinusOne)) =
      coarseOrbit (sheet, .centralMinusOne) := by
  cases sheet <;> rfl

theorem noncentral_orbit_preserved_orderFour
    (sheet : Banerjee.GaloisSheet) :
    coarseOrbit (galoisInvolution (sheet, .orderFour)) =
      coarseOrbit (sheet, .orderFour) := by
  cases sheet <;> rfl

theorem noncentral_orbit_preserved_orderThreePair
    (sheet : Banerjee.GaloisSheet) :
    coarseOrbit (galoisInvolution (sheet, .orderThreePair)) =
      coarseOrbit (sheet, .orderThreePair) := by
  cases sheet <;> rfl

theorem noncentral_orbit_preserved_orderSixPair
    (sheet : Banerjee.GaloisSheet) :
    coarseOrbit (galoisInvolution (sheet, .orderSixPair)) =
      coarseOrbit (sheet, .orderSixPair) := by
  cases sheet <;> rfl

structure GloballyInvariantCoarseOrbit where
  invariant :
    ∀ s, coarseOrbit (galoisInvolution s) = coarseOrbit s

theorem natural_galois_cannot_preserve_current_coarse_orbit :
    ¬ GloballyInvariantCoarseOrbit := by
  intro h
  exact centre_orbit_changes_under_galois
    (h.invariant (.identity, .identity))

inductive MismatchLocus
  | duplicatedCentre
  deriving DecidableEq, Repr

structure Boundary where
  naturalGaloisInvolutionOwned : Bool
  involutivityPaid : Bool
  centreCoarseOrbitChanges : Bool
  allFourNoncentralInertiaSectorsPreserveCoarseOrbit : Bool
  globalCurrentF4OrbitInvariancePossible : Bool
  mismatchLocalizedToDuplicatedCentre : Bool
  galoisActionIdentifiedWithRawF4Frobenius : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  naturalGaloisInvolutionOwned := true
  involutivityPaid := true
  centreCoarseOrbitChanges := true
  allFourNoncentralInertiaSectorsPreserveCoarseOrbit := true
  globalCurrentF4OrbitInvariancePossible := false
  mismatchLocalizedToDuplicatedCentre := true
  galoisActionIdentifiedWithRawF4Frobenius := false

end Integration.OggSSPP2BanerjeeGaloisVsF4OrbitNoGo
