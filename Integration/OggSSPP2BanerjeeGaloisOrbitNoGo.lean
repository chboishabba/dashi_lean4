import Mathlib
import Integration.OggSSPP2BanerjeeF4UniversalDeformationSource

/-!
# Banerjee Galois sheet is not a ten-component orbit quotient

The exact finite carrier is

  GaloisInertiaState = GalSheet × (five inversion-inertia sectors).

The C₂ sheet involution is free: its orbit label is the inertia sector alone,
so it has FIVE orbits, not ten.  This rejects promotion of the ten-state
rechart as a pi₀ identification for the bare Galois C₂ action.

This is a DASHI finite reconstruction. It does NOT construct the actual
geometric action on the universal deformation or a Gamma_0(4) marked stack.
-/

namespace Integration.OggSSPP2BanerjeeGaloisOrbitNoGo

namespace B := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace I := Integration.OggSSPP2OrientedInertiaTenStateRecognition
namespace T := Integration.OggSSPP2F4AntipodalStratifiedRefinement

def flipSheet : B.GaloisSheet → B.GaloisSheet
  | .identity => .frobenius
  | .frobenius => .identity

theorem flipSheet_involutive (s : B.GaloisSheet) :
    flipSheet (flipSheet s) = s := by
  cases s <;> rfl

theorem flipSheet_fixed_point_free (s : B.GaloisSheet) :
    flipSheet s ≠ s := by
  cases s <;> decide

def galoisFlip : B.GaloisInertiaState → B.GaloisInertiaState
  | (g, i) => (flipSheet g, i)

theorem galoisFlip_involutive (s : B.GaloisInertiaState) :
    galoisFlip (galoisFlip s) = s := by
  rcases s with ⟨g, i⟩
  cases g <;> rfl

theorem galoisFlip_moves_every_state (s : B.GaloisInertiaState) :
    galoisFlip s ≠ s := by
  rcases s with ⟨g, i⟩
  cases g <;> simp [galoisFlip, flipSheet]

def galoisOrbitLabel :
    B.GaloisInertiaState → I.BinaryTetrahedralInversionOrbit :=
  Prod.snd

theorem galois_orbit_label_invariant (s : B.GaloisInertiaState) :
    galoisOrbitLabel (galoisFlip s) = galoisOrbitLabel s := rfl

def orbitRepresentative :
    I.BinaryTetrahedralInversionOrbit → B.GaloisInertiaState :=
  fun i => (.identity, i)

theorem orbit_representative_exact
    (i : I.BinaryTetrahedralInversionOrbit) :
    galoisOrbitLabel (orbitRepresentative i) = i := rfl

theorem same_label_iff_equal_or_flip
    (s t : B.GaloisInertiaState) :
    galoisOrbitLabel s = galoisOrbitLabel t ↔
      t = s ∨ t = galoisFlip s := by
  rcases s with ⟨g, i⟩
  rcases t with ⟨h, j⟩
  cases g <;> cases h <;>
    simp [galoisOrbitLabel, galoisFlip, flipSheet, Prod.mk.injEq]

theorem galois_orbit_count_is_five :
    Fintype.card I.BinaryTetrahedralInversionOrbit = 5 := by
  decide

theorem marked_sector_count_is_ten :
    Fintype.card B.GaloisInertiaState = 10 :=
  B.galois_inertia_state_cardinality

theorem gal_orbits_are_not_ten :
    Fintype.card I.BinaryTetrahedralInversionOrbit ≠
      Fintype.card B.GaloisInertiaState := by
  rw [galois_orbit_count_is_five, marked_sector_count_is_ten]
  decide

theorem galois_flip_changes_target_label (s : B.GaloisInertiaState) :
    B.toTarget (galoisFlip s) ≠ B.toTarget s := by
  intro h
  have e : galoisFlip s = s :=
    B.equivTarget.injective h
  exact galoisFlip_moves_every_state s e

/--
A target whose action on ten labels is identity cannot have an equivariant
ten-state identity-of-presentation map from the bare Gal-sheet action.
-/
theorem no_equivariance_to_identity_ten_label_action :
    ¬ (∀ s : B.GaloisInertiaState,
        B.toTarget (galoisFlip s) = B.toTarget s) := by
  intro h
  exact galois_flip_changes_target_label (.identity, .identity) (h _)

structure Boundary where
  bareGaloisFlipIsFree : Bool
  bareGaloisOrbitCountFive : Bool
  markedLabelsCountTen : Bool
  tenLabelsAreBareGaloisPi0 : Bool
  equivariantToIdentityTenLabelAction : Bool
  arithmeticGamma0FourIdentificationClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  bareGaloisFlipIsFree := true
  bareGaloisOrbitCountFive := true
  markedLabelsCountTen := true
  tenLabelsAreBareGaloisPi0 := false
  equivariantToIdentityTenLabelAction := false
  arithmeticGamma0FourIdentificationClaimed := false

end Integration.OggSSPP2BanerjeeGaloisOrbitNoGo
