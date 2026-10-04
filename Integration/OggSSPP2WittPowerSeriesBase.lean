import Mathlib.RingTheory.WittVector.Compare
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Concrete F2-specialized p=2 Witt power-series carrier

Mathlib owns a concrete algebraic specialization relevant to the p=2 lane:

  F_2        := ZMod 2
  W(F_2)     := WittVector 2 (ZMod 2)
  W(F_2)[[t]] := PowerSeries (WittVector 2 (ZMod 2)).

It also owns the ring equivalence
  WittVector 2 (ZMod 2) ≃+* ℤ_[2].

This file pays only the F2-specialized algebraic carrier layer.  Katz--Mazur's
universal deformation is formulated over W(k)[[t]] for the actual residue field
k of the supersingular curve.  No theorem here identifies that source residue
field with F2 or proves descent/base change to this specialization.
-/

namespace Integration.OggSSPP2WittPowerSeriesBase

abbrev P2ResidueField := ZMod 2
abbrev P2WittRing := WittVector 2 P2ResidueField
abbrev P2WittPowerSeriesBase := PowerSeries P2WittRing

def p2ResidueFieldCommRing : CommRing P2ResidueField :=
  inferInstance

noncomputable def p2WittCommRing : CommRing P2WittRing :=
  inferInstance

noncomputable def p2PowerSeriesCommRing : CommRing P2WittPowerSeriesBase :=
  inferInstance

noncomputable def p2WittEquivPadicInt :
    P2WittRing ≃+* ℤ_[2] :=
  WittVector.equiv 2

noncomputable def p2WittIsLocalRing : IsLocalRing P2WittRing :=
  IsLocalRing.of_surjective'
    p2WittEquivPadicInt.symm.toRingHom
    p2WittEquivPadicInt.symm.surjective

noncomputable local instance : IsLocalRing P2WittRing :=
  p2WittIsLocalRing

noncomputable def p2PowerSeriesIsLocalRing :
    IsLocalRing P2WittPowerSeriesBase :=
  inferInstance

def formalParameter :
    P2WittPowerSeriesBase :=
  PowerSeries.X

theorem residue_characteristic_is_two :
    ringChar P2ResidueField = 2 := by
  decide

structure Boundary where
  zmodTwoResidueFieldCarrierPaid : Bool
  pTypicalWittCarrierPaid : Bool
  powerSeriesCarrierPaid : Bool
  wittRingEquivTwoAdicsPaid : Bool
  wittRingLocalStructurePaid : Bool
  powerSeriesLocalStructurePaid : Bool
  formalParameterXPaid : Bool
  f2SpecializationOnly : Bool
  universalSourceResidueFieldIdentifiedWithF2 : Bool
  topologicalCompletenessForUniversalDeformationClaimed : Bool
  universalEllipticFamilyClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  zmodTwoResidueFieldCarrierPaid := true
  pTypicalWittCarrierPaid := true
  powerSeriesCarrierPaid := true
  wittRingEquivTwoAdicsPaid := true
  wittRingLocalStructurePaid := true
  powerSeriesLocalStructurePaid := true
  formalParameterXPaid := true
  f2SpecializationOnly := true
  universalSourceResidueFieldIdentifiedWithF2 := false
  topologicalCompletenessForUniversalDeformationClaimed := false
  universalEllipticFamilyClaimed := false

end Integration.OggSSPP2WittPowerSeriesBase
