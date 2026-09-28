import Mathlib.RingTheory.WittVector.Compare
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Concrete p=2 Witt power-series carrier

Mathlib already owns the algebraic carriers needed for the base of the
supersingular universal deformation:

  F_2        := ZMod 2
  W(F_2)     := WittVector 2 (ZMod 2)
  W(F_2)[[t]] := PowerSeries (WittVector 2 (ZMod 2)).

It also owns the ring equivalence
  WittVector 2 (ZMod 2) ≃+* ℤ_[2].

This file pays only the algebraic carrier layer.  It does not claim the
specific complete-local topology/universal elliptic family required by the
Katz--Mazur deformation theorem.
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
  formalParameterXPaid : Bool
  completeLocalTopologyForUniversalDeformationClaimed : Bool
  universalEllipticFamilyClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  zmodTwoResidueFieldCarrierPaid := true
  pTypicalWittCarrierPaid := true
  powerSeriesCarrierPaid := true
  wittRingEquivTwoAdicsPaid := true
  formalParameterXPaid := true
  completeLocalTopologyForUniversalDeformationClaimed := false
  universalEllipticFamilyClaimed := false

end Integration.OggSSPP2WittPowerSeriesBase
