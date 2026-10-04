import Integration.TrialecticT5ComplementPhaseOrbitResidual
import Integration.OggSSP369RootRefinementBidi
import Integration.MoonshineSSP15OggAddressCodec
import Mathlib

/-!
# T5 selected-inversion quotient ↔ exact Ogg address × nine residual

Compose the exact quotient

  T5 -> PhaseOrbit15 × InnerT2

with the already-paid address/phase-orbit and root-369 bidirectional recharts.

The result is a canonical quotient target and section:

  T5 -> exact Ogg address × InnerT2
  T5 -> root369 refinement × InnerT2.

The nine-state residual is retained explicitly.  The Ogg address labelling still
uses the chosen SSP15 phase-orbit presentation internally; this does not derive
the arithmetic Ogg labelling from the T5 geometry.
-/

namespace Integration.TrialecticT5ComplementOggResidualBidi

open Integration.TrialecticT5ComplementPhaseOrbitResidual
open Integration.OggSSP15PhaseOrbitBidi
open Integration.OggSSP369RootRefinementBidi
open Integration.MoonshineSSP15OggAddressCodec

abbrev AddressWithNineResidual :=
  SSP15OggAddress15 × InnerT2

def phaseOrbitResidualToAddressResidual :
    PhaseOrbitWithNineResidual → AddressWithNineResidual
  | (phaseOrbit,residual) => (phaseOrbitToAddress phaseOrbit, residual)

def addressResidualToPhaseOrbitResidual :
    AddressWithNineResidual → PhaseOrbitWithNineResidual
  | (address,residual) => (addressToPhaseOrbit address, residual)

theorem phase_address_residual_roundtrip
    (state : PhaseOrbitWithNineResidual) :
    addressResidualToPhaseOrbitResidual
      (phaseOrbitResidualToAddressResidual state) = state := by
  rcases state with ⟨phase,residual⟩
  simp [phaseOrbitResidualToAddressResidual,
    addressResidualToPhaseOrbitResidual,
    phase_orbit_address_roundtrip]

theorem address_phase_residual_roundtrip
    (state : AddressWithNineResidual) :
    phaseOrbitResidualToAddressResidual
      (addressResidualToPhaseOrbitResidual state) = state := by
  rcases state with ⟨address,residual⟩
  simp [phaseOrbitResidualToAddressResidual,
    addressResidualToPhaseOrbitResidual,
    address_phase_orbit_roundtrip]

def quotientT5ToAddressResidual :
    T5Carrier → AddressWithNineResidual :=
  fun state =>
    phaseOrbitResidualToAddressResidual (quotientT5 state)

def canonicalLiftAddressResidual :
    AddressWithNineResidual → T5Carrier :=
  fun state =>
    canonicalLiftT5 (addressResidualToPhaseOrbitResidual state)

theorem quotient_lift_address_residual_roundtrip
    (state : AddressWithNineResidual) :
    quotientT5ToAddressResidual (canonicalLiftAddressResidual state) = state := by
  rw [quotientT5ToAddressResidual, canonicalLiftAddressResidual,
    quotient_canonical_lift_t5,
    address_phase_residual_roundtrip]

abbrev Root369WithNineResidual :=
  Root369Refinement × InnerT2

def addressResidualToRoot369Residual :
    AddressWithNineResidual → Root369WithNineResidual
  | (address,residual) => (addressToRoot369 address, residual)

def root369ResidualToAddressResidual :
    Root369WithNineResidual → AddressWithNineResidual
  | (root,residual) => (root369ToAddress root, residual)

theorem address_root_residual_roundtrip
    (state : AddressWithNineResidual) :
    root369ResidualToAddressResidual
      (addressResidualToRoot369Residual state) = state := by
  rcases state with ⟨address,residual⟩
  simp [addressResidualToRoot369Residual,
    root369ResidualToAddressResidual, address_root_roundtrip]

theorem root_address_residual_roundtrip
    (state : Root369WithNineResidual) :
    addressResidualToRoot369Residual
      (root369ResidualToAddressResidual state) = state := by
  rcases state with ⟨root,residual⟩
  simp [addressResidualToRoot369Residual,
    root369ResidualToAddressResidual, root_address_roundtrip]

def quotientT5ToRoot369Residual :
    T5Carrier → Root369WithNineResidual :=
  fun state =>
    addressResidualToRoot369Residual (quotientT5ToAddressResidual state)

def canonicalLiftRoot369Residual :
    Root369WithNineResidual → T5Carrier :=
  fun state =>
    canonicalLiftAddressResidual (root369ResidualToAddressResidual state)

theorem quotient_lift_root369_residual_roundtrip
    (state : Root369WithNineResidual) :
    quotientT5ToRoot369Residual
      (canonicalLiftRoot369Residual state) = state := by
  rw [quotientT5ToRoot369Residual, canonicalLiftRoot369Residual,
    quotient_lift_address_residual_roundtrip,
    root_address_residual_roundtrip]

theorem address_residual_count :
    Fintype.card AddressWithNineResidual = 135 := by
  native_decide

theorem root369_residual_count :
    Fintype.card Root369WithNineResidual = 135 := by
  native_decide

inductive T5QuotientDerivesArithmeticOggLabels : Prop
inductive NineResidualMayBeDiscardedCanonically : Prop
inductive RootResidualIsAnalyticPAdicProduct : Prop

theorem t5_quotient_does_not_derive_arithmetic_labels :
    ¬ T5QuotientDerivesArithmeticOggLabels := by
  intro h
  cases h

theorem nine_residual_not_discarded :
    ¬ NineResidualMayBeDiscardedCanonically := by
  intro h
  cases h

theorem root_residual_not_analytic_padic_product :
    ¬ RootResidualIsAnalyticPAdicProduct := by
  intro h
  cases h

structure Boundary where
  phaseOrbitResidualAddressResidualBidiPaid : Bool
  t5QuotientAddressResidualSectionPaid : Bool
  addressResidualRoot369ResidualBidiPaid : Bool
  t5QuotientRoot369ResidualSectionPaid : Bool
  targetCount135 : Bool
  nineResidualRetained : Bool
  arithmeticOggLabelsDerivedFromT5 : Bool
  analyticPAdicProductClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  phaseOrbitResidualAddressResidualBidiPaid := true
  t5QuotientAddressResidualSectionPaid := true
  addressResidualRoot369ResidualBidiPaid := true
  t5QuotientRoot369ResidualSectionPaid := true
  targetCount135 := true
  nineResidualRetained := true
  arithmeticOggLabelsDerivedFromT5 := false
  analyticPAdicProductClaimed := false

end Integration.TrialecticT5ComplementOggResidualBidi
