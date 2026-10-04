import Mathlib.RingTheory.WittVector.Compare
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.AdicCompletion.Completeness
import Integration.OggSSPP2WittPowerSeriesBase

/-!
# Completeness layers on the p=2 Witt power-series base

For
  A := WittVector 2 (ZMod 2)
  R := PowerSeries A

this module pays two distinct Mathlib-backed completeness statements:

1. Pull the p-adic uniformity on ℤ_[2] back along
     WittVector.equiv 2 : A ≃+* ℤ_[2].
   Then A is complete, and with the coefficientwise PowerSeries Pi topology,
   R is complete.

2. Independently, Mathlib proves that a one-variable formal power-series ring
   is X-adically complete:
     IsAdicComplete (Ideal.span {PowerSeries.X}) R.

Neither statement is identified here with completeness for the maximal ideal
(2, X), which is the topology relevant to the usual complete-local universal
supersingular deformation base.  That comparison/realization remains separate.
-/

namespace Integration.OggSSPP2WittPowerSeriesCompleteness

open Integration.OggSSPP2WittPowerSeriesBase

noncomputable def p2WittUniformSpace : UniformSpace P2WittRing :=
  UniformSpace.comap p2WittEquivPadicInt inferInstance

noncomputable local instance : UniformSpace P2WittRing :=
  p2WittUniformSpace

theorem p2WittEquivPadicInt_isUniformEmbedding :
    IsUniformEmbedding p2WittEquivPadicInt :=
  isUniformEmbedding_comap p2WittEquivPadicInt.injective

noncomputable def p2WittCompleteSpace : CompleteSpace P2WittRing :=
  (p2WittEquivPadicInt_isUniformEmbedding.isUniformInducing.completeSpace_congr
      p2WittEquivPadicInt.surjective).mpr inferInstance

noncomputable local instance : CompleteSpace P2WittRing :=
  p2WittCompleteSpace

noncomputable local instance : IsLocalRing P2WittRing :=
  p2WittIsLocalRing

noncomputable def p2WittMaximalIdealAdicallyComplete :
    IsAdicComplete (IsLocalRing.maximalIdeal P2WittRing) P2WittRing := by
  apply
    (IsAdicComplete.congr_ringEquiv
      (IsLocalRing.maximalIdeal P2WittRing)
      p2WittEquivPadicInt).mp
  simpa using
    (inferInstance :
      IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[2]) ℤ_[2])

open scoped PowerSeries.WithPiTopology

noncomputable def p2PowerSeriesCoefficientwiseComplete :
    CompleteSpace P2WittPowerSeriesBase :=
  inferInstance

noncomputable def p2PowerSeriesXAdicallyComplete :
    IsAdicComplete
      (Ideal.span ({PowerSeries.X} : Set P2WittPowerSeriesBase))
      P2WittPowerSeriesBase :=
  inferInstance

structure Boundary where
  pAdicUniformityPulledBackToWittRing : Bool
  wittRingCompleteUnderPulledBackUniformity : Bool
  coefficientMaximalIdealAdicComplete : Bool
  coefficientwisePowerSeriesComplete : Bool
  xAdicPowerSeriesComplete : Bool
  coefficientwiseTopologyIdentifiedWithMaximalIdealTopology : Bool
  xAdicTopologyIdentifiedWithMaximalIdealTopology : Bool
  maximalIdealTwoXCompletenessPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  pAdicUniformityPulledBackToWittRing := true
  wittRingCompleteUnderPulledBackUniformity := true
  coefficientMaximalIdealAdicComplete := true
  coefficientwisePowerSeriesComplete := true
  xAdicPowerSeriesComplete := true
  coefficientwiseTopologyIdentifiedWithMaximalIdealTopology := false
  xAdicTopologyIdentifiedWithMaximalIdealTopology := false
  maximalIdealTwoXCompletenessPaid := false

end Integration.OggSSPP2WittPowerSeriesCompleteness
