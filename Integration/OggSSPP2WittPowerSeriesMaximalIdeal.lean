import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Integration.OggSSPP2WittPowerSeriesBase
import Integration.OggSSPP2WittPowerSeriesCompleteness

/-!
# Candidate maximal-ideal presentation for the p=2 deformation base

For A = W(F_2) and R = A[[X]], the universal deformation is naturally
completed at the maximal ideal combining the coefficient maximal ideal with X.

This file introduces the exact candidate ideal already available from the
current Mathlib API:

  mCandidate := (maximalIdeal A).comap PowerSeries.constantCoeff.

It does NOT yet identify this ideal with IsLocalRing.maximalIdeal R or with a
literal generated ideal (2, X).  Those are the next algebraic same-object
theorems.
-/

namespace Integration.OggSSPP2WittPowerSeriesMaximalIdeal

open Integration.OggSSPP2WittPowerSeriesBase

noncomputable local instance : IsLocalRing P2WittRing :=
  p2WittIsLocalRing

noncomputable local instance : IsLocalRing P2WittPowerSeriesBase :=
  p2PowerSeriesIsLocalRing

noncomputable def coefficientMaximalIdeal :
    Ideal P2WittRing :=
  IsLocalRing.maximalIdeal P2WittRing

noncomputable def deformationIdealCandidate :
    Ideal P2WittPowerSeriesBase :=
  coefficientMaximalIdeal.comap PowerSeries.constantCoeff

theorem X_mem_deformationIdealCandidate :
    PowerSeries.X ∈ deformationIdealCandidate := by
  simp [deformationIdealCandidate, coefficientMaximalIdeal]

theorem constantCoeff_mem_maximal_of_mem_candidate
    {f : P2WittPowerSeriesBase}
    (hf : f ∈ deformationIdealCandidate) :
    PowerSeries.constantCoeff f ∈ coefficientMaximalIdeal :=
  hf

theorem candidate_membership_iff_constantCoeff
    (f : P2WittPowerSeriesBase) :
    f ∈ deformationIdealCandidate ↔
      PowerSeries.constantCoeff f ∈ coefficientMaximalIdeal :=
  Iff.rfl

structure Boundary where
  coefficientMaximalIdealOwned : Bool
  deformationIdealCandidateOwned : Bool
  variableXInCandidatePaid : Bool
  candidateIdentifiedWithPowerSeriesMaximalIdeal : Bool
  candidateIdentifiedWithLiteralTwoXIdeal : Bool
  candidateAdicCompletenessPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  coefficientMaximalIdealOwned := true
  deformationIdealCandidateOwned := true
  variableXInCandidatePaid := true
  candidateIdentifiedWithPowerSeriesMaximalIdeal := false
  candidateIdentifiedWithLiteralTwoXIdeal := false
  candidateAdicCompletenessPaid := false

end Integration.OggSSPP2WittPowerSeriesMaximalIdeal
