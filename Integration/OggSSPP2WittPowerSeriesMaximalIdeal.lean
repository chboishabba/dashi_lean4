import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Integration.OggSSPP2WittPowerSeriesBase
import Integration.OggSSPP2WittPowerSeriesCompleteness

/-!
# Candidate maximal-ideal presentation for the p=2 deformation base

For A = W(F_2) and R = A[[X]], the universal deformation is naturally
completed at the maximal ideal combining the coefficient maximal ideal with X.

This file starts from the exact candidate ideal

  mCandidate := (maximalIdeal A).comap PowerSeries.constantCoeff

and proves that it IS the actual maximal ideal of A[[X]].  It then proves the
stronger two-part presentation

  maximalIdeal A[[X]] = C(maximalIdeal A) + (X).

It still does not identify the coefficient maximal ideal with a literal
uniformizer such as 2; that requires a separate coefficient-ring theorem.
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

theorem deformationIdealCandidate_eq_maximalIdeal :
    deformationIdealCandidate =
      IsLocalRing.maximalIdeal P2WittPowerSeriesBase := by
  ext f
  simp only [deformationIdealCandidate, coefficientMaximalIdeal,
    Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact not_congr PowerSeries.isUnit_iff_constantCoeff

theorem maximalIdeal_membership_iff_constantCoeff
    (f : P2WittPowerSeriesBase) :
    f ∈ IsLocalRing.maximalIdeal P2WittPowerSeriesBase ↔
      PowerSeries.constantCoeff f ∈
        IsLocalRing.maximalIdeal P2WittRing := by
  rw [← deformationIdealCandidate_eq_maximalIdeal]
  rfl

noncomputable def coefficientMaximalIdealInPowerSeries :
    Ideal P2WittPowerSeriesBase :=
  coefficientMaximalIdeal.map PowerSeries.C

noncomputable def deformationTwoPartIdeal :
    Ideal P2WittPowerSeriesBase :=
  coefficientMaximalIdealInPowerSeries ⊔
    Ideal.span ({PowerSeries.X} : Set P2WittPowerSeriesBase)

theorem constant_of_coefficient_maximal_mem_twoPart
    {a : P2WittRing}
    (ha : a ∈ coefficientMaximalIdeal) :
    PowerSeries.C a ∈ deformationTwoPartIdeal := by
  apply Ideal.mem_sup_left
  exact Ideal.mem_map_of_mem PowerSeries.C ha

theorem X_mem_twoPart :
    PowerSeries.X ∈ deformationTwoPartIdeal := by
  apply Ideal.mem_sup_right
  exact Ideal.subset_span (Set.mem_singleton PowerSeries.X)

theorem deformationTwoPartIdeal_le_maximalIdeal :
    deformationTwoPartIdeal ≤
      IsLocalRing.maximalIdeal P2WittPowerSeriesBase := by
  apply sup_le
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change PowerSeries.C a ∈
      IsLocalRing.maximalIdeal P2WittPowerSeriesBase
    rw [maximalIdeal_membership_iff_constantCoeff]
    simpa using ha
  · rw [Ideal.span_le]
    intro f hf
    simp only [Set.mem_singleton_iff] at hf
    subst f
    rw [← deformationIdealCandidate_eq_maximalIdeal]
    exact X_mem_deformationIdealCandidate

theorem maximalIdeal_le_deformationTwoPartIdeal :
    IsLocalRing.maximalIdeal P2WittPowerSeriesBase ≤
      deformationTwoPartIdeal := by
  intro f hf
  have hconst :
      PowerSeries.constantCoeff f ∈ coefficientMaximalIdeal := by
    simpa [coefficientMaximalIdeal] using
      (maximalIdeal_membership_iff_constantCoeff f).mp hf
  have hC :
      PowerSeries.C (PowerSeries.constantCoeff f) ∈
        deformationTwoPartIdeal :=
    constant_of_coefficient_maximal_mem_twoPart hconst
  have hX :
      f - PowerSeries.C (PowerSeries.constantCoeff f) ∈
        deformationTwoPartIdeal := by
    rw [PowerSeries.sub_const_eq_shift_mul_X]
    exact deformationTwoPartIdeal.mul_mem_left _ X_mem_twoPart
  have hadd := deformationTwoPartIdeal.add_mem hX hC
  simpa using hadd

theorem deformationTwoPartIdeal_eq_maximalIdeal :
    deformationTwoPartIdeal =
      IsLocalRing.maximalIdeal P2WittPowerSeriesBase :=
  le_antisymm
    deformationTwoPartIdeal_le_maximalIdeal
    maximalIdeal_le_deformationTwoPartIdeal

structure Boundary where
  coefficientMaximalIdealOwned : Bool
  deformationIdealCandidateOwned : Bool
  variableXInCandidatePaid : Bool
  candidateIdentifiedWithPowerSeriesMaximalIdeal : Bool
  candidateIdentifiedWithLiteralTwoXIdeal : Bool
  coefficientMaxPlusXPresentationPaid : Bool
  candidateAdicCompletenessPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  coefficientMaximalIdealOwned := true
  deformationIdealCandidateOwned := true
  variableXInCandidatePaid := true
  candidateIdentifiedWithPowerSeriesMaximalIdeal := true
  candidateIdentifiedWithLiteralTwoXIdeal := false
  coefficientMaxPlusXPresentationPaid := true
  candidateAdicCompletenessPaid := false

end Integration.OggSSPP2WittPowerSeriesMaximalIdeal
