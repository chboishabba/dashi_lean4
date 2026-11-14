import Mathlib
import NobelChemistry.AsymmetricAutocatalysis

/-!
# Recoverable and consumer-relative observers for the finite chiral carrier

This is the Lean companion to the Agda cross-PR observer x-pollination. A
three-valued phase label forgets seed-vs-amplified magnitude. The residual
magnitude reopens the complete five-state fixture. The same coarse phase is
sufficient for handed branch but insufficient for full identity. A further
fixed/transverse quotient answers only racemic-vs-nonracemic.
-/

namespace NobelChemistry

open ChiralBias FutureBranch

inductive PhaseLabel where
  | one
  | zeta
  | zetaSq
  deriving DecidableEq, Repr

open PhaseLabel

def phaseLabel : ChiralBias → PhaseLabel
  | leftAmplified => zeta
  | leftSeed => zeta
  | racemic => one
  | rightSeed => zetaSq
  | rightAmplified => zetaSq

noncomputable def phaseValue : PhaseLabel → ℂ
  | one => 1
  | zeta => Spine.zeta
  | zetaSq => Spine.zeta ^ 2

@[simp] theorem phase_eq_phaseValue (x : ChiralBias) :
    phase x = phaseValue (phaseLabel x) := by
  cases x <;> rfl

/-- Label-level reflection corresponding to cyclotomic conjugation. -/
def conjugatePhaseLabel : PhaseLabel → PhaseLabel
  | one => one
  | zeta => zetaSq
  | zetaSq => zeta

@[simp] theorem phaseLabel_mirror (x : ChiralBias) :
    phaseLabel (mirror x) = conjugatePhaseLabel (phaseLabel x) := by
  cases x <;> rfl

@[simp] theorem phaseValue_conjugate (p : PhaseLabel) :
    phaseValue (conjugatePhaseLabel p) = Complex.conj (phaseValue p) := by
  cases p with
  | one => simp [phaseValue, conjugatePhaseLabel]
  | zeta => simpa [phaseValue, conjugatePhaseLabel] using Spine.conj_zeta.symm
  | zetaSq => simpa [phaseValue, conjugatePhaseLabel] using Spine.conj_zeta_sq.symm

/-- Reopen the exact finite state from phase plus the existing magnitude code. -/
def reopenPhaseMagnitude : PhaseLabel → Nat → ChiralBias
  | one, _ => racemic
  | zeta, 1 => leftSeed
  | zeta, _ => leftAmplified
  | zetaSq, 1 => rightSeed
  | zetaSq, _ => rightAmplified

@[simp] theorem reopen_phase_magnitude (x : ChiralBias) :
    reopenPhaseMagnitude (phaseLabel x) (magnitudeCode x) = x := by
  cases x <;> rfl

/-- The phase observer is genuinely lossy for full identity. -/
theorem no_identity_factor_through_phaseLabel :
    ¬ ∃ f : PhaseLabel → ChiralBias, ∀ x, x = f (phaseLabel x) := by
  rintro ⟨f, h⟩
  have hs := h leftSeed
  have ha := h leftAmplified
  have bad : leftSeed = leftAmplified := by
    calc
      leftSeed = f zeta := by simpa [phaseLabel] using hs
      _ = leftAmplified := by simpa [phaseLabel] using ha.symm
  cases bad

/-- Handed branch factors exactly through the three-phase observer. -/
def branchOfPhase : PhaseLabel → FutureBranch
  | one => FutureBranch.racemic
  | zeta => FutureBranch.left
  | zetaSq => FutureBranch.right

@[simp] theorem futureBranch_factors_through_phaseLabel (x : ChiralBias) :
    futureBranch x = branchOfPhase (phaseLabel x) := by
  cases x <;> rfl

theorem futureBranch_factorization :
    ∃ f : PhaseLabel → FutureBranch, ∀ x, futureBranch x = f (phaseLabel x) := by
  exact ⟨branchOfPhase, futureBranch_factors_through_phaseLabel⟩

------------------------------------------------------------------------
-- Fixed-plus-conjugate-pair realification.
------------------------------------------------------------------------

inductive RealifiedSector where
  | fixed
  | transverse
  deriving DecidableEq, Repr

open RealifiedSector

def realifiedPhase : PhaseLabel → RealifiedSector
  | one => fixed
  | zeta => transverse
  | zetaSq => transverse

def realifiedObserver (x : ChiralBias) : RealifiedSector :=
  realifiedPhase (phaseLabel x)

@[simp] theorem left_right_realified_collision :
    realifiedObserver leftSeed = realifiedObserver rightSeed := rfl

/-- Realification loses handedness, so it cannot pay the branch consumer. -/
theorem no_futureBranch_factor_through_realified :
    ¬ ∃ f : RealifiedSector → FutureBranch,
      ∀ x, futureBranch x = f (realifiedObserver x) := by
  rintro ⟨f, h⟩
  have hl := h leftSeed
  have hr := h rightSeed
  have bad : FutureBranch.left = FutureBranch.right := by
    calc
      FutureBranch.left = f transverse := by
        simpa [futureBranch, realifiedObserver, realifiedPhase, phaseLabel] using hl
      _ = FutureBranch.right := by
        simpa [futureBranch, realifiedObserver, realifiedPhase, phaseLabel] using hr.symm
  cases bad

inductive RacemicStatus where
  | racemic
  | nonRacemic
  deriving DecidableEq, Repr

open RacemicStatus

def racemicStatus : ChiralBias → RacemicStatus
  | ChiralBias.racemic => RacemicStatus.racemic
  | _ => nonRacemic

def statusOfRealified : RealifiedSector → RacemicStatus
  | fixed => RacemicStatus.racemic
  | transverse => nonRacemic

@[simp] theorem racemicStatus_factors_through_realified (x : ChiralBias) :
    racemicStatus x = statusOfRealified (realifiedObserver x) := by
  cases x <;> rfl

theorem racemicStatus_factorization :
    ∃ f : RealifiedSector → RacemicStatus,
      ∀ x, racemicStatus x = f (realifiedObserver x) := by
  exact ⟨statusOfRealified, racemicStatus_factors_through_realified⟩

structure RecoverableObserverBoundary where
  phaseAloneRecoversIdentity : Bool
  phasePlusMagnitudeReopensIdentity : Bool
  phasePaysHandedBranch : Bool
  realifiedPaysRacemicStatus : Bool
  realifiedPaysHandedBranch : Bool
  realifiedSectorIsPhysicalQuantumTPS : Bool
  deriving DecidableEq, Repr

def recoverableObserverBoundary : RecoverableObserverBoundary :=
  ⟨false, true, true, true, false, false⟩

end NobelChemistry
