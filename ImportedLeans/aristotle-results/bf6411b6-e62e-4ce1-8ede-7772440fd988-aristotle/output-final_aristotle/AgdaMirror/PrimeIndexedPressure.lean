import Mathlib
import AgdaMirror.MonsterOntos
import AgdaMirror.GodelLattice
import AgdaMirror.NormalizeAdd
import AgdaMirror.CancellationPressureFromCanonical
import AgdaMirror.CancellationPressureRefinement

/-!
# Lean mirror of `DASHI/Arithmetic/PrimeIndexedPressure.agda` (genuine carrier laws)

The prime-indexed pressure carrier: the per-state prime-profile vector
`primeIndexedPressureAt`, its scalar projection `sum15`, and the lane projection
`primeContribution` with its genuine projection law (`sum15` equals the sum of
the 15 lane contributions).

Honesty discipline: the Agda module's `primeIndexedPressure-factor` (the
identification `sum15 (profile s) ≡ RefinedCancellationPressure s`) is a
*postulate*.  It is **never** assumed here as an axiom — instead the canonical ⇒
bounded transfer results take it as an *explicit hypothesis* (`factor`).
-/

namespace AgdaMirror.PrimeIndexedPressure

open AgdaMirror.MonsterOntos
open AgdaMirror.GodelLattice
open AgdaMirror.NormalizeAdd
open AgdaMirror.CancellationPressureFromCanonical
open AgdaMirror.CancellationPressureRefinement
open SSP

/-- A prime-contribution vector. -/
abbrev PrimeContributionVec : Type := Vec15 Nat

/-- Scalar projection of a prime-contribution vector. -/
def sum15 (v : PrimeContributionVec) : Nat := AgdaMirror.GodelLattice.sum v

/-- The all-zero contribution vector. -/
def canonicalZeroVec : PrimeContributionVec := replicate 0

/-- The per-state prime-profile carrier. -/
def primeIndexedPressureAt (s : NormalizeAddState) : PrimeContributionVec := s.primeProfile

/-- Lane projection of the prime-profile carrier. -/
def primeContribution (p : SSP) (s : NormalizeAddState) : Nat :=
  let v := primeIndexedPressureAt s
  match p with
  | p2 => v.e2 | p3 => v.e3 | p5 => v.e5 | p7 => v.e7 | p11 => v.e11
  | p13 => v.e13 | p17 => v.e17 | p19 => v.e19 | p23 => v.e23 | p29 => v.e29
  | p31 => v.e31 | p41 => v.e41 | p47 => v.e47 | p59 => v.e59 | p71 => v.e71

/-- Genuine projection law: the scalar projection is the sum of the 15 lane
contributions. -/
theorem sum15_eq_primeContributions (s : NormalizeAddState) :
    sum15 (primeIndexedPressureAt s) =
      primeContribution p2 s + primeContribution p3 s + primeContribution p5 s +
      primeContribution p7 s + primeContribution p11 s + primeContribution p13 s +
      primeContribution p17 s + primeContribution p19 s + primeContribution p23 s +
      primeContribution p29 s + primeContribution p31 s + primeContribution p41 s +
      primeContribution p47 s + primeContribution p59 s + primeContribution p71 s := rfl

/-- The `factor` identification of the Agda module, packaged as a hypothesis type
(it is a `postulate` in the source, so it is never assumed as an axiom). -/
abbrev FactorHypothesis : Prop :=
  ∀ s : NormalizeAddState, sum15 (primeIndexedPressureAt s) = RefinedCancellationPressure s

/-- Canonical ⇒ prime-indexed bounded, *given* the factor identification. -/
theorem canonical_primeIndexedBounded (factor : FactorHypothesis)
    (s : NormalizeAddState) (canon : normalizeAddCanonical s) :
    sum15 (primeIndexedPressureAt s) ≤ StateSupportPressure s := by
  rw [factor s]
  exact canonical_refinedBounded s canon

/-- One-step prime-indexed bound, *given* the factor identification. -/
theorem normalizeAdd_primeIndexedBounded (factor : FactorHypothesis) (s : NormalizeAddState) :
    sum15 (primeIndexedPressureAt (normalizeAdd s)) ≤ StateSupportPressure (normalizeAdd s) :=
  canonical_primeIndexedBounded factor (normalizeAdd s) (normalizeAdd_canonical s)

/-- One-step canonical-and-bounded pair, *given* the factor identification. -/
theorem normalizeAdd_primeIndexedCanonicalBounded (factor : FactorHypothesis)
    (s : NormalizeAddState) :
    normalizeAddCanonical (normalizeAdd s) ∧
      sum15 (primeIndexedPressureAt (normalizeAdd s)) ≤ StateSupportPressure (normalizeAdd s) :=
  ⟨normalizeAdd_canonical s, normalizeAdd_primeIndexedBounded factor s⟩

end AgdaMirror.PrimeIndexedPressure
