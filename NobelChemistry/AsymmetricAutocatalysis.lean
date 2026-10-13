import Mathlib
import Spine.TernaryPhase

/-!
# 2026 Nobel Chemistry: finite asymmetric-autocatalysis / C₃ bridge

This file formalises only the reusable finite symmetry shape behind the Kagan /
Soai asymmetric-amplification story.  It deliberately does not claim a
quantitative kinetic model, a quantum mechanism, or an origin-of-life theorem.

The cyclotomic phase map reuses `Spine.TernaryPhase` literally: racemic maps to
the conjugation-fixed phase `1`, while left/right branches map to the conjugate
pair `ζ, ζ²`.  Thus molecular mirror exchange intertwines with complex
conjugation on this finite observer.  That intertwiner is a representation
choice, not an identification of chirality with a quantum amplitude.
-/

open Complex ComplexConjugate

namespace NobelChemistry

inductive ChiralBias where
  | leftAmplified
  | leftSeed
  | racemic
  | rightSeed
  | rightAmplified
  deriving DecidableEq, Repr

open ChiralBias

/-- Mirror exchange on the finite chirality carrier. -/
def mirror : ChiralBias → ChiralBias
  | leftAmplified => rightAmplified
  | leftSeed => rightSeed
  | racemic => racemic
  | rightSeed => leftSeed
  | rightAmplified => leftAmplified

@[simp] theorem mirror_involutive (x : ChiralBias) : mirror (mirror x) = x := by
  cases x <;> rfl

/-- A finite amplification step: non-racemic seeds are sent to stable branches. -/
def amplify : ChiralBias → ChiralBias
  | leftAmplified => leftAmplified
  | leftSeed => leftAmplified
  | racemic => racemic
  | rightSeed => rightAmplified
  | rightAmplified => rightAmplified

@[simp] theorem amplify_mirror_equivariant (x : ChiralBias) :
    amplify (mirror x) = mirror (amplify x) := by
  cases x <;> rfl

@[simp] theorem racemic_fixed : amplify racemic = racemic := rfl
@[simp] theorem left_seed_amplifies : amplify leftSeed = leftAmplified := rfl
@[simp] theorem right_seed_amplifies : amplify rightSeed = rightAmplified := rfl
@[simp] theorem left_branch_fixed : amplify leftAmplified = leftAmplified := rfl
@[simp] theorem right_branch_fixed : amplify rightAmplified = rightAmplified := rfl

/-- Discrete magnitude witness only; not a calibrated enantiomeric excess. -/
def magnitudeCode : ChiralBias → Nat
  | leftAmplified => 2
  | leftSeed => 1
  | racemic => 0
  | rightSeed => 1
  | rightAmplified => 2

@[simp] theorem left_amplification_code : magnitudeCode (amplify leftSeed) = 2 := rfl
@[simp] theorem right_amplification_code : magnitudeCode (amplify rightSeed) = 2 := rfl

/--
Finite cyclotomic observer.  This is deliberately observer-level: it does not
claim that molecular chirality *is* a complex phase.
-/
noncomputable def phase : ChiralBias → ℂ
  | leftAmplified => Spine.zeta
  | leftSeed => Spine.zeta
  | racemic => 1
  | rightSeed => Spine.zeta ^ 2
  | rightAmplified => Spine.zeta ^ 2

/-- Molecular mirror exchange is represented by literal complex conjugation. -/
theorem phase_mirror_eq_conj (x : ChiralBias) :
    phase (mirror x) = Complex.conj (phase x) := by
  cases x with
  | leftAmplified => simpa [phase, mirror] using Spine.conj_zeta.symm
  | leftSeed => simpa [phase, mirror] using Spine.conj_zeta.symm
  | racemic => simp [phase, mirror]
  | rightSeed => simpa [phase, mirror] using Spine.conj_zeta_sq.symm
  | rightAmplified => simpa [phase, mirror] using Spine.conj_zeta_sq.symm

@[simp] theorem racemic_phase_fixed : phase racemic = 1 := rfl

/-- Amplification remains compatible with conjugation after phase projection. -/
theorem phase_amplify_mirror_eq_conj (x : ChiralBias) :
    phase (amplify (mirror x)) = Complex.conj (phase (amplify x)) := by
  simpa [amplify_mirror_equivariant] using phase_mirror_eq_conj (amplify x)

inductive FutureBranch where
  | left
  | racemic
  | right
  deriving DecidableEq, Repr

open FutureBranch

/-- A deliberately chirality-forgetting coarse observation. -/
def coarse (_ : ChiralBias) : Unit := ()

/-- A branch-sensitive future consumer. -/
def futureBranch : ChiralBias → FutureBranch
  | leftAmplified => left
  | leftSeed => left
  | racemic => racemic
  | rightSeed => right
  | rightAmplified => right

/-- Future readout after one nonlinear amplification step. -/
def futureAfterStep (x : ChiralBias) : FutureBranch := futureBranch (amplify x)

@[simp] theorem same_coarse_seeds : coarse leftSeed = coarse rightSeed := rfl

/--
The chirality-forgetting observation is not sufficient for this future consumer:
left/right seeds collide coarsely but diverge after the same equivariant step.
-/
theorem no_future_factor_through_coarse :
    ¬ ∃ f : Unit → FutureBranch, ∀ x, futureAfterStep x = f (coarse x) := by
  rintro ⟨f, h⟩
  have hl := h leftSeed
  have hr := h rightSeed
  have hbad : FutureBranch.left = FutureBranch.right := by
    calc
      FutureBranch.left = f () := by simpa [futureAfterStep, futureBranch, amplify, coarse] using hl
      _ = FutureBranch.right := by simpa [futureAfterStep, futureBranch, amplify, coarse] using hr.symm
  cases hbad

/-- The law is mirror symmetric while non-racemic realised branches exist. -/
theorem symmetric_law_does_not_force_racemic_state :
    amplify_mirror_equivariant leftSeed ∧ amplify leftSeed ≠ racemic := by
  constructor
  · exact amplify_mirror_equivariant leftSeed
  · decide

end NobelChemistry
