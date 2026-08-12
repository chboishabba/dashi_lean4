import AgdaMirror.Base369
import AgdaMirror.LogicTlurey

/-!
# Lean mirror of `DASHI/Algebra/TetralemmaBridge.agda` (genuine, fully proved)

Faithful transcription of the four-position alignment surface between the
`LogicTlurey` dialectical `Stage`s, the ternary `TriTruth` tone, and the
SensibLaw `ResidualLevel` chain.  As the Agda module is explicit about, this is a
*formal alignment carrier only* (no semantic/historical equivalence is asserted).

Proved content:

* the `stageTone` of every stage factors through the tetralemma position
  (`stageTone_via_tetralemma`);
* the tone→residual map `triResidual` never produces the cross-claim
  `contradiction` level (`triResidual_excludes_contradiction`), and hence neither
  does `stageResidualTone` (`stageResidualTone_excludes_contradiction`);
* the residual↔position table entries (`exact`↦`affirmation`, etc.).

All proofs are by case analysis; no `sorry`, axiom-clean.
-/

namespace AgdaMirror.TetralemmaBridge

open AgdaMirror.Base369 (TriTruth)
open AgdaMirror.LogicTlurey (Stage stageTone)

/-- SensibLaw residual-meet level (mirrors `ResidualLevel`). -/
inductive ResidualLevel
  | exact | partialMeet | noTypedMeet | contradiction
  deriving DecidableEq, Repr

/-- The four classical tetralemma positions. -/
inductive TetralemmaPosition
  | affirmation | negation | both | neither
  deriving DecidableEq, Repr

/-- Stage → tetralemma position. -/
def stageTetralemma : Stage → TetralemmaPosition
  | .seed => .affirmation
  | .counter => .negation
  | .resonance => .both
  | .overflow => .neither

/-- Tetralemma position → ternary tone. -/
def tetralemmaTone : TetralemmaPosition → TriTruth
  | .affirmation => .low
  | .negation => .mid
  | .both => .high
  | .neither => .low

/-- The stage tone factors through the tetralemma position. -/
theorem stageTone_via_tetralemma (s : Stage) :
    stageTone s = tetralemmaTone (stageTetralemma s) := by cases s <;> rfl

/-- Residual level → tetralemma position. -/
def residualTetralemma : ResidualLevel → TetralemmaPosition
  | .exact => .affirmation
  | .partialMeet => .both
  | .noTypedMeet => .neither
  | .contradiction => .negation

/-- Tone → residual level. -/
def triResidual : TriTruth → ResidualLevel
  | .low => .exact
  | .mid => .partialMeet
  | .high => .noTypedMeet

/-- Stage → residual level via the tone. -/
def stageResidualTone (s : Stage) : ResidualLevel := triResidual (stageTone s)

theorem triResidual_low : triResidual .low = ResidualLevel.exact := rfl
theorem triResidual_mid : triResidual .mid = ResidualLevel.partialMeet := rfl
theorem triResidual_high : triResidual .high = ResidualLevel.noTypedMeet := rfl

/-- The tone→residual map never yields the cross-claim `contradiction` level. -/
theorem triResidual_excludes_contradiction (t : TriTruth) :
    triResidual t ≠ ResidualLevel.contradiction := by cases t <;> decide

/-- Hence neither does the stage→residual tone. -/
theorem stageResidualTone_excludes_contradiction (s : Stage) :
    stageResidualTone s ≠ ResidualLevel.contradiction := by
  cases s <;> decide

theorem exact_is_affirmation :
    residualTetralemma .exact = TetralemmaPosition.affirmation := rfl
theorem partial_is_both :
    residualTetralemma .partialMeet = TetralemmaPosition.both := rfl
theorem noTypedMeet_is_neither :
    residualTetralemma .noTypedMeet = TetralemmaPosition.neither := rfl
theorem contradiction_is_negation :
    residualTetralemma .contradiction = TetralemmaPosition.negation := rfl

/-- The tetralemma bridge surface (mirrors `TetralemmaBridgeSurface`). -/
structure TetralemmaBridgeSurface where
  stageProjection : Stage → TetralemmaPosition
  residualProjection : ResidualLevel → TetralemmaPosition
  toneResidualProjection : TriTruth → ResidualLevel
  stageToneFactors : ∀ s, stageTone s = tetralemmaTone (stageProjection s)
  toneResidualExcludesContradiction :
    ∀ t, toneResidualProjection t ≠ ResidualLevel.contradiction
  nonClaimBoundary : List String

/-- The canonical bridge surface. -/
def tetralemmaBridgeSurface : TetralemmaBridgeSurface where
  stageProjection := stageTetralemma
  residualProjection := residualTetralemma
  toneResidualProjection := triResidual
  stageToneFactors := stageTone_via_tetralemma
  toneResidualExcludesContradiction := triResidual_excludes_contradiction
  nonClaimBoundary :=
    ["LogicTlurey stage cycle and SensibLaw residual chain share a four-position carrier only",
     "The Stage topology is cyclic; the ResidualLevel topology is an ordered join-semilattice",
     "TriTruth tone embeds only into exact/partial/noTypedMeet; contradiction is cross-claim pressure",
     "The bridge does not identify runtime PNF evidence with dialectical truth"]

end AgdaMirror.TetralemmaBridge
