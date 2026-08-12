import AgdaMirror.Base369
import AgdaMirror.LogicTlurey

/-!
# Lean mirror of `DASHI/Algebra/StageQuotient.agda` (genuine, fully proved)

Faithful transcription of `DASHI.Algebra.StageQuotient`, which studies the tone
quotient `q = stageTone : Stage → TriTruth` (reusing the already-mirrored
`AgdaMirror.LogicTlurey.stageTone` and `AgdaMirror.Base369.TriTruth`).

It proves that `q` hits all three tones (`seed ↦ low`, `counter ↦ mid`,
`resonance ↦ high`), that `overflow` collapses onto `seed`, and that the
quotient is `rotateTri`-*equivariant* on the first three stages — but **not** on
`overflow`: `q (next overflow) = low` while `rotateTri (q overflow) = mid`, so
equivariance genuinely *fails* there.  This "seam" failure is a real disproof
(`overflow_equivariance_fails`), faithfully preserved.
-/

namespace AgdaMirror.StageQuotient

open AgdaMirror.Base369 (TriTruth rotateTri)
open AgdaMirror.LogicTlurey (Stage next stageTone)

/-- The tone quotient. -/
def q : Stage → TriTruth := stageTone

theorem q_surj_low : q .seed = .low := rfl
theorem q_surj_mid : q .counter = .mid := rfl
theorem q_surj_high : q .resonance = .high := rfl

/-- `overflow` collapses onto `seed`. -/
theorem q_overflow_collapse : q .overflow = q .seed := rfl

theorem q_next_seed : q (next .seed) = rotateTri (q .seed) := rfl
theorem q_next_counter : q (next .counter) = rotateTri (q .counter) := rfl
theorem q_next_resonance : q (next .resonance) = rotateTri (q .resonance) := rfl

theorem q_next_overflow : q (next .overflow) = TriTruth.low := rfl
theorem rotate_q_overflow : rotateTri (q .overflow) = TriTruth.mid := rfl

/-- The equivariance **seam**: the quotient is not `rotateTri`-equivariant on
`overflow`. -/
theorem overflow_equivariance_fails :
    q (next .overflow) ≠ rotateTri (q .overflow) := by decide

/-- The full stage-quotient seam surface (mirrors `StageQuotientSeam`). -/
structure StageQuotientSeam where
  quotient : Stage → TriTruth
  representative_low : quotient .seed = .low
  representative_mid : quotient .counter = .mid
  representative_high : quotient .resonance = .high
  overflow_collapse : quotient .overflow = quotient .seed
  seed_equivariant : quotient (next .seed) = rotateTri (quotient .seed)
  counter_equivariant : quotient (next .counter) = rotateTri (quotient .counter)
  resonance_equivariant : quotient (next .resonance) = rotateTri (quotient .resonance)
  overflow_seam : quotient (next .overflow) ≠ rotateTri (quotient .overflow)

/-- The canonical seam surface. -/
def stageQuotientSeamSurface : StageQuotientSeam where
  quotient := q
  representative_low := q_surj_low
  representative_mid := q_surj_mid
  representative_high := q_surj_high
  overflow_collapse := q_overflow_collapse
  seed_equivariant := q_next_seed
  counter_equivariant := q_next_counter
  resonance_equivariant := q_next_resonance
  overflow_seam := overflow_equivariance_fails

end AgdaMirror.StageQuotient
