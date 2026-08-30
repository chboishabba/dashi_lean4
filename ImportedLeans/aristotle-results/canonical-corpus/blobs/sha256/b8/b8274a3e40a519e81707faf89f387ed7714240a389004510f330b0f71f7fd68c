import Cuisine.SensoryCore
import Synthesis.ToneCore

/-!
# Cuisine ↔ Synthesis: the one carrier they share, and what it does not give

The Agda cuisine lane and the Lean `Synthesis` spine both contain three-element
carriers: `SafetyEvidence` (verified / unknown / rejected) on the cuisine side
and `TriTruth` (the ternary tone, identified with `ℤ/3` in
`Synthesis.ToneCore.toneZMod`) on the synthesis side.

This file records, in checked form, exactly how far that coincidence goes.

* Positively: the carriers are abstractly isomorphic (`safetyTritEquiv`), as any
  two three-element sets are.
* But the isomorphism is not canonical: at least two distinct ones exist, so
  "the safety carrier is the tone carrier" is a choice, not a fact
  (`no_canonical_identification`).
* And the isomorphism does not transport structure.  The distinguished datum of
  the tone carrier is its fixed-point-free order-3 rotation `rotateTri`.  The
  distinguished datum of the safety carrier is its fail-closed severity order
  `safetyVerified < safetyUnknown < safetyRejected`.  These are incompatible:
  *no* self-map of the safety carrier is simultaneously order-3 (with a moved
  point) and monotone for severity (`no_order_three_monotone_selfmap`), and the
  transported rotation is in particular not monotone
  (`safetyRotate_not_monotone`).

Conclusion, stated precisely and nothing more: the shared word "ternary" does
not give a structure-preserving link between the cuisine lane and the Monster /
tone spine.  Every other cross-domain identification in this repository must be
checked the same way.
-/

namespace Cuisine.ToneSeparation

open Cuisine.SensoryCore (SafetyEvidence)
open Cuisine.SensoryCore.SafetyEvidence
open AgdaMirror.Base369 (TriTruth rotateTri)

/-! ## Bare carriers -/

theorem card_safetyEvidence : Fintype.card SafetyEvidence = 3 := by decide

theorem card_triTruth : Fintype.card TriTruth = 3 := by decide

/-- A bijection between the safety carrier and the tone carrier, sending the
fail-closed order to the numeric order of `ℤ/3`. -/
def safetyTritEquiv : SafetyEvidence ≃ TriTruth where
  toFun
    | safetyVerified => .low
    | safetyUnknown => .mid
    | safetyRejected => .high
  invFun
    | .low => safetyVerified
    | .mid => safetyUnknown
    | .high => safetyRejected
  left_inv := by decide
  right_inv := by decide

/-- A second, different bijection. -/
def safetyTritEquiv' : SafetyEvidence ≃ TriTruth where
  toFun
    | safetyVerified => .high
    | safetyUnknown => .mid
    | safetyRejected => .low
  invFun
    | .low => safetyRejected
    | .mid => safetyUnknown
    | .high => safetyVerified
  left_inv := by decide
  right_inv := by decide

/-- **The identification is not canonical.**  Two three-element sets admit six
bijections; exhibiting one proves nothing about the two theories. -/
theorem no_canonical_identification :
    (safetyTritEquiv : SafetyEvidence → TriTruth) ≠ safetyTritEquiv' := by
  intro h
  exact absurd (congrFun h safetyVerified) (by decide)

/-! ## The structures the two carriers actually carry -/

/-- Severity of a safety verdict: the fail-closed order used throughout the
cuisine lane (`unknown` is worse than `verified`, `rejected` is worst). -/
def safetyLevel : SafetyEvidence → ℕ
  | safetyVerified => 0
  | safetyUnknown => 1
  | safetyRejected => 2

theorem safetyLevel_injective {a b : SafetyEvidence} (h : safetyLevel a = safetyLevel b) :
    a = b := by cases a <;> cases b <;> simp_all [safetyLevel]

/-- Monotone for the severity order. -/
abbrev SeverityMonotone (f : SafetyEvidence → SafetyEvidence) : Prop :=
  ∀ a b, safetyLevel a ≤ safetyLevel b → safetyLevel (f a) ≤ safetyLevel (f b)

/-- The tone rotation transported along `safetyTritEquiv`. -/
def safetyRotate : SafetyEvidence → SafetyEvidence
  | safetyVerified => safetyUnknown
  | safetyUnknown => safetyRejected
  | safetyRejected => safetyVerified

/-- `safetyRotate` really is the transport of the tone rotation. -/
theorem safetyRotate_eq_transport (s : SafetyEvidence) :
    safetyRotate s = safetyTritEquiv.symm (rotateTri (safetyTritEquiv s)) := by
  cases s <;> rfl

theorem safetyRotate_no_fixpoint (s : SafetyEvidence) : safetyRotate s ≠ s := by
  cases s <;> decide

theorem safetyRotate_cubed (s : SafetyEvidence) :
    safetyRotate (safetyRotate (safetyRotate s)) = s := by cases s <;> decide

/-- The transported rotation is not compatible with the fail-closed order: it
sends the worst verdict to the best one. -/
theorem safetyRotate_not_monotone : ¬ SeverityMonotone safetyRotate := by decide

/-- **The separation theorem.**  No self-map of the safety carrier is at once
order-3-with-a-moved-point (the defining property of the tone rotation) and
monotone for the fail-closed severity order.  Hence the tone structure of
`Synthesis.ToneCore` does not transport to the cuisine safety carrier along any
bijection whatsoever. -/
theorem no_order_three_monotone_selfmap :
    ¬ ∃ f : SafetyEvidence → SafetyEvidence,
        SeverityMonotone f ∧ (∀ a, f (f (f a)) = a) ∧ (∃ a, f a ≠ a) := by decide

/-- The positive half of the same computation: a severity-monotone bijection of
the safety carrier is the identity.  The safety carrier is rigid, whereas the
tone carrier has an order-3 automorphism; so the two carriers are not isomorphic
*as structured objects*. -/
theorem severityMonotone_injective_eq_id :
    ∀ f : SafetyEvidence → SafetyEvidence,
      SeverityMonotone f → (∀ a b, f a = f b → a = b) → ∀ a, f a = a := by decide

end Cuisine.ToneSeparation
