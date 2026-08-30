module DASHI.Foundations.BishopToDASHIRealTransportExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Foundations.RealAnalysisAxioms as DASHIReal
open import DASHI.Foundations.BishopConstructiveRealBridgeExact
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Transport into DASHI's pre-existing postulated real socket.
--
-- The submodule removes the need to postulate a second completeness theorem.
-- A remaining choice is architectural: either migrate analytic consumers to
-- Bishopℝ directly, or provide this explicit structure-preserving transport.
-- The transport is intentionally a record, not a hidden equality of carriers.
------------------------------------------------------------------------

record BishopToDASHIRealBridge : Set₁ where
  field
    embed : Bishopℝ → DASHIReal.ℝ

    embedZero : embed bishopZero ≡ DASHIReal.0ℝ
    embedOne : embed bishopOne ≡ DASHIReal.1ℝ

    embedAdd : ∀ left right →
      embed (bishopAdd left right)
      ≡ DASHIReal._+ℝ_ (embed left) (embed right)

    embedSub : ∀ left right →
      embed (bishopSub left right)
      ≡ DASHIReal._-ℝ_ (embed left) (embed right)

    embedMul : ∀ left right →
      embed (bishopMul left right)
      ≡ DASHIReal._*ℝ_ (embed left) (embed right)

    embedNeg : ∀ value →
      embed (bishopNeg value) ≡ DASHIReal.-ℝ_ (embed value)

    embedAbs : ∀ value →
      embed (bishopAbs value) ≡ DASHIReal.absℝ (embed value)

    embedEquivalent : ∀ {left right} →
      BishopEquivalent left right → embed left ≡ embed right

    embedLessEqual : ∀ {left right} →
      BishopLessEqual left right →
      DASHIReal._≤ℝ_ (embed left) (embed right)

    embedStrictLess : ∀ {left right} →
      BishopStrictLess left right →
      DASHIReal._<ℝ_ (embed left) (embed right)

    DASHIConvergesTo :
      (Nat → DASHIReal.ℝ) → DASHIReal.ℝ → Set

    convergencePreserved :
      ∀ {sequence limit} →
      BishopConvergesTo sequence limit →
      DASHIConvergesTo
        (λ index → embed (sequence index))
        (embed limit)

open BishopToDASHIRealBridge public

bishopToDASHITransportInputsLevel : ProofLevel
bishopToDASHITransportInputsLevel = conditional
