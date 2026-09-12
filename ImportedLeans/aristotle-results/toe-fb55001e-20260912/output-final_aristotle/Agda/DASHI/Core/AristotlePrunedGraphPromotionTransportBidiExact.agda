module DASHI.Core.AristotlePrunedGraphPromotionTransportBidiExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- ARISTOTLE / WIKIDATA RETURN 4
--   PRUNED TYPE MODULE  ×  PROMOTION TRANSPORT CHAIN
--
-- Reverse extraction of the Lean owner
--   Integration.Kernel.Aristotle.PrunedGraphPromotionTransport,
-- which instantiates the four-obligation promotion chain on a pruned
-- knowledge base of the archive's derivation engine.
--
-- STATUS.  Agda source; no Agda kernel receipt is claimed here.
------------------------------------------------------------------------

-- The two type modules: a full one and a routed/pruned one.

data Typing : Set where
  adamsHuman : Typing
  adamsAgent : Typing

fullAnswers : Typing → Bool
fullAnswers adamsHuman = true
fullAnswers adamsAgent = true

prunedAnswers : Typing → Bool
prunedAnswers adamsHuman = true
prunedAnswers adamsAgent = false

-- SOUNDNESS: every positive answer of the pruned module is a positive
-- answer of the full one.  Quantified over all typings.

Soundness : Set
Soundness = (t : Typing) → prunedAnswers t ≡ true → fullAnswers t ≡ true

prunedIsSound : Soundness
prunedIsSound adamsHuman _ = refl
prunedIsSound adamsAgent ()

-- COMPLETENESS: every positive answer of the full module is returned.

Completeness : Set
Completeness = (t : Typing) → fullAnswers t ≡ true → prunedAnswers t ≡ true

prunedIsNotComplete : ¬ Completeness
prunedIsNotComplete c with c adamsAgent refl
... | ()

-- SoundnessReceipt does not give CompletenessReceipt.

soundnessIsNotCompleteness : Soundness × (¬ Completeness)
soundnessIsNotCompleteness = prunedIsSound , prunedIsNotComplete

-- A negative answer of the pruned module is not a negative fact.

absenceIsNotAbsence :
  (prunedAnswers adamsAgent ≡ false) × (fullAnswers adamsAgent ≡ true)
absenceIsNotAbsence = refl , refl

------------------------------------------------------------------------
-- THE PROMOTION CHAIN
------------------------------------------------------------------------

-- The four obligations, as separate types.

record PromotionReceipt : Set₁ where
  constructor promotion-receipt
  field
    Artifact Statement Target Term : Set
    claims : Artifact → Statement
    transport : Statement → Target
    Holds : Target → Set
    Inhabits : Term → Target → Set
    -- 1: an artefact
    artifact : Artifact
    -- 2: it corresponds to the statement in question
    statement : Statement
    corresponds : claims artifact ≡ statement
    -- 3: the transport is sound on it
    sound : Holds (transport statement)
    -- 4: a term inhabits the target
    term : Term
    inhabits : Inhabits term (transport statement)

open PromotionReceipt public

-- A positive answer of the pruned module pays all four.

positiveAnswerPromotes : PromotionReceipt
positiveAnswerPromotes = promotion-receipt
  Typing Typing Typing ⊤
  (λ t → t)
  (λ t → t)
  (λ t → fullAnswers t ≡ true)
  (λ _ t → fullAnswers t ≡ true)
  adamsHuman adamsHuman refl refl tt refl

-- The negative reading pays the first three and not the fourth: the
-- absence frame has no term at all.

record AbsenceReceipt : Set where
  constructor absence-receipt
  field
    term : ⊥

open AbsenceReceipt public

negativeAnswerDoesNotPromote : ¬ AbsenceReceipt
negativeAnswerDoesNotPromote r = ⊥-elim (term r)

-- The pair, in the garden idiom:
--   sound positive answers promote; absence does not.

soundPositiveButNoNegativeCompleteness :
  Soundness × (¬ Completeness) × (¬ AbsenceReceipt)
soundPositiveButNoNegativeCompleteness =
  prunedIsSound , prunedIsNotComplete , negativeAnswerDoesNotPromote
