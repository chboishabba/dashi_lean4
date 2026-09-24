module DASHI.Core.AristotleSnakAbsenceInformationLossBidiExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- ARISTOTLE / WIKIDATA RETURN 2
--   SNAK ABSENCE SEMANTICS  ×  INFORMATION-LOSS LOCUS
--
-- Reverse extraction of the Lean owner
--   Integration.Kernel.Aristotle.SnakAbsenceInformationLoss,
-- which instantiates the information-loss-locus bridge on the entailment
-- semantics of the archive module RequestProject.Snaks.
--
-- STATUS.  Agda source, written without an available Agda toolchain: no
-- kernel receipt is claimed for this file.  The Lean side carries the
-- checked proofs of the corresponding statements.
------------------------------------------------------------------------

-- The three states a pipeline over the snak layer can be in for a
-- subject-property pair.  They are *definitionally distinct constructors*:
-- this is the whole content of the firewall.

data Absence : Set where
  uninspected         : Absence
  noStatementObserved : Absence
  nativeNoValue       : Absence

-- Distinctness, exactly.

uninspectedIsNotObserved : ¬ (uninspected ≡ noStatementObserved)
uninspectedIsNotObserved ()

observedIsNotNoValue : ¬ (noStatementObserved ≡ nativeNoValue)
observedIsNotNoValue ()

uninspectedIsNotNoValue : ¬ (uninspected ≡ nativeNoValue)
uninspectedIsNotNoValue ()

------------------------------------------------------------------------
-- THE COLLAPSING PROJECTION
------------------------------------------------------------------------

-- What a consumer sees if it reads only returned values: "empty" or "not".

data VisibleResult : Set where
  emptyResult    : VisibleResult
  nonEmptyResult : VisibleResult

visible : Absence → VisibleResult
visible uninspected         = emptyResult
visible noStatementObserved = emptyResult
visible nativeNoValue       = emptyResult

-- The projection collapses two distinct states.

collapsesObservedAndNoValue :
  visible noStatementObserved ≡ visible nativeNoValue
collapsesObservedAndNoValue = refl

-- ... and no downstream stage restores the distinction: every function of
-- the projection returns the same answer on the two states.

downstreamCannotRestore :
  {B : Set} (f : VisibleResult → B) →
  f (visible noStatementObserved) ≡ f (visible nativeNoValue)
downstreamCannotRestore f = cong f collapsesObservedAndNoValue

-- The firewall in the garden idiom:
--   empty result  does not imply  Wikidata novalue.

record EmptyResultIsNotNoValue : Set₁ where
  constructor empty-result-is-not-novalue
  field
    -- a base whose values for the pair are empty ...
    state : Absence
    resultIsEmpty : visible state ≡ emptyResult
    -- ... which is not the native novalue state
    notNoValue : ¬ (state ≡ nativeNoValue)

open EmptyResultIsNotNoValue public

exactEmptyResultWitness : EmptyResultIsNotNoValue
exactEmptyResultWitness =
  empty-result-is-not-novalue noStatementObserved refl observedIsNotNoValue

------------------------------------------------------------------------
-- THE LOSS LOCUS IS PAIR-RELATIVE
------------------------------------------------------------------------

-- A two-stage flattening: stage one reports "nothing came back" for a
-- native novalue, stage two forgets whether the pair was inspected at all.

stageOne : Absence → Absence
stageOne uninspected         = uninspected
stageOne noStatementObserved = noStatementObserved
stageOne nativeNoValue       = noStatementObserved

stageTwo : Absence → Absence
stageTwo uninspected         = noStatementObserved
stageTwo noStatementObserved = noStatementObserved
stageTwo nativeNoValue       = nativeNoValue

-- The (observed, novalue) pair is destroyed by stage one.

noValuePairLostAtStageOne :
  stageOne noStatementObserved ≡ stageOne nativeNoValue
noValuePairLostAtStageOne = refl

-- The (uninspected, novalue) pair survives it.

uninspectedPairSurvivesStageOne :
  ¬ (stageOne uninspected ≡ stageOne nativeNoValue)
uninspectedPairSurvivesStageOne ()

-- And is destroyed by the composite.

uninspectedPairLostAfterStageTwo :
  stageTwo (stageOne uninspected) ≡ stageTwo (stageOne nativeNoValue)
uninspectedPairLostAfterStageTwo = refl

-- So the locus of loss belongs to the pair, not to the stack.

lossLocusIsPairRelative :
  (stageOne noStatementObserved ≡ stageOne nativeNoValue)
  × (¬ (stageOne uninspected ≡ stageOne nativeNoValue))
lossLocusIsPairRelative =
  noValuePairLostAtStageOne , uninspectedPairSurvivesStageOne

-- Once collapsed, always collapsed: any further stage agrees on the pair.

collapsePersists :
  {B : Set} (g : Absence → B) →
  g (stageOne noStatementObserved) ≡ g (stageOne nativeNoValue)
collapsePersists g = cong g noValuePairLostAtStageOne
