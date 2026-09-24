module DASHI.Core.AristotlePropertyFamilyQueryFibreBidiExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- ARISTOTLE / WIKIDATA RETURN 1
--   (Q,P) STATEMENT FAMILY  ×  QUERY-COMPATIBLE FIBRE
--
-- Reverse extraction of the Lean owner
--   Integration.Kernel.Aristotle.PropertyFamilyQueryFibre
-- which is itself the instantiation of the generic compatible-fibre kernel
-- on the truthy semantics of the archive module RequestProject.Ranks.
--
-- STATUS.  This file is *Agda source*.  No Agda toolchain is available in
-- the environment where it was written, so nothing here carries an Agda
-- kernel receipt; the corresponding statements are checked on the Lean side
-- only.  The Lean proof is not an Agda proof: the obligations below are
-- discharged here by their own Agda terms, and until an exact-head Agda
-- build exists they are unvalidated source.
------------------------------------------------------------------------

-- The hidden state is a world; the observation is the statement family of
-- one subject-property pair; the consumer is the truthy answer.

record QueryFamilyFibre : Set₁ where
  constructor query-family-fibre
  field
    World Family Answer : Set
    -- what inspecting the (Q,P) family of a world returns
    familyOf : World → Family
    -- the truthy consumer
    consumer : World → Answer
    -- the load-bearing law: the consumer factors through the family
    consumerFactors : (w v : World) → familyOf w ≡ familyOf v → consumer w ≡ consumer v

open QueryFamilyFibre public

-- Membership in the compatible fibre of an observed family.

InFibre : (F : QueryFamilyFibre) → World F → World F → Set
InFibre F w v = familyOf F v ≡ familyOf F w

-- Point identification of the world by the family observation.

PointIdentification : (F : QueryFamilyFibre) → World F → Set
PointIdentification F w = (v : World F) → InFibre F w v → v ≡ w

-- Closure of the consumer on the fibre.

ConsumerClosure : (F : QueryFamilyFibre) → World F → Set
ConsumerClosure F w = (v : World F) → InFibre F w v → consumer F v ≡ consumer F w

-- POSITIVE DIRECTION: point identification implies consumer closure.

pointIdentificationGivesClosure :
  (F : QueryFamilyFibre) (w : World F) →
  PointIdentification F w → ConsumerClosure F w
pointIdentificationGivesClosure F w pid v inf =
  cong (consumer F) (pid v inf)

-- And, without any identification at all, the factorisation already closes
-- the consumer: this is the whole point of the reverse extraction.

factorisationGivesClosure :
  (F : QueryFamilyFibre) (w : World F) → ConsumerClosure F w
factorisationGivesClosure F w v inf = consumerFactors F v w inf

------------------------------------------------------------------------
-- EXACT COUNTERMODEL: NON-SINGLETON FIBRE, CLOSED CONSUMER
------------------------------------------------------------------------

-- Two worlds differing only outside the observed family.

data TwoWorlds : Set where
  worldA worldB : TwoWorlds

data OneFamily : Set where
  observedFamily : OneFamily

data TruthyAnswer : Set where
  population3645000 : TruthyAnswer

exactFibre : QueryFamilyFibre
exactFibre = query-family-fibre
  TwoWorlds OneFamily TruthyAnswer
  (λ _ → observedFamily)
  (λ _ → population3645000)
  (λ _ _ _ → refl)

worldsDiffer : ¬ (worldA ≡ worldB)
worldsDiffer ()

-- The fibre of the observed family is not a singleton ...

nonSingletonFibre : ¬ (PointIdentification exactFibre worldA)
nonSingletonFibre pid = worldsDiffer (sym (pid worldB refl))

-- ... while the consumer is closed on it.

consumerClosedOnNonSingletonFibre : ConsumerClosure exactFibre worldA
consumerClosedOnNonSingletonFibre = factorisationGivesClosure exactFibre worldA

-- Therefore, in the Agda idiom of the garden:
--   NonSingletonFibre  does not imply  EpistemicFailure.

nonSingletonFibreIsNotEpistemicFailure :
  (¬ (PointIdentification exactFibre worldA)) × ConsumerClosure exactFibre worldA
nonSingletonFibreIsNotEpistemicFailure =
  nonSingletonFibre , consumerClosedOnNonSingletonFibre

------------------------------------------------------------------------
-- THE OTHER BOUNDARY: AN UNCOVERED FAMILY DOES NOT CLOSE THE CONSUMER
------------------------------------------------------------------------

-- Here the observation is only *part* of the family (the normal-rank rows),
-- and an unobserved preferred sibling changes the answer.

record PartialFamilyObservation : Set₁ where
  constructor partial-family-observation
  field
    World Observed Answer : Set
    observe : World → Observed
    answer : World → Answer
    -- two worlds agreeing on everything observed ...
    left right : World
    sameObservation : observe left ≡ observe right
    -- ... whose answers differ
    differentAnswer : ¬ (answer left ≡ answer right)

open PartialFamilyObservation public

data TwoAnswers : Set where
  answerOld answerPreferred : TwoAnswers

answersDiffer : ¬ (answerOld ≡ answerPreferred)
answersDiffer ()

witnessAnswer : TwoWorlds → TwoAnswers
witnessAnswer worldA = answerOld
witnessAnswer worldB = answerPreferred

uncoveredFamily : PartialFamilyObservation
uncoveredFamily = partial-family-observation
  TwoWorlds OneFamily TwoAnswers
  (λ _ → observedFamily)
  witnessAnswer
  worldA worldB refl answersDiffer

-- Coverage of the family is what the consumer needs; identification of the
-- whole item is not.
