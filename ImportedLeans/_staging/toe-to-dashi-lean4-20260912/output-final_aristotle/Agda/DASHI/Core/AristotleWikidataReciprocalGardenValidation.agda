module DASHI.Core.AristotleWikidataReciprocalGardenValidation where

open import DASHI.Core.Prelude

import DASHI.Core.AristotlePropertyFamilyQueryFibreBidiExact as Fibre
import DASHI.Core.AristotleSnakAbsenceInformationLossBidiExact as Absence
import DASHI.Core.AristotleReliableSourceConsumerAdequacyBidiExact as Provenance
import DASHI.Core.AristotlePrunedGraphPromotionTransportBidiExact as Pruned
import DASHI.Core.AristotleWikibaseZelphBraidedPromotionBidiExact as Braid

------------------------------------------------------------------------
-- VALIDATION OWNER FOR THE ARISTOTLE / WIKIDATA RECIPROCAL GARDEN
--
-- One regression per owner, restating the headline boundary so that a
-- rename or a weakening of any owner breaks this module.
--
-- STATUS.  Agda source.  No Agda toolchain was available where this file
-- was written, so it carries no kernel receipt; the corresponding
-- statements are checked on the Lean side, in
-- Integration.Kernel.Aristotle.* and Integration.AxiomAuditAristotle.
------------------------------------------------------------------------

-- 1.  A non-singleton compatible fibre can nevertheless close the consumer.

nonSingletonFibreClosesConsumerRegression :
  (¬ (Fibre.PointIdentification Fibre.exactFibre Fibre.worldA))
  × Fibre.ConsumerClosure Fibre.exactFibre Fibre.worldA
nonSingletonFibreClosesConsumerRegression =
  Fibre.nonSingletonFibreIsNotEpistemicFailure

-- 2.  An empty result is not a native `novalue`, and the collapse is not
--     reversible downstream.

emptyResultIsNotNoValueRegression : Absence.EmptyResultIsNotNoValue
emptyResultIsNotNoValueRegression = Absence.exactEmptyResultWitness

lossLocusIsPairRelativeRegression :
  (Absence.stageOne Absence.noStatementObserved
     ≡ Absence.stageOne Absence.nativeNoValue)
  × (¬ (Absence.stageOne Absence.uninspected
          ≡ Absence.stageOne Absence.nativeNoValue))
lossLocusIsPairRelativeRegression = Absence.lossLocusIsPairRelative

-- 3.  Visible support is not independent reliable support.

visibleSupportIsNotIndependentSupportRegression :
  (Provenance.isSource (Provenance.kindOf Provenance.rowStated₁) ≡ true)
  × (Provenance.isSource (Provenance.kindOf Provenance.rowStated₂) ≡ true)
  × (¬ (Provenance.Independent Provenance.rowStated₁ Provenance.rowStated₂))
visibleSupportIsNotIndependentSupportRegression =
  Provenance.twoVisibleReportsAreNotTwoIndependentRoots

patternInFullAbsentInReliableRegression :
  (Provenance.admits Provenance.full Provenance.rowImported ≡ true)
  × (¬ (Provenance.admits Provenance.reliable Provenance.rowImported ≡ true))
patternInFullAbsentInReliableRegression =
  Provenance.patternInFullAbsentInReliable

-- 4.  A soundness receipt is not a completeness receipt.

soundnessIsNotCompletenessRegression :
  Pruned.Soundness × (¬ Pruned.Completeness)
soundnessIsNotCompletenessRegression = Pruned.soundnessIsNotCompleteness

negativeAnswerDoesNotPromoteRegression : ¬ Pruned.AbsenceReceipt
negativeAnswerDoesNotPromoteRegression = Pruned.negativeAnswerDoesNotPromote

-- 5.  Strand-indexed promotion compiles, and the receipt does not
--     reconstruct the strands.

braidedPromotionRegression : Braid.Receipt
braidedPromotionRegression = Braid.strandAssignmentCompiles

receiptDoesNotDetermineProvenanceRegression :
  ¬ (Σ (Braid.Receipt → Braid.Assignment)
       (λ f → (A : Braid.Assignment) (d : Braid.Discharges A)
                → f (Braid.compile A d) ≡ A))
receiptDoesNotDetermineProvenanceRegression =
  Braid.fullReceiptDoesNotDetermineProvenance
