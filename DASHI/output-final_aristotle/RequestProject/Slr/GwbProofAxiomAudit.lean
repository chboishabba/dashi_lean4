import RequestProject.Slr.GwbConsumerFibreProof

/-!
GWB source relative query theorem audit.
Lean's kernel reports the exact axioms used by these concrete proofs.
propext / Quot.sound / classical.choice can occur in ordinary Lean logic;
"sorryAx" or unchecked user axioms are forbidden.
-/

#check Wikidata.Slr.GwbConsumer.fibreJoinIdempotent
#check Wikidata.Slr.GwbConsumer.fibreJoinCommutative
#check Wikidata.Slr.GwbConsumer.fibreJoinAssociative
#check Wikidata.Slr.GwbConsumer.fibreJoinRetainsBothAnnotations
#check Wikidata.Slr.GwbConsumer.sourceMentionQueryCloses
#check Wikidata.Slr.GwbConsumer.literalYearQueryCloses
#check Wikidata.Slr.GwbConsumer.actualPossessionNotLicensed
#check Wikidata.Slr.GwbConsumer.actorIdentityNotLicensed
#check Wikidata.Slr.GwbConsumer.eventDateNotLicensed
#check Wikidata.Slr.GwbConsumer.embeddedScopeNotLicensed
#check Wikidata.Slr.GwbConsumer.scopedTimelineClosure

#print axioms Wikidata.Slr.GwbConsumer.fibreJoinAssociative
#print axioms Wikidata.Slr.GwbConsumer.sourceMentionQueryCloses
#print axioms Wikidata.Slr.GwbConsumer.actualPossessionNotLicensed
#print axioms Wikidata.Slr.GwbConsumer.actorIdentityNotLicensed
#print axioms Wikidata.Slr.GwbConsumer.eventDateNotLicensed
#print axioms Wikidata.Slr.GwbConsumer.embeddedScopeNotLicensed
