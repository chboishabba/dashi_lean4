import RequestProject.Slr.RelationalObservedMeet

def main (args : List String) : IO UInt32 := do
  match args with
  | ["historical-focus", receipt] => Wikidata.Slr.RelationalObservedMeet.runHistoricalFocus receipt
  | ["demand", receipt] => Wikidata.Slr.RelationalObservedMeet.runDemandInventory receipt
  | ["factors", packet, answer] => Wikidata.Slr.RelationalObservedMeet.runFactorProjection packet answer
  | ["reciprocal", family, answer] => Wikidata.Slr.RelationalObservedMeet.runReciprocalQuery family answer
  | ["participant", family, answer] => Wikidata.Slr.RelationalObservedMeet.runParticipantQuery family answer
  | ["relations", packet, answer] => Wikidata.Slr.RelationalObservedMeet.runRecordedRelationQuery packet answer
  | [input, output] => Wikidata.Slr.RelationalObservedMeet.run input output
  | _ =>
    IO.eprintln "usage: RelationalObservedMeetRunner INPUT_NATIVE_FAMILY_JSON OUTPUT"
    return 2

#print axioms Wikidata.Slr.RelationalObservedMeet.checkedMembershipSound
#print axioms Wikidata.Slr.RelationalObservedMeet.commonObservedSound
#print axioms Wikidata.Slr.RelationalObservedMeet.checkedCommonConsumerConstant
#print axioms Wikidata.Slr.RelationalObservedMeet.differentRecordedAnswersBlockConstant

#print axioms Wikidata.Slr.RelationalObservedMeet.selectedRelationExact

#print axioms Wikidata.Slr.FiniteConsumer.projectedEnvelopeConsumerClosed
#print axioms Wikidata.Slr.FiniteConsumer.licenceOfProjectedEnvelope
#print axioms Wikidata.Slr.RelationalObservedMeet.recordedFactorConstancy

#print axioms Wikidata.Slr.RelationalObservedMeet.participantCoordinatesExact

#print axioms Wikidata.Slr.RelationalObservedMeet.selectDirectionalExact

#print axioms Wikidata.Slr.RelationalObservedMeet.historicalFocusRetainsKey
#print axioms Wikidata.Slr.RelationalObservedMeet.historicalFocusRetainsOutside
#print axioms Wikidata.Slr.RelationalObservedMeet.historicalFocusConsumerClosed
