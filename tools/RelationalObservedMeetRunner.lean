import RequestProject.Slr.RelationalObservedMeet

def main (args : List String) : IO UInt32 := do
  match args with
  | [input, output] => Wikidata.Slr.RelationalObservedMeet.run input output
  | _ =>
    IO.eprintln "usage: RelationalObservedMeetRunner INPUT_NATIVE_FAMILY_JSON OUTPUT"
    return 2

#print axioms Wikidata.Slr.RelationalObservedMeet.checkedMembershipSound
#print axioms Wikidata.Slr.RelationalObservedMeet.commonObservedSound
#print axioms Wikidata.Slr.RelationalObservedMeet.checkedCommonConsumerConstant
#print axioms Wikidata.Slr.RelationalObservedMeet.differentRecordedAnswersBlockConstant
