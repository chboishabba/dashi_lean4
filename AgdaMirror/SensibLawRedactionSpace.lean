/-! Secondary mirror of DASHI.Cognition.PNF.SensibLawRedactionSpaceExact.
Agda is authoritative. Field projection does not establish full noninterference. -/
namespace AgdaMirror.SensibLawRedactionSpace

structure PrivateDraft where
  publicText : String
  privateText : String

structure PublicOutput where
  visibleText : String

def redactOutput (draft : PrivateDraft) : PublicOutput :=
  ⟨draft.publicText⟩

theorem redactionPreservesPublicText (draft : PrivateDraft) :
    (redactOutput draft).visibleText = draft.publicText := rfl

structure SpacedPublicOutput where
  first : PublicOutput
  separator : String
  second : PublicOutput

def placeWithSpace (left right : PublicOutput) : SpacedPublicOutput :=
  ⟨left, " ", right⟩

theorem spaceSeparatorPreserved (left right : PublicOutput) :
    (placeWithSpace left right).separator = " " := rfl


/- Repeated projection of already-public output is identity. -/
def redactPublic (output : PublicOutput) : PublicOutput := output

theorem redactPublicIdempotent (output : PublicOutput) :
    redactPublic (redactPublic output) = redactPublic output := rfl

theorem redactAgainPreservesProjection (draft : PrivateDraft) :
    redactPublic (redactOutput draft) = redactOutput draft := rfl

def redactSpaced (output : SpacedPublicOutput) : SpacedPublicOutput :=
  ⟨redactPublic output.first, output.separator, redactPublic output.second⟩

theorem redactSpacedPreservesSeparator (output : SpacedPublicOutput) :
    (redactSpaced output).separator = output.separator := rfl

end AgdaMirror.SensibLawRedactionSpace
