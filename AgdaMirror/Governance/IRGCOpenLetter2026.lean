/-!
Typed mirror of the 2026 IRGC open letter as a source-bounded political
communication.  This file models attribution and argumentative structure only.

Primary source:
IRGC, open letter to the people of the United States, 2026-09-29,
https://newsmedia.tasnimmedia.com/Tasnim/Uploaded/Document/1405/07/07/140507071435363573839468.pdf

Publication of a claim is not evidence that the proposition is true, that a
theological interpretation is doctrinally authoritative, or that an audience
was persuaded.
-/

namespace AgdaMirror.Governance.IRGCOpenLetter2026

inductive Actor
  | irgc | americanPeople | americanGovernment | iranianPeople
  | americanPoliticalElite | unnamedWorldPublic
  deriving DecidableEq, Repr

inductive Audience
  | usPublic | scholars | students | journalists | generalAudience
  deriving DecidableEq, Repr

inductive ClaimKind
  | empirical | theological | historical | evaluative | predictive | attributional
  deriving DecidableEq, Repr

inductive SpeechAct
  | assertion | accusation | prediction | warning | appeal | exhortation
  | moralAnalogy | identityReframing | solidarityOffer | conditionalCoexistence
  deriving DecidableEq, Repr

inductive RhetoricalRole
  | peopleStateSeparation | commonOppressorFrame | sharedVictimFrame
  | agencyAttribution | coexistenceFrame | liberationFrame
  | scripturalEthicalBridge | eschatologicalClosure
  deriving DecidableEq, Repr

inductive Tradition
  | islam | christianity | judaism
  deriving DecidableEq, Repr

inductive NormativeText
  | quran13_11 | quran21_105 | matthew7_12 | luke6_31
  | jeremiah18_7_10 | talmudicGoldenRule
  deriving DecidableEq, Repr

structure Artifact where
  issuer : Actor
  audience : Audience
  title : String
  date : String
  primaryReceipt : String

def irgcLetter : Artifact :=
  ⟨.irgc, .usPublic,
   "IRGC open letter to the people of the United States",
   "2026-09-29",
   "IRGC 2026 primary English PDF"⟩

structure AttributedClaim where
  claimId : String
  kind : ClaimKind
  assertedBy : Actor
  content : String
  sourceReceipt : String
  independentlyEstablished : Bool

def mkSourceLocalClaim (id : String) (kind : ClaimKind) (speaker : Actor)
    (content receipt : String) : AttributedClaim :=
  ⟨id, kind, speaker, content, receipt, false⟩

theorem publication_does_not_promote_truth
    (id : String) (kind : ClaimKind) (speaker : Actor)
    (content receipt : String) :
    (mkSourceLocalClaim id kind speaker content receipt).independentlyEstablished = false := rfl

structure CrossTraditionCitation where
  tradition : Tradition
  sourceText : NormativeText
  locator : String
  invokedPrinciple : String
  receipt : String
  doctrinalIdentityEstablished : Bool

def mkInvocation (tradition : Tradition) (text : NormativeText)
    (locator principle receipt : String) : CrossTraditionCitation :=
  ⟨tradition, text, locator, principle, receipt, false⟩

theorem invocation_does_not_establish_doctrinal_identity
    (tradition : Tradition) (text : NormativeText)
    (locator principle receipt : String) :
    (mkInvocation tradition text locator principle receipt).doctrinalIdentityEstablished = false := rfl

def quranAgency : CrossTraditionCitation :=
  mkInvocation .islam .quran13_11 "Qur'an 13:11"
    "people changing their own condition / affairs"
    "opening citation in primary PDF"

def matthewReciprocity : CrossTraditionCitation :=
  mkInvocation .christianity .matthew7_12 "Matthew 7:12"
    "reciprocity / treatment of others"
    "cross-tradition citation in primary PDF"

def lukeReciprocity : CrossTraditionCitation :=
  mkInvocation .christianity .luke6_31 "Luke 6:31"
    "reciprocity / treatment of others"
    "cross-tradition citation in primary PDF"

def jeremiahConditionality : CrossTraditionCitation :=
  mkInvocation .christianity .jeremiah18_7_10 "Jeremiah 18:7-10"
    "conditional judgement and change"
    "cross-tradition citation in primary PDF"

def talmudicReciprocity : CrossTraditionCitation :=
  mkInvocation .judaism .talmudicGoldenRule
    "Talmudic reciprocity citation as rendered by source"
    "do not do to another what is hateful to you"
    "cross-tradition citation in primary PDF"

def quranClosure : CrossTraditionCitation :=
  mkInvocation .islam .quran21_105 "Qur'an 21:105"
    "inheritance of the earth by the righteous / servants"
    "closing citation in primary PDF"

inductive AudienceEffectEstablished : Prop

theorem publication_alone_cannot_establish_audience_effect
    (_artifact : Artifact) : ¬ AudienceEffectEstablished := by
  intro h
  cases h

end AgdaMirror.Governance.IRGCOpenLetter2026
