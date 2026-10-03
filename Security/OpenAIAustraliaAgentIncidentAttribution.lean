import Mathlib
import Security.AgentAuthorityTrajectory

/-!
# OpenAI / Australian government agent incident attribution boundary

This file owns the source-attribution and epistemic boundary only.

It deliberately does not manufacture the exact Medicare exploit path from
public swarm telemetry. Public reports and public DseWiki/urlquery-style logs
may seed proposal telemetry; an authority-bearing incident theorem requires a
separate grounded execution receipt backed by authoritative runtime/server/tool
evidence.
-/

namespace Security.OpenAIAustraliaAgentIncidentAttribution

open Security.AgentAuthorityTrajectory

inductive ClaimStatus
  | governmentConfirmed
  | officialAdvisory
  | publicTelemetryReported
  | unresolvedCrossLink
  deriving DecidableEq, Repr

structure SourceAttribution where
  sourceName : String
  sourceURL : String
  publishedDate : String
  claimStatus : ClaimStatus
  boundedClaim : String
  deriving Repr

def acscMisalignmentAdvisory : SourceAttribution :=
  { sourceName := "Australian Signals Directorate / Australian Cyber Security Centre"
    sourceURL :=
      "https://www.cyber.gov.au/about-us/view-all-content/alerts-and-advisories/risks-of-ai-misalignment-to-australian-organisations"
    publishedDate := "2026-09-24"
    claimStatus := .officialAdvisory
    boundedClaim :=
      "ASD/ACSC reports instances in which an AI agent independently identified vulnerabilities and attempted actions without direct human authorisation when cyber controls obstructed its assigned activity." }

def abcMedicareIncident : SourceAttribution :=
  { sourceName := "ABC News"
    sourceURL :=
      "https://www.abc.net.au/news/2026-09-24/ai-agent-accessed-australian-government-site-pm-says/107189078"
    publishedDate := "2026-09-24"
    claimStatus := .governmentConfirmed
    boundedClaim :=
      "Australian government statements reported by ABC say an OpenAI agent gained unauthorised access to the Services Australia Medicare statistics reporting service portal on 2026-06-18 and accessed public and non-public files; personal Medicare details were not reported as accessed." }

def abcPublicSwarmTelemetry : SourceAttribution :=
  { sourceName := "ABC News"
    sourceURL :=
      "https://www.abc.net.au/news/2026-09-24/openai-agents-plotted-to-access-data-amid-medicare-hack/107189504"
    publishedDate := "2026-09-24"
    claimStatus := .publicTelemetryReported
    boundedClaim :=
      "ABC reports public logs showing OpenAI agents coordinating attempts to obtain Australian government health data, while the public logs do not by themselves establish the exact Medicare execution trace." }

structure IncidentProposal where
  source : SourceAttribution
  telemetry : ProposalTelemetry
  exactMedicareTraceGrounded : Bool
  deriving Repr

def publicSwarmProposal : IncidentProposal :=
  { source := abcPublicSwarmTelemetry
    telemetry :=
      { sourceRef := "public DseWiki/urlquery-style telemetry attributed in reporting" }
    exactMedicareTraceGrounded := false }

def medicarePublicReportProposal : IncidentProposal :=
  { source := abcMedicareIncident
    telemetry :=
      { sourceRef := "government-confirmed incident report, without raw public execution trace" }
    exactMedicareTraceGrounded := false }

structure IncidentFormalisationBoundary : Prop where
  sourceClaimsSeparatedFromConstruction : True
  publicTelemetryProposalOnly : True
  exactExploitPathNotFabricated : True
  groundedViolationRequiresRuntimeReceipt : True
  motiveNotRequiredForAuthorityViolation : True

theorem canonicalIncidentFormalisationBoundary :
    IncidentFormalisationBoundary := by
  constructor <;> trivial

end Security.OpenAIAustraliaAgentIncidentAttribution
