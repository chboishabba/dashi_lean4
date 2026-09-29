/-!
DASHI-original relation index for candidate legal wrong patterns.
The Care / Transaction / Power labels are visible in the user-supplied
uvsmpub / Rob McNamara "A System of Wrong" diagram; directional semantics,
offence placement and legal interpretation here are DASHI constructions,
not attributed to Forrest Landry or McNamara.

Primary-law locator (historical consolidation; not a present-law claim):
Queensland Criminal Code Act 1899, ss 245-246, 354A, 391, 408C, 409, 415.
https://www.legislation.qld.gov.au/view/whole/html/inforce/2024-08-09/act-1899-009

A source reference never establishes liability or discharges an offence element.
-/
namespace AgdaMirror.Law.WrongTypeGrid

inductive Mode
  | care | transaction | power
  deriving DecidableEq, Repr

structure Cell where
  actor : Mode
  context : Mode
  deriving DecidableEq, Repr

inductive Pattern
  | neglect | professionalNegligence | fiduciaryAbuse
  | theft | fraud | extortion | robbery | assault | kidnapping
  | bribery | publicPowerMisuse | cyberMisuse | environmentalHarm
  deriving DecidableEq, Repr

structure SourceLocator where
  originator : String
  work : String
  canonicalURL : String
  pinpoint : String
  version : String

structure GridCandidate where
  wrongTypeId : String
  pattern : Pattern
  cell : Cell
  circumstanceRef : String
  evidenceRef : String
  source : SourceLocator
  attributionScope : String

def qldCode (section : String) : SourceLocator :=
  ⟨"Queensland Parliament", "Criminal Code Act 1899 (Qld)",
   "https://www.legislation.qld.gov.au/view/whole/html/inforce/2024-08-09/act-1899-009",
   section, "2024-08-09 historical consolidation"⟩

-- This is an evidence-index relation, not an offence elements judgement.
def Fits (wrong : String) (cell : Cell) (xs : List GridCandidate) : Prop :=
  ∃ x ∈ xs, x.wrongTypeId = wrong ∧ x.cell = cell

def first : GridCandidate :=
  ⟨"example:abstract-wrong-type", .fraud, ⟨.transaction, .transaction⟩,
   "example:context-1", "example:evidence-pending", qldCode "s 408C",
   "DASHI hypothetical; not a legal finding"⟩

def second : GridCandidate :=
  ⟨"example:abstract-wrong-type", .fraud, ⟨.power, .transaction⟩,
   "example:context-2", "example:evidence-pending", qldCode "s 408C",
   "DASHI hypothetical; not a legal finding"⟩

def sample : List GridCandidate := [first, second]

theorem example_many_to_many :
    Fits "example:abstract-wrong-type" ⟨.transaction, .transaction⟩ sample ∧
    Fits "example:abstract-wrong-type" ⟨.power, .transaction⟩ sample := by
  constructor
  · exact ⟨first, by simp [sample], rfl, rfl⟩
  · exact ⟨second, by simp [sample], rfl, rfl⟩

-- No coercion from candidate into this assessment: authority, each
-- legal element and possible defences must be separately sourced.
structure LegalAssessmentBoundary where
  candidate : GridCandidate
  applicableNormEvidence : Prop
  satisfiedElementEvidence : Prop
  defenceAndExceptionReview : Prop

end AgdaMirror.Law.WrongTypeGrid
