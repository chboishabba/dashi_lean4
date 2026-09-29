/-!
DASHI-original relation index for candidate legal wrong patterns.
Rob McNamara's user-supplied Episode 4 transcript explicitly defines
the first coordinate as the *violated frame* and the second as the
*imposed frame*. His examples populate all nine cells. McNamara attributes
the underlying framework to Forrest Landry; original authorship and
his universality claim have NOT been independently established.
Lean predicates and proofs are DASHI-original.

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
  violated : Mode
  imposed : Mode
  deriving DecidableEq, Repr

inductive Pattern
  | neglect | professionalNegligence | fiduciaryAbuse
  | theft | fraud | extortion | robbery | assault | kidnapping
  | murder | manslaughter | sexualAssault | burglary
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
  ⟨"example:abstract-wrong-type", .fraud, ⟨.transaction, .power⟩,
   "example:context-2", "example:evidence-pending", qldCode "s 408C",
   "DASHI hypothetical; not a legal finding"⟩

def sample : List GridCandidate := [first, second]

theorem example_many_to_many :
    Fits "example:abstract-wrong-type" ⟨.transaction, .transaction⟩ sample ∧
    Fits "example:abstract-wrong-type" ⟨.transaction, .power⟩ sample := by
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

/-- Each fixture is an offence-family locator with an explicitly editorial
cell assignment. A cell may be supported by the video while legal elements remain unproved. -/
def crimeCandidate (id : String) (p : Pattern) (c : Cell)
    (section : String) : GridCandidate :=
  ⟨id, p, c, "illustrative:context-not-established", "evidence:not-provided",
    qldCode section, "DASHI illustrative fixture; statute does not classify cells"⟩

def illustrativeCrimes : List GridCandidate := [
  crimeCandidate "wrong:QLD:assault" .assault ⟨.care, .power⟩ "ss 245-246",
  crimeCandidate "wrong:QLD:sexual-assault" .sexualAssault ⟨.care, .power⟩ "s 352",
  crimeCandidate "wrong:QLD:murder" .murder ⟨.care, .power⟩ "s 302",
  crimeCandidate "wrong:QLD:manslaughter" .manslaughter ⟨.care, .power⟩ "s 303",
  crimeCandidate "wrong:QLD:stealing" .theft ⟨.transaction, .transaction⟩ "s 391",
  crimeCandidate "wrong:QLD:fraud" .fraud ⟨.transaction, .transaction⟩ "s 408C",
  crimeCandidate "wrong:QLD:robbery" .robbery ⟨.transaction, .power⟩ "s 409",
  crimeCandidate "wrong:QLD:extortion" .extortion ⟨.transaction, .power⟩ "s 415",
  crimeCandidate "wrong:QLD:kidnapping-ransom" .kidnapping ⟨.care, .power⟩ "s 354A",
  crimeCandidate "wrong:QLD:burglary" .burglary ⟨.transaction, .power⟩ "s 419",
  crimeCandidate "wrong:QLD:computer-misuse" .cyberMisuse ⟨.transaction, .power⟩ "s 408E"
]


/-- Exact episode-level labels and examples supplied by user transcript.
These are claims of the named speaker, not proven classifications of
criminal offences or evidence that such conduct is unlawful. -/
structure EpisodeCellClaim where
  cell : Cell
  label : String
  spokenExamples : String
  speaker : String := "Rob McNamara"
  work : String := "A System of Wrong, Episode 4: The Grid"
  provenance : String := "user-provided transcript 2026-09-30"
  status : String := "attributed speech; legally unverified"

def spoken (target imposed : Mode) (label examples : String) :
    EpisodeCellClaim :=
  ⟨⟨target, imposed⟩, label, examples,
    "Rob McNamara", "A System of Wrong, Episode 4: The Grid",
    "user-provided transcript 2026-09-30",
    "attributed speech; legally unverified"⟩

def episodeCells : List EpisodeCellClaim := [
  spoken .care .care "care betrayed from within"
    "neglect; abandonment; institutional self-service",
  spoken .care .transaction "priced person"
    "trafficking; commodified intimacy; engagement metrics",
  spoken .care .power "body, safety, life seized by force"
    "murder; assault; rape; enslavement",
  spoken .transaction .care "rigged gift"
    "conditional charity; aid with hidden strings",
  spoken .transaction .transaction "corrupted ledger"
    "theft; fraud; forgery; embezzlement",
  spoken .transaction .power "manufactured sale"
    "robbery; extortion; ransomware; protection racket",
  spoken .power .care "authority dissolved by sentiment"
    "judge favouring friend; commander sparing guilty",
  spoken .power .transaction "sold decision"
    "bribery; corruption; regulatory capture",
  spoken .power .power "betrayal from within"
    "treason; sedition; insider subversion"
]

-- The speaker's assertion that all serious legal wrongs belong in the
-- nine cells is intentionally NOT promoted into a theorem.
end AgdaMirror.Law.WrongTypeGrid
