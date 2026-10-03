/-!
DASHI-original countermodel to unconditional Care/Transaction/Power
classification completeness.

Source distinction:
* Rob McNamara, "A System of Wrong", Episode 4 ("The Grid"),
  user transcript supplied 2026-09-30, asserts every serious wrong fits.
* The attribution to Forrest Landry is McNamara's; no independent
  confirmation of authorship of this nine-cell schema.
* Queensland Nature Conservation Act 1992, s 89, compilation current
  as at 16 June 2026:
  https://www.legislation.qld.gov.au/view/pdf/inforce/current/act-1992-020
  The statutory offence has qualifications, exceptions and defences.
* Neither the statutory source nor the transcript proves that an actual
  environmental offence lacks every possible philosophical frame.
* The model, definition of grounded placement, and proofs are DASHI.
-/
import AgdaMirror.Law.WrongTypeGrid

namespace AgdaMirror.Law.WrongTypeGrid.Coverage

/-- The semantic grounds needed to *justify* a cell classification.
    No legal liability or statute applicability is constructed here. -/
structure Grounding where
  violatedBasis : Mode → Prop
  imposedBasis : Mode → Prop

def GroundedCell (g : Grounding) (c : Cell) : Prop :=
  g.violatedBasis c.violated ∧ g.imposedBasis c.imposed

def UniversallyCovered (wrongs : Type) (grounds : wrongs → Grounding) : Prop :=
  ∀ w : wrongs, ∃ c : Cell, GroundedCell (grounds w) c

/-- Countermodel: some interpretive frameworks contain no justified
    violated-frame basis for this hypothetical WrongType. -/
def noneViolated : Grounding where
  violatedBasis := fun _ => False
  imposedBasis := fun _ => True

theorem no_cell_under_noneViolated (c : Cell) :
    ¬ GroundedCell noneViolated c := by
  intro h
  exact h.1

inductive EcosystemWrong
  | protectedPlantTaking

def ecosystemInterpretation : EcosystemWrong → Grounding :=
  fun _ => noneViolated

theorem not_universally_covered :
    ¬ UniversallyCovered EcosystemWrong ecosystemInterpretation := by
  intro h
  obtain ⟨c, hc⟩ := h .protectedPlantTaking
  exact no_cell_under_noneViolated c hc

/-- The logical countermodel does not prove the actual Queensland
s 89 offence has no possible Care/Transaction/Power interpretation. -/
end AgdaMirror.Law.WrongTypeGrid.Coverage
