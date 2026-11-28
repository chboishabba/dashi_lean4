import RequestProject.Slr.WorldSemanticFibre

/-! Golden contract for the explicit Abstract AST argument projection.
This is not the meaning or execution of a Wikifunctions implementation.
External dynamic dependencies and runtime interpretation must be paid
separately. -/
namespace Wikidata.Slr.AbstractConstructorConsumer

structure OccupationCoordinate where
  subject : String
  countries : List String
  occupations : List String
  deriving DecidableEq, Repr

structure OfficeDetail where
  office : String
  ordinal : Nat
  startYear : Nat
  endYear : Nat
  deriving DecidableEq, Repr

structure Completion where
  explicit : OccupationCoordinate
  officeDetail : Option OfficeDetail
  deriving DecidableEq, Repr

def observation (c : Completion) : OccupationCoordinate := c.explicit

def q207Explicit : OccupationCoordinate := ⟨"Q207", ["Q30"], ["Q30461"]⟩

def office : OfficeDetail := ⟨"Q11696", 43, 2001, 2009⟩

/-- Reverse-solve: the explicit argument projection does not determine
    the office detail across possible completions. Neither completion
    asserts the actual historical truth or actual function output. -/
theorem occupationDoesNotDetermineOffice :
    ¬ (∃ f : OccupationCoordinate → Option OfficeDetail,
        ∀ c : Completion, f (observation c) = c.officeDetail) := by
  rintro ⟨f,h⟩
  have a := h ⟨q207Explicit, none⟩
  have b := h ⟨q207Explicit, some office⟩
  change f q207Explicit = none at a
  change f q207Explicit = some office at b
  have impossible := a.symm.trans b
  cases impossible

end Wikidata.Slr.AbstractConstructorConsumer

#print axioms Wikidata.Slr.AbstractConstructorConsumer.occupationDoesNotDetermineOffice
