import RequestProject.Parenting
import RequestProject.ParentingDiagnostics

/-!
# Worked examples of alternative parenting

These are the executable illustrations of `RequestProject.Parenting`: a family with
four recorded parents (an egg from one mother, donated sperm, a surrogate and an
adoptive co-mother), an adoption with a stepparent, and the layers the validator
rejects.  Every claim below is decided by computation.

The identifiers `Q1`, `Q2`, … are stand-ins for individual people, as elsewhere in
the library; `Q5` is Wikidata's `human`.
-/

namespace Wikidata

namespace ParentingKB

/-! ### Worked examples -/

/-- Shorthand for an ordinary Wikidata item. -/
private def Q (s : String) : Qid := Qid.wd s

/-- A base of eight stylised individuals, all instances of `human` (Q5). -/
private def people : KB :=
  { name := "people"
    items := [Q "Q1", Q "Q2", Q "Q3", Q "Q4", Q "Q6", Q "Q7", Q "Q8", Q "Q9", Q "Q5"]
    levels := [(Q "Q5", 1)]
    inst := [(Q "Q1", Q "Q5"), (Q "Q2", Q "Q5"), (Q "Q3", Q "Q5"), (Q "Q4", Q "Q5"),
      (Q "Q6", Q "Q5"), (Q "Q7", Q "Q5"), (Q "Q8", Q "Q5"), (Q "Q9", Q "Q5")] }

/-- **Four parents.**  `Q1` is conceived from the egg of `Q4` and donated sperm from
`Q2`, carried by the surrogate `Q7`, and is raised by `Q4` and her wife `Q8`, who
adopts the child. -/
def rainbow : ParentingKB where
  base := people
  edges :=
    [ ⟨Q "Q1", Q "Q4", ParentRole.biological, ParentSlot.mother⟩,
      ⟨Q "Q1", Q "Q2", ParentRole.donor, ParentSlot.father⟩,
      ⟨Q "Q1", Q "Q7", ParentRole.surrogate, ParentSlot.parent⟩,
      ⟨Q "Q1", Q "Q8", ParentRole.adoptive, ParentSlot.parent⟩ ]
  spouses := [(Q "Q4", Q "Q8")]

example : rainbow.pValid = true := by decide

/-- The child has **four recorded parents** — the classical layer could not say
this — but only **two genetic** ones. -/
theorem rainbow_four_parents :
    (rainbow.parentsF (Q "Q1")).card = 4 ∧
    (rainbow.geneticParentsF (Q "Q1")).card = 2 ∧
    rainbow.geneticParentsL (Q "Q1") = [Q "Q4", Q "Q2"] := by decide

/-- The two mothers are co-parents without either being a genetic parent of the
other's making: `Q8` is a legal parent but not a genetic one. -/
theorem rainbow_legal_not_genetic :
    rainbow.legalParentsL (Q "Q1") = [Q "Q4", Q "Q8"] ∧
    rainbow.hasRoleB (Q "Q1") (Q "Q8") ParentRole.adoptive = true ∧
    (Q "Q8") ∉ rainbow.geneticParentsL (Q "Q1") ∧
    rainbow.coParentB (Q "Q4") (Q "Q8") = true := by decide

/-- **The surrogate gave birth but is not a genetic parent**, and the donor is a
genetic parent but neither a legal nor a social one. -/
theorem surrogacy_birth_not_genetic :
    rainbow.gestationalParent? (Q "Q1") = some (Q "Q7") ∧
    (Q "Q7") ∉ rainbow.geneticParentsL (Q "Q1") ∧
    (Q "Q7") ∉ rainbow.legalParentsL (Q "Q1") ∧
    (Q "Q2") ∈ rainbow.geneticParentsL (Q "Q1") ∧
    (Q "Q2") ∉ rainbow.legalParentsL (Q "Q1") ∧
    (Q "Q2") ∉ rainbow.socialParentsL (Q "Q1") := by decide

/-- Without a surrogate the person who gave birth is the biological mother. -/
theorem gestationalParent_default :
    (ParentingKB.mk people [⟨Q "Q1", Q "Q4", ParentRole.biological, ParentSlot.mother⟩]
      []).gestationalParent? (Q "Q1") = some (Q "Q4") := by decide

/-- **Adoption.**  `Q1` is born to `Q2` and `Q4` and adopted by the couple `Q8`, `Q9`;
`Q6` is the new spouse of `Q4` and so a stepparent. -/
def adoption : ParentingKB where
  base := people
  edges :=
    [ ⟨Q "Q1", Q "Q2", ParentRole.biological, ParentSlot.father⟩,
      ⟨Q "Q1", Q "Q4", ParentRole.biological, ParentSlot.mother⟩,
      ⟨Q "Q1", Q "Q8", ParentRole.adoptive, ParentSlot.parent⟩,
      ⟨Q "Q1", Q "Q9", ParentRole.adoptive, ParentSlot.parent⟩,
      ⟨Q "Q1", Q "Q6", ParentRole.step, ParentSlot.parent⟩ ]
  spouses := [(Q "Q8", Q "Q9"), (Q "Q4", Q "Q6")]

example : adoption.pValid = true := by decide

/-- Step-parenthood is coherent here: the stepparent is the spouse of a parent. -/
example : adoption.stepConsistent = true := by decide

/-- **Legal and genetic parenthood can pull apart.**  The adoptive parents are legal
parents and not genetic ones; the stepparent is a social parent and neither. -/
theorem adoption_legal_disjoint_genetic :
    (Q "Q8") ∈ adoption.legalParentsL (Q "Q1") ∧
    (Q "Q9") ∈ adoption.legalParentsL (Q "Q1") ∧
    (Q "Q8") ∉ adoption.geneticParentsL (Q "Q1") ∧
    (Q "Q9") ∉ adoption.geneticParentsL (Q "Q1") ∧
    (Q "Q6") ∈ adoption.socialParentsL (Q "Q1") ∧
    (Q "Q6") ∉ adoption.legalParentsL (Q "Q1") ∧
    (Q "Q6") ∉ adoption.geneticParentsL (Q "Q1") := by decide

/-- Five parents, and the genetic ones are still exactly two. -/
theorem blended_five_parents :
    (adoption.parentsF (Q "Q1")).card = 5 ∧
    (adoption.geneticParentsF (Q "Q1")).card = 2 := by decide

/-- **A stepparent is not an ancestor.**  `Q6` is a parent of `Q1` in the wide sense,
so `Q1` descends from `Q6`, but not *genetically*. -/
theorem step_not_genetic_ancestor :
    adoption.descendsFromB (Q "Q1") (Q "Q6") = true ∧
    adoption.geneticDescendsFromB (Q "Q1") (Q "Q6") = false ∧
    adoption.geneticDescendsFromB (Q "Q1") (Q "Q2") = true := by decide

/-- A layer recording two different genetic mothers is rejected, whereas two
adoptive parents are perfectly fine. -/
theorem twoGeneticMothers_rejected :
    (ParentingKB.mk people
      [⟨Q "Q1", Q "Q4", ParentRole.biological, ParentSlot.mother⟩,
       ⟨Q "Q1", Q "Q7", ParentRole.biological, ParentSlot.mother⟩] []).singleGeneticParents
      = false ∧
    (ParentingKB.mk people
      [⟨Q "Q1", Q "Q4", ParentRole.adoptive, ParentSlot.parent⟩,
       ⟨Q "Q1", Q "Q7", ParentRole.adoptive, ParentSlot.parent⟩] []).pValid = true := by decide

/-- A genetic parenthood statement must use `father` (P22) or `mother` (P25), not the
neutral `parent` (P8810). -/
theorem geneticSlot_required :
    (ParentingKB.mk people [⟨Q "Q1", Q "Q4", ParentRole.biological, ParentSlot.parent⟩]
      []).geneticSlotsTyped = false := by decide

/-- A cyclic parenting layer is rejected. -/
theorem cycle_rejected :
    (ParentingKB.mk { name := "cycle", items := [Q "Q1", Q "Q2"] }
      [⟨Q "Q1", Q "Q2", ParentRole.adoptive, ParentSlot.parent⟩,
       ⟨Q "Q2", Q "Q1", ParentRole.adoptive, ParentSlot.parent⟩] []).pValid = false := by decide


/-! ### The diagnostic report -/

/-- The two valid layers above have empty reports, and their step-parenthood is
backed by a marriage. -/
theorem examples_report_clean :
    rainbow.pErrors = [] ∧ adoption.pErrors = [] ∧ adoption.stepWarnings = [] := by decide

/-- A layer recording two genetic mothers, a self-parent and an untyped genetic
statement. -/
def broken : ParentingKB :=
  ParentingKB.mk people
    [⟨Q "Q1", Q "Q4", ParentRole.biological, ParentSlot.mother⟩,
     ⟨Q "Q1", Q "Q7", ParentRole.biological, ParentSlot.mother⟩,
     ⟨Q "Q2", Q "Q2", ParentRole.adoptive, ParentSlot.parent⟩,
     ⟨Q "Q3", Q "Q8", ParentRole.donor, ParentSlot.parent⟩] []

/-- Every problem is reported, each with its witness: the self-parenthood statement
(which is also a confusion of the genealogy with the taxonomy, since `subclass of` is
reflexive), the genetic statement filed under the neutral `parent` (P8810), and the
two genetic mothers, in both orders. -/
theorem broken_report :
    broken.pErrors =
      [ParentIssue.selfParent (Q "Q2"),
       ParentIssue.untypedGeneticParent (Q "Q3") (Q "Q8"),
       ParentIssue.twoGeneticParents (Q "Q1") (Q "Q4") (Q "Q7"),
       ParentIssue.twoGeneticParents (Q "Q1") (Q "Q7") (Q "Q4"),
       ParentIssue.parentClassConfusion (Q "Q2") (Q "Q2")] := by decide

/-- And the report is exactly the validator: it is non-empty, and the layer is
rejected. -/
theorem broken_rejected : broken.pValid = false := by decide

/-- A stepparent who is not the spouse of a parent is a warning, not an error. -/
theorem step_warning :
    (ParentingKB.mk people
      [⟨Q "Q1", Q "Q4", ParentRole.biological, ParentSlot.mother⟩,
       ⟨Q "Q1", Q "Q6", ParentRole.step, ParentSlot.parent⟩] []).pErrors = [] ∧
    (ParentingKB.mk people
      [⟨Q "Q1", Q "Q4", ParentRole.biological, ParentSlot.mother⟩,
       ⟨Q "Q1", Q "Q6", ParentRole.step, ParentSlot.parent⟩] []).stepWarnings =
      [ParentIssue.unsupportedStepparent (Q "Q1") (Q "Q6")] := by decide

end ParentingKB

/-! ### The layer at work -/

section Demo
open Wikidata Wikidata.ParentingKB

/-- info: true -/
#guard_msgs in
#eval rainbow.pValid

/-- info: 4 -/
#guard_msgs in
#eval (rainbow.parentsF (Qid.wd "Q1")).card

/-- info: 2 -/
#guard_msgs in
#eval (rainbow.geneticParentsF (Qid.wd "Q1")).card

/-- info: some (Wikidata.Qid.wd "Q7") -/
#guard_msgs in
#eval rainbow.gestationalParent? (Qid.wd "Q1")

/-- info: [Wikidata.Qid.wd "Q4", Wikidata.Qid.wd "Q8"] -/
#guard_msgs in
#eval rainbow.legalParentsL (Qid.wd "Q1")

/-- info: true -/
#guard_msgs in
#eval adoption.stepConsistent

end Demo


end Wikidata
