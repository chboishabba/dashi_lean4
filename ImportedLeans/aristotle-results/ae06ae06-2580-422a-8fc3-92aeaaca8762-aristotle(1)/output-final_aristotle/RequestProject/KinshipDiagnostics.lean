import RequestProject.Kinship
import RequestProject.Diagnostics

/-!
# A diagnostic report for the kinship layer

`RequestProject.Diagnostics` turns the Boolean validator of a knowledge base into a
list of concrete, individually witnessed issues.  This file does the same for the
kinship layer of `RequestProject.Kinship`: `father` (P22), `mother` (P25) and
`spouse` (P26) statements pointing at undeclared items, a person with two different
fathers or two different mothers, a cycle in the ancestry, a person married to
themselves, and parenthood statements between items already related by `subclass of`
or `instance of`.

The report is **sound and complete**: it is empty exactly when the layer passes the
validator (`FKB.fErrors_eq_nil_iff`, `FKB.report_eq_nil_iff_fValid`), so nothing is
invented and nothing is missed, and every issue carries its witness.
-/

namespace Wikidata

/-- The kinds of problem a kinship layer can have. -/
inductive KinIssue where
  /-- A `father` (P22) statement with an endpoint that is not a declared item. -/
  | danglingFather (a b : Qid)
  /-- A `mother` (P25) statement with an endpoint that is not a declared item. -/
  | danglingMother (a b : Qid)
  /-- A `spouse` (P26) statement with an endpoint that is not a declared item. -/
  | danglingSpouse (a b : Qid)
  /-- A person recorded with two different fathers. -/
  | twoFathers (a b c : Qid)
  /-- A person recorded with two different mothers. -/
  | twoMothers (a b c : Qid)
  /-- Two distinct people each descending from the other. -/
  | ancestryCycle (a b : Qid)
  /-- A person recorded as their own spouse. -/
  | selfSpouse (a : Qid)
  /-- A parenthood statement between items already related by `subclass of` or
  `instance of`. -/
  | kinClassConfusion (a b : Qid)
deriving DecidableEq, Repr, Inhabited

namespace FKB

variable (f : FKB)

/-! ### The individual checks -/

/-- P22 statements with an undeclared endpoint. -/
def danglingFatherIssues : List KinIssue :=
  (f.fathers.filter (fun r => !(r.1 ∈ f.base.items && r.2 ∈ f.base.items))).map
    (fun r => KinIssue.danglingFather r.1 r.2)

/-- P25 statements with an undeclared endpoint. -/
def danglingMotherIssues : List KinIssue :=
  (f.mothers.filter (fun r => !(r.1 ∈ f.base.items && r.2 ∈ f.base.items))).map
    (fun r => KinIssue.danglingMother r.1 r.2)

/-- P26 statements with an undeclared endpoint. -/
def danglingSpouseIssues : List KinIssue :=
  (f.spouses.filter (fun r => !(r.1 ∈ f.base.items && r.2 ∈ f.base.items))).map
    (fun r => KinIssue.danglingSpouse r.1 r.2)

/-- People recorded with two different fathers. -/
def twoFatherIssues : List KinIssue :=
  ((f.fathers.product f.fathers).filter (fun p => p.1.1 == p.2.1 && p.1.2 != p.2.2)).map
    (fun p => KinIssue.twoFathers p.1.1 p.1.2 p.2.2)

/-- People recorded with two different mothers. -/
def twoMotherIssues : List KinIssue :=
  ((f.mothers.product f.mothers).filter (fun p => p.1.1 == p.2.1 && p.1.2 != p.2.2)).map
    (fun p => KinIssue.twoMothers p.1.1 p.1.2 p.2.2)

/-- Genuine cycles in the ancestry. -/
def ancestryCycleIssues : List KinIssue :=
  ((f.base.items.product f.base.items).filter
    (fun p => f.descendsFromB p.1 p.2 && f.descendsFromB p.2 p.1 && p.1 != p.2)).map
    (fun p => KinIssue.ancestryCycle p.1 p.2)

/-- People recorded as their own spouse. -/
def selfSpouseIssues : List KinIssue :=
  (f.spouses.filter (fun r => r.1 == r.2)).map (fun r => KinIssue.selfSpouse r.1)

/-- Parenthood statements confusing the genealogy with the taxonomy. -/
def kinClassConfusionIssues : List KinIssue :=
  ((f.fathers ++ f.mothers).filter
    (fun r => !(!f.base.isSubclassOf r.1 r.2 && !f.base.isInstanceOf r.1 r.2))).map
    (fun r => KinIssue.kinClassConfusion r.1 r.2)

/-- The full error report of a kinship layer (the underlying taxonomy is reported
separately, by `KB.errors`). -/
def fErrors : List KinIssue :=
  f.danglingFatherIssues ++ f.danglingMotherIssues ++ f.danglingSpouseIssues ++
    f.twoFatherIssues ++ f.twoMotherIssues ++ f.ancestryCycleIssues ++
    f.selfSpouseIssues ++ f.kinClassConfusionIssues

variable {f}

/-! ### Each check matches its Boolean counterpart -/

theorem danglingFatherIssues_eq_nil_iff :
    f.danglingFatherIssues = [] ↔
      f.fathers.all (fun r => r.1 ∈ f.base.items && r.2 ∈ f.base.items) = true := by
  simp [danglingFatherIssues, List.filter_eq_nil_iff, List.all_eq_true]

theorem danglingMotherIssues_eq_nil_iff :
    f.danglingMotherIssues = [] ↔
      f.mothers.all (fun r => r.1 ∈ f.base.items && r.2 ∈ f.base.items) = true := by
  simp [danglingMotherIssues, List.filter_eq_nil_iff, List.all_eq_true]

theorem danglingSpouseIssues_eq_nil_iff :
    f.danglingSpouseIssues = [] ↔
      f.spouses.all (fun r => r.1 ∈ f.base.items && r.2 ∈ f.base.items) = true := by
  simp [danglingSpouseIssues, List.filter_eq_nil_iff, List.all_eq_true]

/-- The three dangling checks together are exactly well-formedness of the layer, given
a well-formed taxonomy. -/
theorem fWellFormed_iff (hbase : f.base.wellFormed = true) :
    f.fWellFormed = true ↔
      f.danglingFatherIssues = [] ∧ f.danglingMotherIssues = [] ∧
        f.danglingSpouseIssues = [] := by
  simp only [fWellFormed, Bool.and_eq_true, hbase, true_and,
    danglingFatherIssues_eq_nil_iff, danglingMotherIssues_eq_nil_iff,
    danglingSpouseIssues_eq_nil_iff]
  tauto

theorem twoFatherIssues_eq_nil_iff :
    f.twoFatherIssues = [] ↔
      f.fathers.all (fun r => f.fathers.all (fun s => r.1 != s.1 || r.2 == s.2)) = true := by
  rw [twoFatherIssues, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  constructor
  · intro h
    simp only [List.all_eq_true]
    rintro r hr r' hr'
    have hp := h (a := (r, r')) (List.pair_mem_product.2 ⟨hr, hr'⟩)
    revert hp
    cases h1 : (r.1 == r'.1) <;> cases h2 : (r.2 == r'.2) <;> simp_all
  · rintro h ⟨r, r'⟩ hp
    obtain ⟨hr, hr'⟩ := List.pair_mem_product.1 hp
    have hall := List.all_eq_true.1 (List.all_eq_true.1 h r hr) r' hr'
    revert hall
    cases h1 : (r.1 == r'.1) <;> cases h2 : (r.2 == r'.2) <;> simp_all

theorem twoMotherIssues_eq_nil_iff :
    f.twoMotherIssues = [] ↔
      f.mothers.all (fun r => f.mothers.all (fun s => r.1 != s.1 || r.2 == s.2)) = true := by
  rw [twoMotherIssues, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  constructor
  · intro h
    simp only [List.all_eq_true]
    rintro r hr r' hr'
    have hp := h (a := (r, r')) (List.pair_mem_product.2 ⟨hr, hr'⟩)
    revert hp
    cases h1 : (r.1 == r'.1) <;> cases h2 : (r.2 == r'.2) <;> simp_all
  · rintro h ⟨r, r'⟩ hp
    obtain ⟨hr, hr'⟩ := List.pair_mem_product.1 hp
    have hall := List.all_eq_true.1 (List.all_eq_true.1 h r hr) r' hr'
    revert hall
    cases h1 : (r.1 == r'.1) <;> cases h2 : (r.2 == r'.2) <;> simp_all

/-- The two multiple-parent checks together are exactly the `singleParents` check. -/
theorem singleParents_iff :
    f.singleParents = true ↔ f.twoFatherIssues = [] ∧ f.twoMotherIssues = [] := by
  simp only [singleParents, Bool.and_eq_true, twoFatherIssues_eq_nil_iff,
    twoMotherIssues_eq_nil_iff]

theorem ancestryCycleIssues_eq_nil_iff :
    f.ancestryCycleIssues = [] ↔ f.fAcyclic = true := by
  rw [ancestryCycleIssues, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  constructor
  · intro h
    simp only [fAcyclic, List.all_eq_true]
    intro a ha b hb
    have hp := h (a := (a, b)) (List.pair_mem_product.2 ⟨ha, hb⟩)
    revert hp
    cases hab : f.descendsFromB a b <;> cases hba : f.descendsFromB b a <;>
      cases heq : (a == b) <;> simp_all
  · rintro h ⟨a, b⟩ hp
    obtain ⟨ha, hb⟩ := List.pair_mem_product.1 hp
    simp only [fAcyclic, List.all_eq_true] at h
    have hall := h a ha b hb
    revert hall
    cases hab : f.descendsFromB a b <;> cases hba : f.descendsFromB b a <;>
      cases heq : (a == b) <;> simp_all

theorem selfSpouseIssues_eq_nil_iff : f.selfSpouseIssues = [] ↔ f.noSelfSpouse = true := by
  simp [selfSpouseIssues, noSelfSpouse, List.filter_eq_nil_iff, List.all_eq_true]

theorem kinClassConfusionIssues_eq_nil_iff :
    f.kinClassConfusionIssues = [] ↔ f.noKinClassConfusion = true := by
  simp [kinClassConfusionIssues, noKinClassConfusion, List.filter_eq_nil_iff,
    List.all_eq_true]

/-! ### The report is sound and complete -/

/-- **The kinship error report is empty exactly when the kinship layer passes its
checks** (given a well-formed underlying taxonomy). -/
theorem fErrors_eq_nil_iff (hbase : f.base.wellFormed = true) :
    f.fErrors = [] ↔ f.fLayerValid = true := by
  rw [fErrors]
  simp only [List.append_eq_nil_iff, fLayerValid, Bool.and_eq_true,
    fWellFormed_iff hbase, singleParents_iff, ancestryCycleIssues_eq_nil_iff,
    selfSpouseIssues_eq_nil_iff, kinClassConfusionIssues_eq_nil_iff]
  tauto

/-- **The full report**: the taxonomy report and the kinship report are both empty
exactly when the whole layer is valid. -/
theorem report_eq_nil_iff_fValid :
    (f.base.errors = [] ∧ f.fErrors = []) ↔ f.fValid = true := by
  constructor
  · rintro ⟨hb, hk⟩
    have hvalid : f.base.valid = true := KB.errors_eq_nil_iff_valid.1 hb
    have hwf : f.base.wellFormed = true := KB.valid_wellFormed hvalid
    simp only [fValid, Bool.and_eq_true]
    exact ⟨hvalid, (fErrors_eq_nil_iff hwf).1 hk⟩
  · intro h
    simp only [fValid, Bool.and_eq_true] at h
    have hwf : f.base.wellFormed = true := KB.valid_wellFormed h.1
    exact ⟨KB.errors_eq_nil_iff_valid.2 h.1, (fErrors_eq_nil_iff hwf).2 h.2⟩

/-! ### Worked reports -/

example : family.fErrors = [] := by decide

example : cyclicFamily.fErrors ≠ [] := by decide

example : twoFathers.fErrors ≠ [] := by decide

end FKB

end Wikidata
