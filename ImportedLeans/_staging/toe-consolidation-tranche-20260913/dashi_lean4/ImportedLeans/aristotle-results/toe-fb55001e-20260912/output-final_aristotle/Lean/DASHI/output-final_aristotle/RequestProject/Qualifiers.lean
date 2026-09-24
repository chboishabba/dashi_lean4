import RequestProject.Ranks

/-!
# Qualifier constraints and the property scope

A Wikidata statement is not just a subject, a property and a value: it carries
**qualifiers**, property–value pairs that refine it (`point in time` P585,
`determination method` P459, `reason for deprecated rank` P2241, ...).  Which
qualifiers a statement *may* and *must* carry is governed by two constraints of
the property, and a third constraint says in which **slot** a property may be
used at all:

* **allowed qualifiers** (Q21510851) — only the listed properties may appear as
  qualifiers of a statement of this property;
* **mandatory qualifiers** (Q21510856) — the listed properties must appear;
* **property scope** (Q53869507) — whether the property may be used as the main
  value of a statement, as a qualifier, or both.

This file adds that layer on top of the claim model of `RequestProject.Ranks`.

* `Wikidata.QualSpec` is the qualifier profile of one property and
  `Wikidata.QualSpec.claimOk` the executable check for a single claim;
  `Wikidata.qualSetOk` checks a whole claim set against a table of profiles.
* `Wikidata.ScopeSpec` is the scope of one property and `Wikidata.scopeOk` the
  executable scope check.

The results are:

* the checks are characterised exactly — `QualSpec.allowedOk_iff`,
  `QualSpec.mandatoryOk_iff`, `QualSpec.claimOk_iff`, `qualSetOk_iff`,
  `scopeOk_iff` — so they neither over- nor under-approximate the constraints;
* an empty list of allowed qualifiers forbids qualifiers outright
  (`QualSpec.quals_eq_nil_of_allowed_nil`), and a mandatory qualifier that is not
  allowed makes the property unusable (`QualSpec.mandatory_subset_allowed`,
  `QualSpec.not_claimOk_of_mandatory_not_allowed`);
* a mandatory qualifier can always be read off a conforming claim
  (`QualSpec.qualValue_isSome_of_mandatory`), and when a claim does not repeat a
  qualifier property the lookup is exactly membership
  (`Claim.qualValue_eq_some_iff_of_nodup`);
* conformance is **downward closed**: any sublist of a conforming claim set
  conforms, so in particular the truthy fragment of a conforming base conforms
  (`qualSetOk_truthy`, `scopeOk_truthy`) — filtering by rank can never introduce
  a qualifier defect;
* the checks are monotone in the constraints: enlarging the allowed list or
  shrinking the mandatory list preserves conformance
  (`QualSpec.allowedOk_mono`, `QualSpec.mandatoryOk_mono`), and a property absent
  from the table is unconstrained (`qualSetOk_of_not_mem_table`);
* a property whose scope excludes the main slot has no statements of its own in a
  conforming base (`no_main_of_scope`), and one whose scope excludes the
  qualifier slot appears in no qualifier list (`not_qual_of_scope`).

A worked fragment reuses Berlin's population statements from
`RequestProject.Ranks`: the base as a whole is **rejected**, because the
deprecated statement carries `reason for deprecated rank` but no `point in time`,
while its truthy fragment is accepted; `point in time` is checked to be usable as
a qualifier only, and a base using it as a main property is rejected.

As elsewhere in this development the identifiers follow Wikidata, but the example
fragment is a stylised excerpt; the theorems about it are statements about that
fragment.
-/

namespace Wikidata

/-- Looking a key up in a table without repeated keys returns the value recorded
for it. -/
theorem List.lookup_eq_some_of_nodup_keys {α β : Type*} [DecidableEq α] :
    ∀ (l : List (α × β)) (a : α) (b : β),
      (l.map Prod.fst).Nodup → (a, b) ∈ l → l.lookup a = some b := by
  intro l
  induction l with
  | nil => intro a b _ hm; cases hm
  | cons x t ih =>
      obtain ⟨k, w⟩ := x
      intro a b h hm
      rw [_root_.List.map_cons, _root_.List.nodup_cons] at h
      rcases _root_.List.mem_cons.1 hm with heq | hmt
      · cases heq; simp [_root_.List.lookup]
      · have hne : a ≠ k := by
          rintro rfl
          exact h.1 (_root_.List.mem_map.2 ⟨(a, b), hmt, rfl⟩)
        have hb : (a == k) = false := by simpa using hne
        simp only [_root_.List.lookup, hb]
        exact ih a b h.2 hmt

/-- A key that occurs in a table can be looked up. -/
theorem List.lookup_isSome_of_mem {α β : Type*} [DecidableEq α] :
    ∀ (l : List (α × β)) (a : α) (b : β), (a, b) ∈ l → (l.lookup a).isSome := by
  intro l
  induction l with
  | nil => intro a b hm; cases hm
  | cons x t ih =>
      obtain ⟨k, w⟩ := x
      intro a b hm
      rcases _root_.List.mem_cons.1 hm with heq | hmt
      · cases heq; simp [_root_.List.lookup]
      · by_cases hEq : a = k
        · simp [_root_.List.lookup, hEq]
        · have hb : (a == k) = false := by simpa using hEq
          simp only [_root_.List.lookup, hb]
          exact ih a b hmt

namespace Claim

/-- The properties used as qualifiers of a claim. -/
def qualPids (c : Claim) : List Pid := c.quals.map Prod.fst

@[simp] theorem mem_qualPids {c : Claim} {p : Pid} :
    p ∈ c.qualPids ↔ ∃ v, (p, v) ∈ c.quals := by
  simp only [qualPids, List.mem_map]
  constructor
  · rintro ⟨⟨a, b⟩, hmem, h⟩
    simp only at h
    subst h
    exact ⟨b, hmem⟩
  · rintro ⟨v, hv⟩
    exact ⟨(p, v), hv, rfl⟩

/-- The value of a qualifier of a claim, if the claim carries one. -/
def qualValue (c : Claim) (p : Pid) : Option Value := c.quals.lookup p

theorem qualValue_eq_some_mem {c : Claim} {p : Pid} {v : Value}
    (h : c.qualValue p = some v) : (p, v) ∈ c.quals := by
  obtain ⟨l₁, l₂, hl, -⟩ := _root_.List.lookup_eq_some_iff.1 h
  rw [show c.quals = l₁ ++ (p, v) :: l₂ from hl]
  simp

/-- A claim that does not repeat a qualifier property: the lookup is then exactly
membership in the qualifier list. -/
theorem qualValue_eq_some_iff_of_nodup {c : Claim} {p : Pid} {v : Value}
    (h : c.qualPids.Nodup) : c.qualValue p = some v ↔ (p, v) ∈ c.quals := by
  refine ⟨qualValue_eq_some_mem, fun hv => ?_⟩
  exact List.lookup_eq_some_of_nodup_keys c.quals p v h hv

/-- A property occurring among the qualifiers of a claim does have a value there. -/
theorem qualValue_isSome_of_mem {c : Claim} {p : Pid} (h : p ∈ c.qualPids) :
    (c.qualValue p).isSome := by
  obtain ⟨v, hv⟩ := mem_qualPids.1 h
  exact List.lookup_isSome_of_mem c.quals p v hv

end Claim

/-! ### Allowed and mandatory qualifiers -/

/-- The qualifier profile of one property: the qualifiers it allows
(*allowed qualifiers*, Q21510851) and the ones it requires
(*mandatory qualifiers*, Q21510856). -/
structure QualSpec where
  /-- The property the profile is about. -/
  pid : Pid
  /-- The properties permitted as qualifiers. -/
  allowed : List Pid := []
  /-- The properties required as qualifiers. -/
  mandatory : List Pid := []
deriving DecidableEq, Repr, Inhabited

namespace QualSpec

variable (s : QualSpec) (c : Claim)

/-- The executable *allowed qualifiers* check for one claim. -/
def allowedOk : Bool := c.qualPids.all fun p => decide (p ∈ s.allowed)

/-- The executable *mandatory qualifiers* check for one claim. -/
def mandatoryOk : Bool := s.mandatory.all fun p => decide (p ∈ c.qualPids)

/-- Both qualifier constraints of a property, checked on one claim. -/
def claimOk : Bool := s.allowedOk c && s.mandatoryOk c

variable {s c}

theorem allowedOk_iff : s.allowedOk c = true ↔ ∀ p ∈ c.qualPids, p ∈ s.allowed := by
  simp [allowedOk]

theorem mandatoryOk_iff : s.mandatoryOk c = true ↔ ∀ p ∈ s.mandatory, p ∈ c.qualPids := by
  simp [mandatoryOk]

theorem claimOk_iff :
    s.claimOk c = true ↔
      (∀ p ∈ c.qualPids, p ∈ s.allowed) ∧ (∀ p ∈ s.mandatory, p ∈ c.qualPids) := by
  simp [claimOk, allowedOk_iff, mandatoryOk_iff]

/-- A property allowing no qualifier at all has unqualified statements only. -/
theorem quals_eq_nil_of_allowed_nil (hnil : s.allowed = []) (h : s.allowedOk c = true) :
    c.quals = [] := by
  rcases hq : c.quals with _ | ⟨a, t⟩
  · rfl
  · have : a.1 ∈ c.qualPids := by simp [Claim.qualPids, hq]
    exact absurd (hnil ▸ allowedOk_iff.1 h _ this) (by simp)

/-- A conforming claim witnesses that the mandatory qualifiers are allowed. -/
theorem mandatory_subset_allowed (h : s.claimOk c = true) :
    ∀ p ∈ s.mandatory, p ∈ s.allowed := by
  obtain ⟨ha, hm⟩ := claimOk_iff.1 h
  exact fun p hp => ha p (hm p hp)

/-- Hence a property requiring a qualifier it does not allow has **no** conforming
statement: the two constraints are then jointly unsatisfiable. -/
theorem not_claimOk_of_mandatory_not_allowed {p : Pid} (hm : p ∈ s.mandatory)
    (ha : p ∉ s.allowed) : s.claimOk c = false := by
  by_contra h
  exact ha (mandatory_subset_allowed (by simpa using h) p hm)

/-- A mandatory qualifier of a conforming claim can be read off it. -/
theorem qualValue_isSome_of_mandatory (h : s.mandatoryOk c = true) {p : Pid}
    (hp : p ∈ s.mandatory) : (c.qualValue p).isSome :=
  Claim.qualValue_isSome_of_mem (mandatoryOk_iff.1 h p hp)

/-- Enlarging the list of allowed qualifiers preserves conformance. -/
theorem allowedOk_mono {s' : QualSpec} (hsub : ∀ p ∈ s.allowed, p ∈ s'.allowed)
    (h : s.allowedOk c = true) : s'.allowedOk c = true :=
  allowedOk_iff.2 fun p hp => hsub p (allowedOk_iff.1 h p hp)

/-- Shrinking the list of mandatory qualifiers preserves conformance. -/
theorem mandatoryOk_mono {s' : QualSpec} (hsub : ∀ p ∈ s'.mandatory, p ∈ s.mandatory)
    (h : s.mandatoryOk c = true) : s'.mandatoryOk c = true :=
  mandatoryOk_iff.2 fun p hp => mandatoryOk_iff.1 h p (hsub p hp)

end QualSpec

/-! ### Checking a whole claim set -/

/-- The qualifier profile of a property in a table of profiles, if it has one. -/
def specOf (t : List QualSpec) (p : Pid) : Option QualSpec := t.find? fun s => s.pid == p

theorem specOf_eq_some_pid {t : List QualSpec} {p : Pid} {s : QualSpec}
    (h : specOf t p = some s) : s.pid = p := by
  have := List.find?_some h
  simpa using this

theorem specOf_eq_none_iff {t : List QualSpec} {p : Pid} :
    specOf t p = none ↔ ∀ s ∈ t, s.pid ≠ p := by
  simp [specOf, List.find?_eq_none]

/-- The executable qualifier check for a whole claim set against a table of
profiles: a claim whose property has no profile is unconstrained. -/
def qualSetOk (t : List QualSpec) (cs : Claim.Set) : Bool :=
  cs.all fun c => match specOf t c.pid with
    | some s => s.claimOk c
    | none => true

theorem qualSetOk_iff {t : List QualSpec} {cs : Claim.Set} :
    qualSetOk t cs = true ↔
      ∀ c ∈ cs, ∀ s, specOf t c.pid = some s → s.claimOk c = true := by
  simp only [qualSetOk, List.all_eq_true]
  constructor
  · intro h c hc s hs
    have := h c hc
    rw [hs] at this
    exact this
  · intro h c hc
    rcases hs : specOf t c.pid with _ | s
    · rfl
    · exact h c hc s hs

/-- A claim whose property is absent from the table is never rejected. -/
theorem qualSetOk_of_not_mem_table {t : List QualSpec} {cs : Claim.Set}
    (h : ∀ c ∈ cs, ∀ s ∈ t, s.pid ≠ c.pid) : qualSetOk t cs = true :=
  qualSetOk_iff.2 fun c hc s hs =>
    absurd (specOf_eq_some_pid hs) (h c hc s (List.mem_of_find?_eq_some hs))

/-- Conformance is **downward closed**: deleting statements never creates a
qualifier defect. -/
theorem qualSetOk_sublist {t : List QualSpec} {cs ds : Claim.Set} (hsub : ds.Sublist cs)
    (h : qualSetOk t cs = true) : qualSetOk t ds = true :=
  qualSetOk_iff.2 fun c hc s hs => qualSetOk_iff.1 h c (hsub.mem hc) s hs

/-- In particular the truthy fragment of a conforming base conforms: restricting a
query to the best-ranked statements cannot introduce a qualifier defect. -/
theorem qualSetOk_truthy {t : List QualSpec} {cs : Claim.Set} (h : qualSetOk t cs = true) :
    qualSetOk t (Claim.truthy cs) = true :=
  qualSetOk_sublist (List.filter_sublist) h

/-! ### The property scope constraint -/

/-- The *property scope* constraint (Q53869507) of one property: in which slots it
may be used. -/
structure ScopeSpec where
  /-- The property the scope is about. -/
  pid : Pid
  /-- May the property be the main property of a statement? -/
  asMain : Bool := true
  /-- May the property be used as a qualifier? -/
  asQualifier : Bool := true
deriving DecidableEq, Repr, Inhabited

/-- The scope declared for a property, if any. -/
def scopeOf (t : List ScopeSpec) (p : Pid) : Option ScopeSpec := t.find? fun s => s.pid == p

/-- May the property be used as the main property of a statement?  A property with
no declared scope may be used anywhere. -/
def mainAllowed (t : List ScopeSpec) (p : Pid) : Bool :=
  match scopeOf t p with
  | some s => s.asMain
  | none => true

/-- May the property be used as a qualifier? -/
def qualifierAllowed (t : List ScopeSpec) (p : Pid) : Bool :=
  match scopeOf t p with
  | some s => s.asQualifier
  | none => true

/-- The executable scope check for a claim set. -/
def scopeOk (t : List ScopeSpec) (cs : Claim.Set) : Bool :=
  cs.all fun c => mainAllowed t c.pid && c.qualPids.all fun p => qualifierAllowed t p

theorem scopeOk_iff {t : List ScopeSpec} {cs : Claim.Set} :
    scopeOk t cs = true ↔
      ∀ c ∈ cs, mainAllowed t c.pid = true ∧
        ∀ p ∈ c.qualPids, qualifierAllowed t p = true := by
  simp [scopeOk]

/-- A property whose scope excludes the main slot carries no statements of its own. -/
theorem no_main_of_scope {t : List ScopeSpec} {cs : Claim.Set} {c : Claim}
    (h : scopeOk t cs = true) (hc : c ∈ cs) {s : ScopeSpec}
    (hs : scopeOf t c.pid = some s) : s.asMain = true := by
  have := (scopeOk_iff.1 h c hc).1
  rwa [mainAllowed, hs] at this

/-- A property whose scope excludes the qualifier slot appears in no qualifier list. -/
theorem not_qual_of_scope {t : List ScopeSpec} {cs : Claim.Set} {c : Claim} {p : Pid}
    (h : scopeOk t cs = true) (hc : c ∈ cs) (hp : p ∈ c.qualPids) {s : ScopeSpec}
    (hs : scopeOf t p = some s) : s.asQualifier = true := by
  have := (scopeOk_iff.1 h c hc).2 p hp
  rwa [qualifierAllowed, hs] at this

/-- The scope check, too, is downward closed. -/
theorem scopeOk_sublist {t : List ScopeSpec} {cs ds : Claim.Set} (hsub : ds.Sublist cs)
    (h : scopeOk t cs = true) : scopeOk t ds = true :=
  scopeOk_iff.2 fun c hc => scopeOk_iff.1 h c (hsub.mem hc)

/-- Hence the truthy fragment of a base with correct scopes has correct scopes. -/
theorem scopeOk_truthy {t : List ScopeSpec} {cs : Claim.Set} (h : scopeOk t cs = true) :
    scopeOk t (Claim.truthy cs) = true :=
  scopeOk_sublist (List.filter_sublist) h

/-- A qualifier-only property (`asMain := false`) is the extreme case: a conforming
base has no statement whose main property is it. -/
theorem no_claim_of_qualifier_only {t : List ScopeSpec} {cs : Claim.Set} {p : Pid}
    {s : ScopeSpec} (hs : scopeOf t p = some s) (hmain : s.asMain = false)
    (h : scopeOk t cs = true) : ∀ c ∈ cs, c.pid ≠ p := by
  intro c hc hEq
  have := no_main_of_scope h hc (hEq ▸ hs)
  simp [hmain] at this

/-! ### A worked fragment -/

namespace QualExample

open RankExample

/-- The qualifier profile of `population` (P1082): `point in time` (P585) is
mandatory, `determination method` (P459) and `reason for deprecated rank` (P2241)
are allowed as well. -/
def populationSpec : QualSpec :=
  { pid := P "P1082",
    allowed := [P "P585", P "P459", P "P2241"],
    mandatory := [P "P585"] }

/-- The table of qualifier profiles of the fragment. -/
def table : List QualSpec := [populationSpec]

/-- The Berlin fragment of `RequestProject.Ranks` is **rejected**: the deprecated
statement carries `reason for deprecated rank` but no `point in time`. -/
theorem berlin_qualSetOk_false : qualSetOk table berlin = false := by decide

/-- Its truthy fragment, on the other hand, conforms. -/
theorem berlin_truthy_qualSetOk : qualSetOk table (Claim.truthy berlin) = true := by decide

/-- `point in time` (P585) may be used as a qualifier only. -/
def scopeTable : List ScopeSpec :=
  [{ pid := P "P585", asMain := false, asQualifier := true }]

theorem berlin_scopeOk : scopeOk scopeTable berlin = true := by decide

/-- Using `point in time` as the main property of a statement is rejected. -/
theorem berlin_bad_scope :
    scopeOk scopeTable
        ({ subject := Q "Q64", pid := P "P585", value := .time 1237 } :: berlin) = false := by
  decide

/-- A statement of a property with no profile is unconstrained: the `country`
statement passes although it carries no qualifiers at all. -/
theorem country_unconstrained :
    qualSetOk table [{ subject := Q "Q64", pid := P "P17", value := .item (Q "Q183") }] = true := by
  decide

/-- Removing the deprecated statement is enough to repair the base. -/
theorem berlin_repaired :
    qualSetOk table (berlin.filter fun c => c.rank != Rank.deprecated) = true := by decide

end QualExample

end Wikidata
