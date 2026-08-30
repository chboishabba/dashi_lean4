import Mathlib

/-!
# Key tables and partial bijections

Several layers of the Wikidata data model have exactly the same shape: a table of
triples ⟨subject, key, value⟩ subject to two conditions,

* **functionality** — a subject has at most one value per key, and
* **injectivity** — a value belongs to at most one subject per key,

which together make the table a *partial bijection*, for each key, between
subjects and values.  Sitelinks (subject = item, key = site, value = page title)
and external identifiers (subject = item, key = identifier property, value =
identifier string) are two instances, the first being Wikidata's one-page-per-site
rule and the second the combination of the single-value (Q19474404) and
distinct-values (Q21502410) constraints.

This file develops the notion once.  The two lookups `value?` and `subject?` are
proved to be mutually inverse under the two conditions, subjects and values
determine each other, and two tables sharing a key induce a *matching* — the
partial map sending a subject of the first to the subject of the second carrying
the same value — which is proved to be a partial bijection again, symmetric, and
transitive along a third table.  That last part is what authority control does:
two databases are linked through the identifiers they share.
-/

namespace Wikidata

/-- A table of triples ⟨subject, key, value⟩. -/
structure KeyTable (S K V : Type*) where
  /-- The rows of the table. -/
  rows : List (S × K × V) := []
deriving DecidableEq, Repr, Inhabited

namespace KeyTable

variable {S K V W : Type*} [DecidableEq S] [DecidableEq K] [DecidableEq V]

variable (T : KeyTable S K V)

/-- The value of a subject under a key, if any. -/
def value? (s : S) (k : K) : Option V :=
  (T.rows.find? (fun r => r.1 == s && r.2.1 == k)).map (fun r => r.2.2)

/-- The subject carrying a value under a key, if any. -/
def subject? (k : K) (v : V) : Option S :=
  (T.rows.find? (fun r => r.2.1 == k && r.2.2 == v)).map Prod.fst

/-- Each subject has at most one value per key. -/
def Functional : Prop := ∀ s k v v', (s, k, v) ∈ T.rows → (s, k, v') ∈ T.rows → v = v'

/-- Each value belongs to at most one subject per key. -/
def Injective : Prop := ∀ k v s s', (s, k, v) ∈ T.rows → (s', k, v) ∈ T.rows → s = s'

/-- The executable check for `Functional`. -/
def functionalB : Bool :=
  T.rows.all (fun r => T.rows.all (fun r' =>
    !(r.1 == r'.1 && r.2.1 == r'.2.1) || r.2.2 == r'.2.2))

/-- The executable check for `Injective`. -/
def injectiveB : Bool :=
  T.rows.all (fun r => T.rows.all (fun r' =>
    !(r.2.1 == r'.2.1 && r.2.2 == r'.2.2) || r.1 == r'.1))

variable {T}

theorem functionalB_iff : T.functionalB = true ↔ T.Functional := by
  simp only [functionalB, Functional, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, beq_iff_eq, beq_eq_false_iff_ne, ne_eq]
  constructor
  · intro h s k v v' hv hv'
    rcases h _ hv _ hv' with h₁ | h₁
    · rcases h₁ with h₁ | h₁ <;> simp at h₁
    · simpa using h₁
  · intro h r hr r' hr'
    by_cases hs : r.1 = r'.1
    · by_cases hk : r.2.1 = r'.2.1
      · refine Or.inr ?_
        have h1 : (r.1, r.2.1, r.2.2) ∈ T.rows := by simpa using hr
        have h2 : (r.1, r.2.1, r'.2.2) ∈ T.rows := by simpa [hs, hk] using hr'
        exact h _ _ _ _ h1 h2
      · exact Or.inl (Or.inr hk)
    · exact Or.inl (Or.inl hs)

theorem injectiveB_iff : T.injectiveB = true ↔ T.Injective := by
  simp only [injectiveB, Injective, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, beq_iff_eq, beq_eq_false_iff_ne, ne_eq]
  constructor
  · intro h k v s s' hs hs'
    rcases h _ hs _ hs' with h₁ | h₁
    · rcases h₁ with h₁ | h₁ <;> simp at h₁
    · simpa using h₁
  · intro h r hr r' hr'
    by_cases hk : r.2.1 = r'.2.1
    · by_cases hv : r.2.2 = r'.2.2
      · refine Or.inr ?_
        have h1 : (r.1, r.2.1, r.2.2) ∈ T.rows := by simpa using hr
        have h2 : (r'.1, r.2.1, r.2.2) ∈ T.rows := by simpa [hk, hv] using hr'
        exact h _ _ _ _ h1 h2
      · exact Or.inl (Or.inr hv)
    · exact Or.inl (Or.inl hk)

/-! ### The two lookups -/

omit [DecidableEq V] in
theorem value?_eq_some_iff (hf : T.Functional) {s : S} {k : K} {v : V} :
    T.value? s k = some v ↔ (s, k, v) ∈ T.rows := by
  constructor
  · intro h
    simp only [value?, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, hv⟩ := h
    have hmem := List.mem_of_find?_eq_some hr
    have hcond := (List.find?_eq_some_iff_getElem.1 hr).1
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    obtain ⟨h1, h2⟩ := hcond
    have : r = (s, k, v) := by
      obtain ⟨a, b, c⟩ := r; simp_all
    exact this ▸ hmem
  · intro h
    have hne : T.rows.find? (fun r => r.1 == s && r.2.1 == k) ≠ none := by
      intro hnone
      have := List.find?_eq_none.1 hnone _ h
      simp at this
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hne
    have hmem := List.mem_of_find?_eq_some hr
    have hcond := (List.find?_eq_some_iff_getElem.1 hr).1
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    obtain ⟨h1, h2⟩ := hcond
    have hmem' : (s, k, r.2.2) ∈ T.rows := by
      obtain ⟨a, b, c⟩ := r; simp_all
    have : r.2.2 = v := hf _ _ _ _ hmem' h
    simp [value?, hr, this]

omit [DecidableEq S] in
theorem subject?_eq_some_iff (hi : T.Injective) {s : S} {k : K} {v : V} :
    T.subject? k v = some s ↔ (s, k, v) ∈ T.rows := by
  constructor
  · intro h
    simp only [subject?, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, hs⟩ := h
    have hmem := List.mem_of_find?_eq_some hr
    have hcond := (List.find?_eq_some_iff_getElem.1 hr).1
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    obtain ⟨h1, h2⟩ := hcond
    have : r = (s, k, v) := by
      obtain ⟨a, b, c⟩ := r; simp_all
    exact this ▸ hmem
  · intro h
    have hne : T.rows.find? (fun r => r.2.1 == k && r.2.2 == v) ≠ none := by
      intro hnone
      have := List.find?_eq_none.1 hnone _ h
      simp at this
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hne
    have hmem := List.mem_of_find?_eq_some hr
    have hcond := (List.find?_eq_some_iff_getElem.1 hr).1
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    obtain ⟨h1, h2⟩ := hcond
    have hmem' : (r.1, k, v) ∈ T.rows := by
      obtain ⟨a, b, c⟩ := r; simp_all
    have : r.1 = s := hi _ _ _ _ hmem' h
    simp [subject?, hr, this]

/-- **A functional and injective table is a partial bijection**: the lookup from
subjects to values and the lookup from values to subjects are mutually inverse. -/
theorem value?_eq_some_iff_subject?_eq_some (hf : T.Functional) (hi : T.Injective)
    {s : S} {k : K} {v : V} : T.value? s k = some v ↔ T.subject? k v = some s := by
  rw [value?_eq_some_iff hf, subject?_eq_some_iff hi]

omit [DecidableEq V] in
/-- Under injectivity, the value identifies the subject. -/
theorem eq_of_value?_eq (hf : T.Functional) (hi : T.Injective) {s s' : S} {k : K} {v : V}
    (h : T.value? s k = some v) (h' : T.value? s' k = some v) : s = s' := by
  rw [value?_eq_some_iff hf] at h h'
  exact hi _ _ _ _ h h'

omit [DecidableEq S] in
/-- Under functionality, the subject identifies the value. -/
theorem eq_of_subject?_eq (hf : T.Functional) (hi : T.Injective) {s : S} {k : K} {v v' : V}
    (h : T.subject? k v = some s) (h' : T.subject? k v' = some s) : v = v' := by
  rw [subject?_eq_some_iff hi] at h h'
  exact hf _ _ _ _ h h'

/-! ### Matching two tables through a shared key -/

variable [DecidableEq W]

/-- The matching of two tables through a key: a subject of the first is matched to
the subject of the second carrying the same value. -/
def matchWith (T : KeyTable S K V) (U : KeyTable W K V) (k : K) (s : S) : Option W :=
  (T.value? s k).bind (U.subject? k)

omit [DecidableEq W] in
theorem matchWith_eq_some_iff {T : KeyTable S K V} {U : KeyTable W K V} (hf : T.Functional)
    (hi : U.Injective) {k : K} {s : S} {w : W} :
    T.matchWith U k s = some w ↔ ∃ v, (s, k, v) ∈ T.rows ∧ (w, k, v) ∈ U.rows := by
  simp only [matchWith, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨v, hv, hw⟩
    exact ⟨v, (value?_eq_some_iff hf).1 hv, (subject?_eq_some_iff hi).1 hw⟩
  · rintro ⟨v, hv, hw⟩
    exact ⟨v, (value?_eq_some_iff hf).2 hv, (subject?_eq_some_iff hi).2 hw⟩

/-- **The matching is symmetric**: if the first table matches `s` to `w`, the
second matches `w` back to `s`. -/
theorem matchWith_symm {T : KeyTable S K V} {U : KeyTable W K V} (hfT : T.Functional)
    (hiT : T.Injective) (hfU : U.Functional) (hiU : U.Injective) {k : K} {s : S} {w : W}
    (h : T.matchWith U k s = some w) : U.matchWith T k w = some s := by
  obtain ⟨v, hv, hw⟩ := (matchWith_eq_some_iff hfT hiU).1 h
  exact (matchWith_eq_some_iff hfU hiT).2 ⟨v, hw, hv⟩

omit [DecidableEq W] in
/-- **The matching is injective**: two subjects matched to the same one agree. -/
theorem matchWith_inj {T : KeyTable S K V} {U : KeyTable W K V} (hf : T.Functional)
    (hiT : T.Injective) (hfU : U.Functional) (hiU : U.Injective) {k : K} {s s' : S} {w : W}
    (h : T.matchWith U k s = some w) (h' : T.matchWith U k s' = some w) : s = s' := by
  obtain ⟨v, hv, hw⟩ := (matchWith_eq_some_iff hf hiU).1 h
  obtain ⟨v', hv', hw'⟩ := (matchWith_eq_some_iff hf hiU).1 h'
  have : v = v' := hfU _ _ _ _ hw hw'
  subst this
  exact hiT _ _ _ _ hv hv'

/-- **The matching is transitive**: matchings through a common key compose, so a
chain of authority-control links relates the two ends. -/
theorem matchWith_trans {X : Type*} [DecidableEq X] {T : KeyTable S K V} {U : KeyTable W K V}
    {R : KeyTable X K V} (hfT : T.Functional) (hfU : U.Functional) (hiU : U.Injective)
    (hiR : R.Injective) {k : K} {s : S} {w : W} {x : X}
    (h : T.matchWith U k s = some w) (h' : U.matchWith R k w = some x) :
    T.matchWith R k s = some x := by
  obtain ⟨v, hv, hw⟩ := (matchWith_eq_some_iff hfT hiU).1 h
  obtain ⟨v', hw', hx⟩ := (matchWith_eq_some_iff hfU hiR).1 h'
  have : v = v' := hfU _ _ _ _ hw hw'
  subst this
  exact (matchWith_eq_some_iff hfT hiR).2 ⟨v, hv, hx⟩

end KeyTable

end Wikidata
