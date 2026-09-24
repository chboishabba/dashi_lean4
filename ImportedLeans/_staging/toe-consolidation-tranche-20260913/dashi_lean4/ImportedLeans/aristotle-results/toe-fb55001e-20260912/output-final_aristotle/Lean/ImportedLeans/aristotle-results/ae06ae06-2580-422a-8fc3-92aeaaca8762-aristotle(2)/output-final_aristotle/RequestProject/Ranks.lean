import RequestProject.PropertyEngine

/-!
# Statement ranks and qualifiers: the *truthy* fragment of Wikidata

The Wikidata data model does not simply record statements: every statement carries a
**rank** — `preferred`, `normal` or `deprecated` — and a list of **qualifiers**.  The
rank is what lets an item carry several competing values for the same property (the
population of a city at different census dates, say) while still exposing a single
"current" answer.  The *truthy* statements — the ones exported to the RDF
`wdt:` predicates and the ones a query returns by default — are, for each
subject–property pair:

* the `preferred` statements, if there are any;
* otherwise all the `normal` statements;
* never a `deprecated` statement.

This file formalises exactly that rule and certifies the executable queries built on
it.  `Claim` is a statement with a rank and qualifiers, `bestRankNat` computes the
best rank present for a subject–property pair, `isTruthy` decides truthiness and
`truthyValues` is the default-visible list of values.

The main results are:

* `Wikidata.Claim.truthy_sublist` and `Wikidata.Claim.mem_truthyValues_iff` —
  the executable query returns exactly the truthy values;
* `Wikidata.Claim.not_isTruthy_deprecated` — a deprecated statement is never truthy;
* `Wikidata.Claim.exists_isTruthy` — as soon as one non-deprecated statement is
  present, something is truthy: ranks never hide all the data;
* `Wikidata.Claim.isTruthy_iff_preferred` and
  `Wikidata.Claim.isTruthy_iff_normal_of_no_preferred` — the two clauses of the rule;
* `Wikidata.Claim.isTruthy_congr` — truthiness does not depend on the qualifiers or on
  the value, only on subject, property and rank;
* `Wikidata.Claim.truthyValues_append_deprecated` — adding a deprecated statement
  changes nothing that is visible, whereas `truthyValues_append_preferred` shows that
  adding a preferred one hides every previously visible value;
* `Wikidata.Claim.truthyItemStmts` feeds the truthy item-valued statements into the
  property engine of `RequestProject.PropertyEngine`, so the whole ontology layer
  applies to the truthy fragment (`Wikidata.Claim.holds_of_mem_truthyItemStmts`).

As elsewhere in this development the identifiers follow Wikidata, but the example
fragment at the end is a stylised excerpt; the theorems about it are statements about
that fragment.
-/

namespace Wikidata

/-- The rank of a Wikidata statement. -/
inductive Rank where
  /-- A statement known to be wrong (or superseded); never truthy. -/
  | deprecated
  /-- The default rank. -/
  | normal
  /-- A statement singled out as the best value for its subject and property. -/
  | preferred
deriving DecidableEq, Repr, Inhabited

/-- Ranks as numbers, so that they can be compared: `deprecated < normal < preferred`. -/
def Rank.toNat : Rank → Nat
  | .deprecated => 0
  | .normal => 1
  | .preferred => 2

@[simp] theorem Rank.toNat_deprecated : Rank.deprecated.toNat = 0 := rfl
@[simp] theorem Rank.toNat_normal : Rank.normal.toNat = 1 := rfl
@[simp] theorem Rank.toNat_preferred : Rank.preferred.toNat = 2 := rfl

theorem Rank.toNat_injective : Function.Injective Rank.toNat := by
  intro a b h; cases a <;> cases b <;> simp_all [Rank.toNat]

theorem Rank.eq_of_toNat_eq {a b : Rank} (h : a.toNat = b.toNat) : a = b :=
  Rank.toNat_injective h

theorem Rank.toNat_le_two (r : Rank) : r.toNat ≤ 2 := by cases r <;> decide

theorem Rank.toNat_le_one {r : Rank} (h : r ≠ .preferred) : r.toNat ≤ 1 := by
  cases r
  · decide
  · decide
  · exact absurd rfl h

theorem Rank.toNat_pos {r : Rank} (h : r ≠ .deprecated) : 0 < r.toNat := by
  cases r
  · exact absurd rfl h
  · decide
  · decide

/-- The value of a Wikidata statement: another item, a quantity, a point in time
(recorded by its year) or a string. -/
inductive Value where
  /-- An item value, e.g. `spouse → Q76`. -/
  | item (q : Qid)
  /-- A quantity value, e.g. a population count. -/
  | quantity (n : Int)
  /-- A time value, recorded by its year. -/
  | time (year : Int)
  /-- A string value. -/
  | str (s : String)
deriving DecidableEq, Repr, Inhabited

/-- A Wikidata claim: a statement `⟨subject, property, value⟩` together with its rank
and its qualifiers (themselves property–value pairs). -/
structure Claim where
  /-- The subject item of the statement. -/
  subject : Qid
  /-- The property of the statement. -/
  pid : Pid
  /-- The value of the statement. -/
  value : Value
  /-- The rank of the statement; `normal` unless specified. -/
  rank : Rank := .normal
  /-- The qualifiers of the statement, e.g. `point in time` (P585). -/
  quals : List (Pid × Value) := []
deriving DecidableEq, Repr, Inhabited

namespace Claim

/-- A claim set: the statements of a fragment of Wikidata. -/
abbrev Set := List Claim

/-! ### Maxima of lists of numbers

Two small facts about `List.foldr max 0`, used to compute the best rank present. -/

/-- Every member of a list is at most its maximum. -/
theorem le_foldr_max {l : List Nat} {x : Nat} (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => cases hx
  | cons a t ih =>
      rcases List.mem_cons.1 hx with h | h
      · subst h; exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)

/-- The maximum of a concatenation is the maximum of the maxima. -/
theorem foldr_max_append (l m : List Nat) :
    (l ++ m).foldr max 0 = max (l.foldr max 0) (m.foldr max 0) := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.foldr_cons, ih, max_assoc]

/-- The maximum of a list is either `0` or one of its members. -/
theorem foldr_max_eq_zero_or_mem (l : List Nat) :
    l.foldr max 0 = 0 ∨ l.foldr max 0 ∈ l := by
  induction l with
  | nil => exact Or.inl rfl
  | cons a t ih =>
      by_cases h : a ≤ t.foldr max 0
      · have : (a :: t).foldr max 0 = t.foldr max 0 := by
          simp [List.foldr_cons, max_eq_right h]
        rcases ih with h0 | hm
        · exact Or.inl (by rw [this, h0])
        · exact Or.inr (by rw [this]; exact List.mem_cons_of_mem _ hm)
      · have : (a :: t).foldr max 0 = a := by
          simp [List.foldr_cons, max_eq_left (le_of_not_ge h)]
        exact Or.inr (by rw [this]; exact List.mem_cons_self)

/-! ### Groups, best rank and truthiness -/

/-- The claims of a claim set with a given subject and property. -/
def group (cs : Set) (s : Qid) (p : Pid) : Set :=
  cs.filter (fun c => c.subject = s ∧ c.pid = p)

@[simp] theorem mem_group_iff {cs : Set} {s : Qid} {p : Pid} {c : Claim} :
    c ∈ group cs s p ↔ c ∈ cs ∧ c.subject = s ∧ c.pid = p := by
  simp [group]

/-- The best rank present for a subject–property pair, as a number (`0` if there are
no statements at all). -/
def bestRankNat (cs : Set) (s : Qid) (p : Pid) : Nat :=
  ((group cs s p).map (fun c => c.rank.toNat)).foldr max 0

/-- No statement has a rank above the best rank of its group. -/
theorem rank_le_bestRankNat {cs : Set} {c : Claim} (hc : c ∈ cs) :
    c.rank.toNat ≤ bestRankNat cs c.subject c.pid :=
  le_foldr_max (List.mem_map_of_mem (by simp [hc]))

/-- The best rank of a nonempty group is attained by a statement of the group. -/
theorem exists_rank_eq_bestRankNat {cs : Set} {s : Qid} {p : Pid}
    (hpos : 0 < bestRankNat cs s p) :
    ∃ d ∈ group cs s p, d.rank.toNat = bestRankNat cs s p := by
  rcases foldr_max_eq_zero_or_mem ((group cs s p).map (fun c => c.rank.toNat)) with h | h
  · exact absurd (show bestRankNat cs s p = 0 from h) (Nat.ne_of_gt hpos)
  · obtain ⟨d, hd, hdr⟩ := List.mem_map.1 h
    exact ⟨d, hd, hdr⟩

/-- Whether a claim is *truthy*: it is not deprecated and its rank is the best rank
present for its subject and property. -/
def isTruthy (cs : Set) (c : Claim) : Prop :=
  c.rank ≠ .deprecated ∧ c.rank.toNat = bestRankNat cs c.subject c.pid

instance (cs : Set) (c : Claim) : Decidable (isTruthy cs c) := by
  unfold isTruthy; infer_instance

/-- The truthy statements of a claim set. -/
def truthy (cs : Set) : Set := cs.filter (fun c => decide (isTruthy cs c))

/-- The values a query returns by default for a subject and a property. -/
def truthyValues (cs : Set) (s : Qid) (p : Pid) : List Value :=
  ((group cs s p).filter (fun c => decide (isTruthy cs c))).map (·.value)

@[simp] theorem mem_truthy_iff {cs : Set} {c : Claim} :
    c ∈ truthy cs ↔ c ∈ cs ∧ isTruthy cs c := by
  simp [truthy]

/-- Truthy statements are statements. -/
theorem truthy_sublist (cs : Set) : ∀ c ∈ truthy cs, c ∈ cs := by
  intro c hc; exact (mem_truthy_iff.1 hc).1

/-- A deprecated statement is never truthy. -/
theorem not_isTruthy_deprecated {cs : Set} {c : Claim} (h : c.rank = .deprecated) :
    ¬ isTruthy cs c := fun ht => ht.1 h

/-- The executable query returns exactly the truthy values. -/
theorem mem_truthyValues_iff {cs : Set} {s : Qid} {p : Pid} {v : Value} :
    v ∈ truthyValues cs s p ↔
      ∃ c ∈ cs, c.subject = s ∧ c.pid = p ∧ isTruthy cs c ∧ c.value = v := by
  constructor
  · intro h
    obtain ⟨c, hc, hv⟩ := List.mem_map.1 h
    obtain ⟨hcg, ht⟩ := List.mem_filter.1 hc
    obtain ⟨hcs, hs, hp⟩ := mem_group_iff.1 hcg
    exact ⟨c, hcs, hs, hp, of_decide_eq_true ht, hv⟩
  · rintro ⟨c, hcs, hs, hp, ht, hv⟩
    refine List.mem_map.2 ⟨c, List.mem_filter.2 ⟨mem_group_iff.2 ⟨hcs, hs, hp⟩, ?_⟩, hv⟩
    exact decide_eq_true ht

/-! ### The two clauses of the rank rule -/

/-- Ranks never hide all the data: if some statement for a subject–property pair is
not deprecated, then some statement for that pair is truthy. -/
theorem exists_isTruthy {cs : Set} {s : Qid} {p : Pid} {c : Claim}
    (hc : c ∈ group cs s p) (hr : c.rank ≠ .deprecated) :
    ∃ d ∈ group cs s p, isTruthy cs d := by
  have hpos : 0 < bestRankNat cs s p := by
    have h1 : c.rank.toNat ≤ bestRankNat cs c.subject c.pid :=
      rank_le_bestRankNat (mem_group_iff.1 hc).1
    obtain ⟨-, hs, hp⟩ := mem_group_iff.1 hc
    rw [hs, hp] at h1
    have h0 : 0 < c.rank.toNat := Rank.toNat_pos hr
    omega
  obtain ⟨d, hd, hdr⟩ := exists_rank_eq_bestRankNat hpos
  obtain ⟨-, hs, hp⟩ := mem_group_iff.1 hd
  refine ⟨d, hd, ?_, ?_⟩
  · intro hdep
    rw [hdep] at hdr
    simp only [Rank.toNat_deprecated] at hdr
    omega
  · rw [hs, hp]; exact hdr

/-- Truthiness depends only on the subject, the property and the rank — not on the
value and not on the qualifiers. -/
theorem isTruthy_congr {cs : Set} {c d : Claim} (hs : c.subject = d.subject)
    (hp : c.pid = d.pid) (hr : c.rank = d.rank) : isTruthy cs c ↔ isTruthy cs d := by
  unfold isTruthy; rw [hs, hp, hr]

/-- **First clause of the rank rule.** If some statement for a subject–property pair
is preferred, the truthy statements for that pair are exactly the preferred ones. -/
theorem isTruthy_iff_preferred {cs : Set} {s : Qid} {p : Pid} {c d : Claim}
    (hd : d ∈ group cs s p) (hdr : d.rank = .preferred) (hc : c ∈ group cs s p) :
    isTruthy cs c ↔ c.rank = .preferred := by
  obtain ⟨hds, hdsub, hdpid⟩ := mem_group_iff.1 hd
  obtain ⟨hcs, hcsub, hcpid⟩ := mem_group_iff.1 hc
  have hbest : bestRankNat cs s p = 2 := by
    have hle : (2 : Nat) ≤ bestRankNat cs s p := by
      have := rank_le_bestRankNat hds
      rw [hdsub, hdpid, hdr] at this
      simpa using this
    have hge : bestRankNat cs s p ≤ 2 := by
      rcases foldr_max_eq_zero_or_mem ((group cs s p).map (fun c => c.rank.toNat)) with h | h
      · simp [bestRankNat, h]
      · obtain ⟨e, -, he⟩ := List.mem_map.1 h
        have h2 : e.rank.toNat ≤ 2 := Rank.toNat_le_two _
        rw [bestRankNat, ← he]; exact h2
    omega
  constructor
  · rintro ⟨-, h2⟩
    rw [hcsub, hcpid, hbest] at h2
    exact Rank.eq_of_toNat_eq (by simpa using h2)
  · intro h
    exact ⟨by rw [h]; exact fun h' => Rank.noConfusion h', by rw [hcsub, hcpid, hbest, h]; rfl⟩

/-- **Second clause of the rank rule.** If no statement for a subject–property pair is
preferred, the truthy statements for that pair are exactly the normal ones. -/
theorem isTruthy_iff_normal_of_no_preferred {cs : Set} {s : Qid} {p : Pid} {c : Claim}
    (hno : ∀ e ∈ group cs s p, e.rank ≠ .preferred) (hc : c ∈ group cs s p) :
    isTruthy cs c ↔ c.rank = .normal := by
  obtain ⟨hcs, hcsub, hcpid⟩ := mem_group_iff.1 hc
  have hle : bestRankNat cs s p ≤ 1 := by
    rcases foldr_max_eq_zero_or_mem ((group cs s p).map (fun c => c.rank.toNat)) with h | h
    · simp [bestRankNat, h]
    · obtain ⟨e, he, hev⟩ := List.mem_map.1 h
      have h1 : e.rank.toNat ≤ 1 := Rank.toNat_le_one (hno e he)
      rw [bestRankNat, ← hev]; exact h1
  constructor
  · rintro ⟨hne, h2⟩
    rw [hcsub, hcpid] at h2
    have : c.rank.toNat ≤ 1 := h2 ▸ hle
    cases hrk : c.rank with
    | deprecated => exact absurd hrk hne
    | normal => rfl
    | preferred => rw [hrk] at this; simp at this
  · intro h
    have hge : 1 ≤ bestRankNat cs s p := by
      have := rank_le_bestRankNat hcs
      rw [hcsub, hcpid, h] at this
      simpa using this
    exact ⟨by rw [h]; exact fun h' => Rank.noConfusion h',
      by rw [hcsub, hcpid, h]; simp; omega⟩

/-! ### Robustness of the truthy fragment -/

/-- The best rank is unchanged by adding a deprecated statement. -/
theorem bestRankNat_append_deprecated {cs : Set} {d : Claim} (hd : d.rank = .deprecated)
    (s : Qid) (p : Pid) : bestRankNat (cs ++ [d]) s p = bestRankNat cs s p := by
  have hgroup : group (cs ++ [d]) s p =
      group cs s p ++ (if d.subject = s ∧ d.pid = p then [d] else []) := by
    simp [group, List.filter_append]
    split <;> simp_all
  rw [bestRankNat, bestRankNat, hgroup]
  by_cases hmem : d.subject = s ∧ d.pid = p
  · simp only [hmem, List.map_append]
    rw [foldr_max_append]
    simp [hd]
  · simp [hmem]

/-- Adding a deprecated statement changes nothing that is visible by default. -/
theorem truthyValues_append_deprecated {cs : Set} {d : Claim} (hd : d.rank = .deprecated)
    (s : Qid) (p : Pid) : truthyValues (cs ++ [d]) s p = truthyValues cs s p := by
  have hbest : ∀ s' p', bestRankNat (cs ++ [d]) s' p' = bestRankNat cs s' p' :=
    fun s' p' => bestRankNat_append_deprecated hd s' p'
  have hT : ∀ c : Claim, isTruthy (cs ++ [d]) c ↔ isTruthy cs c := by
    intro c; unfold isTruthy; rw [hbest]
  have hgroup : group (cs ++ [d]) s p =
      group cs s p ++ (if d.subject = s ∧ d.pid = p then [d] else []) := by
    simp [group, List.filter_append]
    split <;> simp_all
  unfold truthyValues
  rw [hgroup]
  have hfilter : ∀ l : Set, l.filter (fun c => decide (isTruthy (cs ++ [d]) c)) =
      l.filter (fun c => decide (isTruthy cs c)) := by
    intro l
    apply List.filter_congr
    intro c _
    simp [hT c]
  rw [List.filter_append, hfilter]
  by_cases hmem : d.subject = s ∧ d.pid = p
  · have : ¬ isTruthy (cs ++ [d]) d := not_isTruthy_deprecated hd
    simp [hmem, List.filter, this]
  · simp [hmem]

/-- Adding a preferred statement hides every previously visible value of the same
subject and property: the truthy values become exactly the preferred ones. -/
theorem truthyValues_append_preferred {cs : Set} {d : Claim} (hd : d.rank = .preferred)
    (hno : ∀ e ∈ group cs d.subject d.pid, e.rank ≠ .preferred) :
    ∀ v ∈ truthyValues (cs ++ [d]) d.subject d.pid, v = d.value := by
  intro v hv
  obtain ⟨c, hc, hcs, hcp, ht, hcv⟩ := mem_truthyValues_iff.1 hv
  have hdmem : d ∈ group (cs ++ [d]) d.subject d.pid := by
    simp [mem_group_iff]
  have hcmem : c ∈ group (cs ++ [d]) d.subject d.pid := mem_group_iff.2 ⟨hc, hcs, hcp⟩
  have hpref : c.rank = .preferred := (isTruthy_iff_preferred hdmem hd hcmem).1 ht
  -- a preferred claim of this group must be `d` itself, since `cs` has none
  rcases List.mem_append.1 hc with h | h
  · exact absurd hpref (hno c (mem_group_iff.2 ⟨h, hcs, hcp⟩))
  · have : c = d := by simpa using h
    rw [← hcv, this]

/-! ### Feeding the truthy fragment into the property engine -/

/-- The truthy statements with item values, in the format of `Wikidata.PKB.stmts`. -/
def truthyItemStmts (cs : Set) : List (Pid × Qid × Qid) :=
  (truthy cs).filterMap fun c =>
    match c.value with
    | .item q => some (c.pid, c.subject, q)
    | _ => none

theorem mem_truthyItemStmts_iff {cs : Set} {p : Pid} {s o : Qid} :
    (p, s, o) ∈ truthyItemStmts cs ↔
      ∃ c ∈ cs, isTruthy cs c ∧ c.pid = p ∧ c.subject = s ∧ c.value = .item o := by
  constructor
  · intro h
    obtain ⟨c, hc, hval⟩ := List.mem_filterMap.1 h
    obtain ⟨hcs, ht⟩ := mem_truthy_iff.1 hc
    revert hval
    cases hv : c.value with
    | item q => intro hval; simp at hval; exact ⟨c, hcs, ht, hval.1, hval.2.1, by rw [hv, hval.2.2]⟩
    | quantity n => intro hval; simp at hval
    | time y => intro hval; simp at hval
    | str t => intro hval; simp at hval
  · rintro ⟨c, hcs, ht, hp, hs, hv⟩
    exact List.mem_filterMap.2 ⟨c, mem_truthy_iff.2 ⟨hcs, ht⟩, by rw [hv]; simp [hp, hs]⟩

/-- A deprecated statement never reaches the property engine: it contributes no
entry of its own to the truthy fragment.  (Another, non-deprecated, statement may of
course assert the same triple; what the rank rule guarantees is that a deprecated
statement is never a reason for a triple to be exported.) -/
theorem not_mem_truthy_of_deprecated {cs : Set} {c : Claim} (hd : c.rank = .deprecated) :
    c ∉ truthy cs := fun h => not_isTruthy_deprecated hd (mem_truthy_iff.1 h).2

/-- Every truthy item-valued statement is derivable in the property layer of a
knowledge base whose statements are the truthy ones. -/
theorem holds_of_mem_truthyItemStmts (K : PKB) (cs : Set)
    (hK : K.stmts = truthyItemStmts cs) {p : Pid} {s o : Qid}
    (h : (p, s, o) ∈ truthyItemStmts cs) : K.toLayer.Holds p s o := by
  refine PropertyLayer.Holds.stmt ?_
  simpa [PKB.toLayer, hK] using h

end Claim

/-! ### A worked fragment

The textbook use of ranks: an item with several values for the same property, one of
them singled out as `preferred`, one superseded but still `normal`, and one
`deprecated` because it is wrong. -/

namespace RankExample

/-- Abbreviation for a Wikidata item. -/
def Q (s : String) : Qid := .wd s

/-- Abbreviation for a Wikidata property. -/
def P (s : String) : Pid := .wd s

/-- Berlin (Q64): three `population` (P1082) statements of different ranks, each
qualified by a `point in time` (P585), together with two item-valued statements
(`country`, P17, and `capital of`, P1376). -/
def berlin : Claim.Set :=
  [ { subject := Q "Q64", pid := P "P1082", value := .quantity 3644826, rank := .preferred,
      quals := [(P "P585", .time 2018)] },
    { subject := Q "Q64", pid := P "P1082", value := .quantity 3292365, rank := .normal,
      quals := [(P "P585", .time 2011)] },
    { subject := Q "Q64", pid := P "P1082", value := .quantity 100, rank := .deprecated,
      quals := [(P "P2241", .item (Q "Q1193907"))] },
    { subject := Q "Q64", pid := P "P17", value := .item (Q "Q183") },
    { subject := Q "Q64", pid := P "P1376", value := .item (Q "Q183") } ]

/-- A default query for the population of Berlin returns the preferred value only. -/
theorem berlin_population_truthy :
    Claim.truthyValues berlin (Q "Q64") (P "P1082") = [.quantity 3644826] := by decide

/-- The single normal statement about the country is truthy. -/
theorem berlin_country_truthy :
    Claim.truthyValues berlin (Q "Q64") (P "P17") = [.item (Q "Q183")] := by decide

/-- Only the two item-valued truthy statements are exported to the property engine;
the deprecated population statement contributes nothing. -/
theorem berlin_truthyItemStmts :
    Claim.truthyItemStmts berlin =
      [(P "P17", Q "Q64", Q "Q183"), (P "P1376", Q "Q64", Q "Q183")] := by decide

/-- The same fragment with the preferred statement demoted to `normal`: now *both*
non-deprecated population values are visible -- and the deprecated one still is not. -/
def berlinNoPreferred : Claim.Set :=
  berlin.map fun c => if c.rank = .preferred then { c with rank := .normal } else c

theorem berlinNoPreferred_population_truthy :
    Claim.truthyValues berlinNoPreferred (Q "Q64") (P "P1082") =
      [.quantity 3644826, .quantity 3292365] := by decide

/-- Dropping the deprecated statement altogether changes nothing that is visible. -/
theorem berlin_drop_deprecated :
    Claim.truthyValues (berlin.filter fun c => c.rank != Rank.deprecated) (Q "Q64") (P "P1082") =
      Claim.truthyValues berlin (Q "Q64") (P "P1082") := by decide

/-- A property with no statements at all has nothing truthy. -/
theorem berlin_no_statements :
    Claim.truthyValues berlin (Q "Q64") (P "P571") = [] := by decide

end RankExample

end Wikidata
