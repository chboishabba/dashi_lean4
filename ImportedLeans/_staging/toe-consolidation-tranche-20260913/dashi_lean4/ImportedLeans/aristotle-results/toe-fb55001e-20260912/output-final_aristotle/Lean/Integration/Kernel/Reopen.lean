import Integration.Kernel.Authority

/-!
# Edge-indexed selective reopening, and the provenance of a coordinate

Fifth component of the shared kernel.  Once a discovery is merged, which
already-closed certificates have to be re-derived?

## §1 Reopening

A `DepGraph` records, for each certificate, the set of derivation *edges* it
used.  Revising a set of edges reopens exactly the certificates whose history
meets it:

```
e ∈ history c  ∧  e revised   ⇒   c reopened.
```

* `mem_reopened_iff`, `reopen_of_revised_edge`, `stays_closed_of_disjoint` — the
  rule and its contrapositive: a certificate whose history is disjoint from the
  revision stays closed.  Reopening is *selective*, not global
  (`reopening_is_selective` gives a graph where one revision reopens one
  certificate and leaves another closed).
* `reopened_mono`, `reopened_union`, `reopened_empty` — the reopened set is a
  monotone, union-preserving function of the revision, and nothing is reopened
  by revising nothing.
* `reopen_propagates` — if the graph is *inheriting* (a dependant's history
  contains its dependency's history) then reopening travels up the dependency
  relation, so the selective rule is still transitively sound.
* `closedAfter` and `closedAfter_subset`, `unaffected_stays_closed` — the
  bookkeeping the loop needs: the surviving closed set after a revision.

## §2 Introduced ≠ inherited

A coordinate carries a value and an `Origin` (`inherited` from upstream, or
`introduced` downstream).  `no_rule_recovers_origin` shows no function of the
value alone returns the origin, so **reintroducing a coordinate downstream is
not the same as restoring inherited lineage**, and a pipeline that only
transports values cannot certify lineage
(`value_agreement_is_not_lineage_agreement`).

**Claim boundary.** Certificates and edges are elements of arbitrary types; no
proof object, hash or repository is modelled.  What is proved is the algebra of
the reopening rule.
-/

namespace Integration.Kernel.Reopen

open Set

variable {C E V : Type*}

/-! ## §1 Reopening -/

/-- Each certificate's derivation history, as a set of edges. -/
structure DepGraph (C E : Type*) where
  /-- The edges the certificate's derivation used. -/
  history : C → Set E

/-- The certificates a revision reopens. -/
def reopened (G : DepGraph C E) (revised : Set E) : Set C :=
  {c | ∃ e ∈ revised, e ∈ G.history c}

theorem mem_reopened_iff {G : DepGraph C E} {revised : Set E} {c : C} :
    c ∈ reopened G revised ↔ ∃ e ∈ revised, e ∈ G.history c := Iff.rfl

theorem reopen_of_revised_edge {G : DepGraph C E} {revised : Set E} {c : C} {e : E}
    (he : e ∈ revised) (hc : e ∈ G.history c) : c ∈ reopened G revised := ⟨e, he, hc⟩

theorem stays_closed_of_disjoint {G : DepGraph C E} {revised : Set E} {c : C}
    (h : Disjoint (G.history c) revised) : c ∉ reopened G revised := by
  rintro ⟨e, he, hc⟩
  exact (h.le_bot ⟨hc, he⟩).elim

theorem reopened_mono {G : DepGraph C E} {r₁ r₂ : Set E} (h : r₁ ⊆ r₂) :
    reopened G r₁ ⊆ reopened G r₂ := fun _ ⟨e, he, hc⟩ => ⟨e, h he, hc⟩

theorem reopened_union (G : DepGraph C E) (r₁ r₂ : Set E) :
    reopened G (r₁ ∪ r₂) = reopened G r₁ ∪ reopened G r₂ := by
  ext c
  constructor
  · rintro ⟨e, he | he, hc⟩
    exacts [Or.inl ⟨e, he, hc⟩, Or.inr ⟨e, he, hc⟩]
  · rintro (⟨e, he, hc⟩ | ⟨e, he, hc⟩)
    exacts [⟨e, Or.inl he, hc⟩, ⟨e, Or.inr he, hc⟩]

@[simp] theorem reopened_empty (G : DepGraph C E) : reopened G (∅ : Set E) = ∅ := by
  ext c; simp [reopened]

/-- **Reopening is selective.**  One revision reopens the certificate that used
the revised edge and leaves the other closed. -/
theorem reopening_is_selective :
    ∃ (G : DepGraph Bool Bool) (revised : Set Bool),
      true ∈ reopened G revised ∧ false ∉ reopened G revised := by
  refine ⟨⟨fun c => {c}⟩, {true}, ⟨true, rfl, rfl⟩, ?_⟩
  rintro ⟨e, he, hc⟩
  rw [mem_singleton_iff] at he hc
  exact Bool.noConfusion (hc ▸ he)

/-- The graph is inheriting: a dependant's history contains its dependencies'. -/
def Inheriting (G : DepGraph C E) (dep : C → Set C) : Prop :=
  ∀ c c', c' ∈ dep c → G.history c' ⊆ G.history c

/-- In an inheriting graph, reopening travels up the dependency relation. -/
theorem reopen_propagates {G : DepGraph C E} {dep : C → Set C} {revised : Set E} {c c' : C}
    (hinh : Inheriting G dep) (hdep : c' ∈ dep c) (h : c' ∈ reopened G revised) :
    c ∈ reopened G revised := by
  obtain ⟨e, he, hc⟩ := h
  exact ⟨e, he, hinh c c' hdep hc⟩

/-- The certificates still closed after a revision. -/
def closedAfter (G : DepGraph C E) (closed : Set C) (revised : Set E) : Set C :=
  closed \ reopened G revised

theorem closedAfter_subset (G : DepGraph C E) (closed : Set C) (revised : Set E) :
    closedAfter G closed revised ⊆ closed := diff_subset

theorem unaffected_stays_closed {G : DepGraph C E} {closed : Set C} {revised : Set E} {c : C}
    (hc : c ∈ closed) (h : Disjoint (G.history c) revised) :
    c ∈ closedAfter G closed revised := ⟨hc, stays_closed_of_disjoint h⟩

@[simp] theorem closedAfter_empty_revision (G : DepGraph C E) (closed : Set C) :
    closedAfter G closed (∅ : Set E) = closed := by simp [closedAfter]

/-- Reopening more edges keeps fewer certificates closed. -/
theorem closedAfter_antitone {G : DepGraph C E} {closed : Set C} {r₁ r₂ : Set E} (h : r₁ ⊆ r₂) :
    closedAfter G closed r₂ ⊆ closedAfter G closed r₁ :=
  diff_subset_diff_right (reopened_mono h)

/-! ## §2 Introduced ≠ inherited -/

/-- Where a coordinate's content came from. -/
inductive Origin
  /-- Carried down from an upstream source. -/
  | inherited
  /-- Added downstream. -/
  | introduced
  deriving DecidableEq, Repr

/-- A coordinate: its value together with its provenance. -/
structure Coordinate (V : Type*) where
  /-- The transported content. -/
  value : V
  /-- Where the content came from. -/
  origin : Origin

/-- **Introduced downstream ≠ restored inherited lineage.**  No rule reading the
value alone returns the origin. -/
theorem no_rule_recovers_origin (v : V) :
    ¬ ∃ f : V → Origin, ∀ r : Coordinate V, f r.value = r.origin := by
  rintro ⟨f, hf⟩
  have h1 := hf ⟨v, Origin.inherited⟩
  have h2 := hf ⟨v, Origin.introduced⟩
  rw [h2] at h1
  exact Origin.noConfusion h1

/-- Two coordinates can agree on everything transported and still differ in
lineage. -/
theorem value_agreement_is_not_lineage_agreement (v : V) :
    ∃ r₁ r₂ : Coordinate V, r₁.value = r₂.value ∧ r₁.origin ≠ r₂.origin :=
  ⟨⟨v, Origin.inherited⟩, ⟨v, Origin.introduced⟩, rfl, by simp⟩

end Integration.Kernel.Reopen
