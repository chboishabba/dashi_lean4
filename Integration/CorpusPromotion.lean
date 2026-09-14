import Integration.RecordConstraintAdequacy

/-!
# The promotion ladder: from ingested source to a theorem the corpus owns

This round ingested a handoff archive: 2 427 Lean sources and 328 Agda modules
that were not already in the tree.  The archive is gone; the sources are in
`Lean/Imported` and `Agda/`.  That raises exactly the question this file
answers formally: **what does the presence of a file prove?**

The corpus's answer is a ladder of five rungs,

```
ingested  <  elaborates  <  wired  <  audited  <  cited
```

read as: the source is in the tree; it elaborates in *this* toolchain; it is a
module of a built library; its axiom profile has been printed and checked; a
canonical module depends on it.  The ladder is modelled here as a
downward-closed predicate on rungs, which is the only structural fact that is
true of it: reaching a rung says something about the rungs below and nothing
about the rungs above.

## What is proved

* `Stage` is a five-element linear order (`Stage.instLinearOrder`), and
  `Promotion` — a downward-closed set of reached rungs — gives
  `Promotion.reached_of_le`: reaching a rung implies every earlier rung.
* `reachedUpTo` exhibits, for each rung, a promotion that reaches exactly that
  far, so `no_upward_implication` holds: for every rung below the top there is a
  promotion satisfying it and failing the next.  The ladder is therefore strict,
  not a chain of definitional synonyms.
* `Promotion.notAdequate` states this as a contract audit in the sense of
  `Integration.RecordConstraintAdequacy`: "reached rung `s`" is **not** adequate
  for "reached rung `s+1`", with an explicit countermodel.
* `presence_does_not_determine_elaboration` — the load-bearing one.  A source is
  ingested together with the environment it is elaborated in; the store observes
  only the source text.  Two artefacts with the *same* source and different
  environments differ in whether they elaborate, so elaboration status does not
  factor through the store — an `Integration.FactorisationCollision.Collision`,
  hence inherited by every downstream reading of the store
  (`no_store_reading_gives_status`).
* `store_membership_is_a_ledger` — the corresponding positive statement, and its
  limit: "this content is in the store" is a pinned-value ledger, uniquely
  inhabited, so it separates nothing about the content.

Nothing here inspects real files: `Stage`, `Promotion` and the artefact model are
Lean definitions, and the theorems are about them.  They are the statement of the
policy, not evidence that the policy was followed.
-/

namespace Integration.CorpusPromotion

open Integration.FactorisationCollision
open Integration.RecordConstraintAdequacy

/-! ## The five rungs -/

/-- The rungs of the promotion ladder. -/
inductive Stage
  /-- The source is in the tree. -/
  | ingested
  /-- It elaborates in this toolchain. -/
  | elaborates
  /-- It is a module of a library the build produces. -/
  | wired
  /-- Its axiom profile has been printed and checked. -/
  | audited
  /-- A canonical module depends on it. -/
  | cited
  deriving DecidableEq, Repr

namespace Stage

/-- The rung's height, `0` for `ingested` through `4` for `cited`. -/
def height : Stage → Nat
  | ingested => 0
  | elaborates => 1
  | wired => 2
  | audited => 3
  | cited => 4

theorem height_injective : Function.Injective height := by
  intro a b h; cases a <;> cases b <;> simp_all [height]

/-- The rungs are ordered by height. -/
instance : LinearOrder Stage := LinearOrder.lift' height height_injective

/-- The next rung, where there is one. -/
def next : Stage → Option Stage
  | ingested => some elaborates
  | elaborates => some wired
  | wired => some audited
  | audited => some cited
  | cited => none

theorem lt_next {s t : Stage} (h : s.next = some t) : s < t := by
  cases s <;> simp [next] at h <;> subst h <;> decide

end Stage

/-! ## Promotions -/

/-- A **promotion state**: the set of rungs an artefact has reached, subject to
the one structural law the ladder really has — the set is downward closed. -/
structure Promotion where
  /-- Which rungs have been reached. -/
  reached : Stage → Prop
  /-- Reaching a rung means the earlier rungs were reached too. -/
  downward : ∀ {s t : Stage}, s ≤ t → reached t → reached s

namespace Promotion

/-- Reaching a rung implies every earlier rung. -/
theorem reached_of_le (p : Promotion) {s t : Stage} (h : s ≤ t) (ht : p.reached t) :
    p.reached s := p.downward h ht

/-- A promotion that has reached exactly the rungs up to `s`. -/
def reachedUpTo (s : Stage) : Promotion where
  reached := fun t => t ≤ s
  downward := fun h ht => le_trans h ht

@[simp] theorem reachedUpTo_reached (s t : Stage) : (reachedUpTo s).reached t ↔ t ≤ s := Iff.rfl

end Promotion

/-- **The ladder is strict.**  For every rung with a successor there is a
promotion that has reached the rung and not its successor: no rung implies the
next. -/
theorem no_upward_implication {s t : Stage} (h : s.next = some t) :
    ∃ p : Promotion, p.reached s ∧ ¬ p.reached t := by
  refine ⟨Promotion.reachedUpTo s, le_refl s, ?_⟩
  simp only [Promotion.reachedUpTo_reached, not_le]
  exact Stage.lt_next h

/-- The same statement as a failed contract audit: "has reached `s`" is not
adequate for "has reached `t`". -/
theorem notAdequate {s t : Stage} (h : s.next = some t) :
    ¬ Adequate (fun p : Promotion => p.reached s) (fun p => p.reached t) := by
  obtain ⟨p, hs, ht⟩ := no_upward_implication h
  exact Countermodel.not_adequate ⟨p, hs, ht⟩

/-- Every rung below `cited` has a successor, so the strictness statement covers
the whole ladder. -/
theorem every_rung_but_cited_is_strict (s : Stage) (h : s ≠ Stage.cited) :
    ∃ t, s.next = some t := by
  cases s <;> first | exact absurd rfl h | exact ⟨_, rfl⟩

/-! ## Presence in the store versus status in the build -/

/-- An **artefact**: a source text together with the environment it is elaborated
in.  `Source` and `Env` are abstract; the point is only that the second component
exists and the store does not record it. -/
structure Artefact (Source Env : Type) where
  /-- The source text, as ingested. -/
  source : Source
  /-- The toolchain, Mathlib revision and available imports it is elaborated in. -/
  env : Env

/-- The store observes the source text and nothing else. -/
def stored {Source Env : Type} (a : Artefact Source Env) : Source := a.source

/-- **Presence in the store does not determine elaboration status.**  With
`Env := Bool` reading "does this environment provide what the source needs", the
same source both elaborates and fails to elaborate, so the status is not a
function of what the store holds. -/
def presence_does_not_determine_elaboration {Source : Type} (src : Source) :
    Collision (stored (Source := Source) (Env := Bool)) (fun a => a.env) where
  left := ⟨src, true⟩
  right := ⟨src, false⟩
  distinct := by intro h; exact Bool.noConfusion (congrArg Artefact.env h)
  collide := rfl
  separate := by simp

/-- Hence no reading of the store returns the status: the failure survives every
index, digest or report computed from the stored text alone. -/
theorem no_store_reading_gives_status {Source : Type} (src : Source) (r : Source → Bool) :
    ¬ ∀ a : Artefact Source Bool, a.env = r (stored a) :=
  (presence_does_not_determine_elaboration src).no_reading r

/-- **What presence does prove.**  "This content is in the store" is a
pinned-value ledger: uniquely inhabited, hence carrying no information about the
content beyond the fact that it was filed. -/
theorem store_membership_is_a_ledger {A : Type} (a : A) (P : Ledger a → Prop) :
    (∃ l, P l) ↔ P default := ledger_no_information a P

end Integration.CorpusPromotion
