import Integration.Kernel.Quotient

/-!
# Append-only history: repair adds information, it does not rewrite provenance

The corpus states in several lanes that a correction must *add* to the record
rather than silently replace it — that a revision is a new entry, not an edit of
an old one, and that the earlier reading remains a correct reading of the
earlier record.  `Integration.Kernel.Quotient.refinement_is_not_refutation`
already owns the coordinate form of that.  This file owns the **temporal** form.

## What is proved

* `Extends` (list prefix) is a partial order, and `append_extends` — every
  correction extends the history.
* **`earlier_entries_unchanged`** — under an extension, every position of the
  old history reads exactly as before.  This is non-retroactivity.
* **`correction_does_not_erase`** — the entry being corrected is still in the
  record after the correction.
* **`rewriting_is_not_an_extension`** — editing a past entry in place is
  provably *not* an extension, so the two operations are distinguishable and
  the discipline is not vacuous.
* `replay_append` — replaying an extended history is replaying the old one and
  then the new events, so the current state is a function of the history …
* **`state_does_not_determine_history`** — … and never conversely: two
  different histories replay to the same state, an instance of
  `Integration.Kernel.Quotient.not_descendsThrough_of_collision`.  A state
  snapshot is a quotient of the record; keeping the log is what keeps the
  provenance.
* `history_strictly_refines_state` packages the two directions.

**Claim boundary.**  A history is a `List` of arbitrary events and replay is an
arbitrary fold.  Nothing is claimed about any storage system, ledger or
physical record.
-/

namespace Integration.Kernel.AppendOnlyHistory

open Integration.Kernel.Quotient

universe u v

variable {Ev : Type u} {S : Type v}

/-! ## §1 Histories and extensions -/

/-- A history is the events so far, oldest first. -/
abbrev History (Ev : Type u) : Type u := List Ev

/-- Recording a new event. -/
def append (h : History Ev) (e : Ev) : History Ev := h ++ [e]

/-- `h'` extends `h`: everything already recorded is still recorded, in place. -/
def Extends (h' h : History Ev) : Prop := h <+: h'

theorem extends_refl (h : History Ev) : Extends h h := List.prefix_refl h

theorem extends_trans {a b c : History Ev} (h₁ : Extends a b) (h₂ : Extends b c) :
    Extends a c := h₂.trans h₁

theorem extends_antisymm {a b : History Ev} (h₁ : Extends a b) (h₂ : Extends b a) : a = b :=
  h₂.eq_of_length (le_antisymm h₂.length_le h₁.length_le)

theorem append_extends (h : History Ev) (e : Ev) : Extends (append h e) h :=
  ⟨[e], rfl⟩

theorem extends_nil (h : History Ev) : Extends h [] := List.nil_prefix

/-! ## §2 Non-retroactivity -/

/-- **The past is not rewritten.**  Every position of the old history reads the
same in the extended one. -/
theorem earlier_entries_unchanged {h' h : History Ev} (hx : Extends h' h) (i : ℕ)
    (hi : i < h.length) : h'[i]? = h[i]? := by
  obtain ⟨t, rfl⟩ := hx
  rw [List.getElem?_append_left hi]

/-- A correction never erases what it corrects. -/
theorem correction_does_not_erase {h : History Ev} {x : Ev} (hx : x ∈ h) (e : Ev) :
    x ∈ append h e := List.mem_append_left _ hx

/-- The corrected record is strictly longer: the repair is visible. -/
theorem append_length (h : History Ev) (e : Ev) : (append h e).length = h.length + 1 := by
  simp [append]

/-- **Editing in place is not extending.**  Replacing a past entry produces a
history that is not an extension of the original, so the two operations are
genuinely different and the append-only discipline has content. -/
theorem rewriting_is_not_an_extension :
    ∃ (h : History Bool) (i : ℕ) (e : Bool), ¬ Extends (h.set i e) h := by
  refine ⟨[true], 0, false, ?_⟩
  rintro ⟨t, ht⟩
  simp only [List.set, List.cons_append, List.nil_append, List.cons.injEq] at ht
  exact Bool.noConfusion ht.1

/-! ## §3 The state is a quotient of the record -/

/-- Replaying a history from an initial state. -/
def replay (step : S → Ev → S) (s₀ : S) : History Ev → S
  | [] => s₀
  | e :: es => replay step (step s₀ e) es

@[simp] theorem replay_nil (step : S → Ev → S) (s₀ : S) : replay step s₀ [] = s₀ := rfl

theorem replay_cons (step : S → Ev → S) (s₀ : S) (e : Ev) (es : History Ev) :
    replay step s₀ (e :: es) = replay step (step s₀ e) es := rfl

/-- Replay respects concatenation, so an extension is replayed by continuing
from where the old history left off. -/
theorem replay_append_list (step : S → Ev → S) (s₀ : S) (h t : History Ev) :
    replay step s₀ (h ++ t) = replay step (replay step s₀ h) t := by
  induction h generalizing s₀ with
  | nil => rfl
  | cons e es ih => simpa [replay_cons] using ih (step s₀ e)

theorem replay_append (step : S → Ev → S) (s₀ : S) (h : History Ev) (e : Ev) :
    replay step s₀ (append h e) = step (replay step s₀ h) e := by
  simp [append, replay_append_list, replay_cons]

/-- Toggling a Boolean state. -/
def toggle : Bool → Unit → Bool := fun b _ => !b

/-- **A state snapshot does not determine the history.**  Two different records
replay to the same state, so the current state is a strictly coarser reading
than the log. -/
theorem state_does_not_determine_history :
    ¬ DescendsThrough (id : History Unit → History Unit)
        (fun h => replay toggle false h) :=
  not_descendsThrough_of_collision (x := []) (y := [(), ()]) rfl (by decide)

/-- The history, on the other hand, does determine the state. -/
theorem state_descends_through_history (step : S → Ev → S) (s₀ : S) :
    DescendsThrough (fun h => replay step s₀ h) (id : History Ev → History Ev) :=
  ⟨fun h => replay step s₀ h, fun _ => rfl⟩

/-- The two directions together: keeping the log strictly refines keeping the
state, and the state reading survives the refinement unchanged. -/
theorem history_strictly_refines_state :
    StrictlyRefines (fun h => replay toggle false h) (id : History Unit → History Unit) where
  law := fun _ _ h => congrArg _ h
  witness := ⟨[], [(), ()], rfl, by decide⟩

end Integration.Kernel.AppendOnlyHistory
