import Integration.Kernel.Probe

/-!
# Four merge modes, kept apart by proof

Third component of the shared kernel.  Two branches refine a common base
residual fibre; the discoveries have to be combined.  The corpus's search lane
insists that

```
fast-forward ≠ three-way reconciliation ≠ proved-knowledge join ≠ guarded reconciliation,
```

and this file makes that a theorem rather than a convention.

## The four modes

For a base fibre `b` and branch fibres `l r` with `Refines l b`, `Refines r b`:

* `fastForward b l r` — take the other side *provided one side has not moved*
  (`NotDiverged b l`).  Implemented as `if l = b then r else b`: without
  divergence it is `r`; with divergence it refuses and returns `b`.
* `threeWay l r = l ∩ r` — reconcile both refinements.
* `provedJoin l r jl jr` — reconcile, but only claims carrying a receipt;
  a side without a receipt contributes nothing.
* `guarded g b l r` — reconcile only if the admission guard `g` holds,
  otherwise keep the base.

## What is proved

* `fastForward_refines`, `threeWay_refines_base`, `provedJoin_refines_base`,
  `guarded_refines_base` — no mode ever *widens* the base fibre; in particular
  `guarded_never_weakens_base`.
* `threeWay_refines_left`, `threeWay_refines_right`, `threeWay_comm`,
  `threeWay_assoc`, `threeWay_idem` — reconciliation is a meet.
* `merge_preserves_truth` — a world surviving on both branches survives the
  merge; `merge_preserves_determination` — anything either branch had already
  determined stays determined.
* `fastForward_eq_threeWay_of_not_diverged` — the modes *agree* exactly in the
  degenerate case, which is why they get confused.
* `threeWay_can_refute` — two individually inhabited branches can merge to `∅`:
  reconciliation is also conflict detection.

The separations (`§3`), each an explicit witness on `Bool × Bool`:

* `fastForward_ne_threeWay`
* `provedJoin_ne_threeWay`
* `guarded_ne_threeWay`
* `guarded_ne_fastForward`

**Claim boundary.** A "receipt" here is a `Prop` supplied with the merge, and a
"guard" is a `Prop`; nothing in this file checks either.  What is proved is only
how the four combination rules differ once those inputs are given.
-/

namespace Integration.Kernel.Merge

open Set Integration.Kernel.ResidualFibre

variable {Ω C : Type*}

/-! ## §1 The four modes -/

/-- The branch has not moved away from its base. -/
def NotDiverged (b l : Set Ω) : Prop := l = b

open Classical in
/-- Fast-forward: adopt `r` when `l` has not diverged, otherwise refuse. -/
noncomputable def fastForward (b l r : Set Ω) : Set Ω := if l = b then r else b

/-- Three-way reconciliation. -/
def threeWay (l r : Set Ω) : Set Ω := l ∩ r

open Classical in
/-- Proved-knowledge join: a side only contributes if it carries a receipt. -/
noncomputable def provedJoin (b l r : Set Ω) (jl jr : Prop) : Set Ω :=
  (if jl then l else b) ∩ (if jr then r else b)

open Classical in
/-- Guarded reconciliation: admit the join only under the guard. -/
noncomputable def guarded (g : Prop) (b l r : Set Ω) : Set Ω := if g then l ∩ r else b

/-! ## §2 What every mode guarantees -/

theorem threeWay_refines_left (l r : Set Ω) : Refines (threeWay l r) l := inter_subset_left

theorem threeWay_refines_right (l r : Set Ω) : Refines (threeWay l r) r := inter_subset_right

theorem threeWay_refines_base {b l r : Set Ω} (hl : Refines l b) : Refines (threeWay l r) b :=
  inter_subset_left.trans hl

theorem threeWay_comm (l r : Set Ω) : threeWay l r = threeWay r l := inter_comm l r

theorem threeWay_assoc (l r s : Set Ω) : threeWay (threeWay l r) s = threeWay l (threeWay r s) :=
  inter_assoc l r s

@[simp] theorem threeWay_idem (l : Set Ω) : threeWay l l = l := inter_self l

theorem fastForward_refines {b l r : Set Ω} (hr : Refines r b) : Refines (fastForward b l r) b := by
  unfold fastForward
  split
  · exact hr
  · exact refines_refl b

theorem provedJoin_refines_base {b l r : Set Ω} (jl jr : Prop) (hl : Refines l b) :
    Refines (provedJoin b l r jl jr) b := by
  unfold provedJoin
  refine inter_subset_left.trans ?_
  split
  · exact hl
  · exact refines_refl b

theorem guarded_refines_base {b l r : Set Ω} (g : Prop) (hl : Refines l b) :
    Refines (guarded g b l r) b := by
  unfold guarded
  split
  · exact inter_subset_left.trans hl
  · exact refines_refl b

/-- **A guarded merge never weakens the base**, whatever the guard decides. -/
theorem guarded_never_weakens_base {b l r : Set Ω} (g : Prop) (hl : Refines l b) :
    guarded g b l r ⊆ b := guarded_refines_base g hl

/-- A world surviving on both branches survives the reconciliation. -/
theorem merge_preserves_truth {l r : Set Ω} {w : Ω} (hl : w ∈ l) (hr : w ∈ r) :
    w ∈ threeWay l r := ⟨hl, hr⟩

/-- Anything a branch had already determined stays determined after the merge. -/
theorem merge_preserves_determination {l r : Set Ω} {c : Ω → C} (h : Determines l c) :
    Determines (threeWay l r) c := determines_mono (threeWay_refines_left l r) h

/-- Without divergence, fast-forward *is* three-way reconciliation.  This
degenerate agreement is the source of the confusion the separations refuse. -/
theorem fastForward_eq_threeWay_of_not_diverged {b l r : Set Ω} (h : NotDiverged b l)
    (hr : Refines r b) : fastForward b l r = threeWay l r := by
  subst h
  simp only [fastForward, threeWay]
  exact (inter_eq_right.2 hr).symm

/-- Reconciliation is also conflict detection: two inhabited branches can merge
to the empty fibre. -/
theorem threeWay_can_refute :
    ∃ l r : Set Bool, l.Nonempty ∧ r.Nonempty ∧ threeWay l r = ∅ := by
  refine ⟨{true}, {false}, ⟨true, rfl⟩, ⟨false, rfl⟩, ?_⟩
  ext w; cases w <;> simp [threeWay]

/-! ## §3 The four modes are pairwise different

All witnesses use the base `univ` and two genuinely divergent branches
`l = {w | w.1 = true}`, `r = {w | w.2 = true}` in `Bool × Bool`. -/

private def bwit : Set (Bool × Bool) := univ
private def lwit : Set (Bool × Bool) := {w | w.1 = true}
private def rwit : Set (Bool × Bool) := {w | w.2 = true}

private theorem lwit_refines : Refines lwit bwit := subset_univ _
private theorem rwit_refines : Refines rwit bwit := subset_univ _
private theorem lwit_diverged : ¬ NotDiverged bwit lwit := by
  intro h
  have : ((false, true) : Bool × Bool) ∈ lwit := h ▸ mem_univ _
  exact Bool.noConfusion this

/-- Fast-forward is not three-way reconciliation: with both branches diverged,
fast-forward refuses and keeps the base. -/
theorem fastForward_ne_threeWay :
    fastForward bwit lwit rwit ≠ threeWay lwit rwit := by
  have h : fastForward bwit lwit rwit = bwit := if_neg lwit_diverged
  intro hc
  have h1 : ((false, false) : Bool × Bool) ∈ threeWay lwit rwit := by
    rw [← hc, h]; exact mem_univ _
  simp [threeWay, lwit, rwit] at h1

/-- A proved-knowledge join with an unreceipted side is not the three-way
reconciliation: the unreceipted discovery is dropped. -/
theorem provedJoin_ne_threeWay :
    provedJoin bwit lwit rwit True False ≠ threeWay lwit rwit := by
  have h : provedJoin bwit lwit rwit True False = lwit ∩ bwit := by
    simp [provedJoin]
  intro hc
  have h1 : ((true, false) : Bool × Bool) ∈ threeWay lwit rwit := by
    rw [← hc, h]; exact ⟨rfl, mem_univ _⟩
  simp [threeWay, rwit] at h1

/-- A guarded reconciliation whose guard fails is not the three-way
reconciliation. -/
theorem guarded_ne_threeWay :
    guarded False bwit lwit rwit ≠ threeWay lwit rwit := by
  have h : guarded False bwit lwit rwit = bwit := if_neg not_false
  intro hc
  have h1 : ((false, false) : Bool × Bool) ∈ threeWay lwit rwit := by
    rw [← hc, h]; exact mem_univ _
  simp [threeWay, lwit, rwit] at h1

/-- A guarded reconciliation whose guard holds is not a fast-forward: the
fast-forward refuses on divergence while the guarded merge combines. -/
theorem guarded_ne_fastForward :
    guarded True bwit lwit rwit ≠ fastForward bwit lwit rwit := by
  have hg : guarded True bwit lwit rwit = lwit ∩ rwit := if_pos trivial
  have hf : fastForward bwit lwit rwit = bwit := if_neg lwit_diverged
  intro hc
  have h1 : ((false, false) : Bool × Bool) ∈ lwit ∩ rwit := by
    rw [← hg, hc, hf]; exact mem_univ _
  simp [lwit, rwit] at h1

end Integration.Kernel.Merge
