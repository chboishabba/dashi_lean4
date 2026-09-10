import Integration.Kernel.ResidualFibre

/-!
# Discriminators, probes and the AND-node terminal bug

Second component of the shared kernel.  Given a residual fibre and a consumer
coordinate, which probe is worth running, and what does running it buy?

## What is proved

* `Discriminates O F` — the probe separates two surviving worlds.  For an
  *achievable* outcome this is exactly the ability to refine strictly:
  `strictly_refines_iff_discriminates`.  Unachievable outcomes are excluded on
  purpose: refining by an outcome no surviving world produces would "shrink"
  the fibre to `∅`, which is refutation, not information
  (`unachievable_outcome_empties`).
* `ResolvesFor O F c` and `resolves_of_factors` — a probe whose read-out
  determines the consumer coordinate resolves the collision *whatever* it
  returns.  Conversely `discriminating_probe_need_not_resolve`: separating
  worlds is strictly weaker than resolving the consumer's question.
* `collision_persists_of_constant` — a probe constant on the fibre changes
  nothing at all.
* `progress`: after a resolving probe on an inhabited fibre the consumer
  coordinate is determined and the fibre is still inhabited
  (`resolving_probe_closes`).

## The AND-node terminal bug (`§4`)

A proof/experiment search that treats *an action with no targets* as a
successful terminal cannot distinguish

```
unknown empirical leaf     from     leaf with an empty target list.
```

`vacuous_success_is_not_resolution` exhibits an AND node all of whose leaves are
target-free — so the search reports success — over a fibre on which the
consumer collision is untouched.  `real_target_resolves` shows the same node
shape *with* one genuine target does resolve it, so the failure is the vacuity
convention and not the node format.

**Claim boundary.** Nothing here models the cost, feasibility or admissibility
of running a probe; those are separate obligations (see
`Integration.Kernel.Authority` and `Integration.Kernel.Distribution`).
-/

namespace Integration.Kernel.Probe

open Set Integration.Kernel.ResidualFibre

variable {Ω Y C : Type*}

/-! ## §1 Discrimination -/

/-- The probe separates two worlds still in the fibre. -/
def Discriminates (O : Channel Ω Y) (F : Set Ω) : Prop := Collision F O.read

/-- The outcomes the fibre can actually produce. -/
def achievable (O : Channel Ω Y) (F : Set Ω) : Set Y := O.read '' F

theorem refine_eq_self_of_constant {O : Channel Ω Y} {F : Set Ω} {y : Y}
    (h : ∀ w ∈ F, O.read w = y) : refine F O y = F :=
  Subset.antisymm (refine_refines _ _ _) fun w hw => ⟨hw, h w hw⟩

/-- Refining by an outcome the fibre cannot produce is refutation, not information. -/
theorem unachievable_outcome_empties {O : Channel Ω Y} {F : Set Ω} {y : Y}
    (h : y ∉ achievable O F) : refine F O y = ∅ := by
  ext w
  simp only [mem_refine, mem_empty_iff_false, iff_false, not_and]
  intro hw hy
  exact h ⟨w, hw, hy⟩

/-- A probe buys a strict refinement at some achievable outcome exactly when it
discriminates on the fibre. -/
theorem strictly_refines_iff_discriminates {O : Channel Ω Y} {F : Set Ω} :
    (∃ y ∈ achievable O F, refine F O y ⊂ F) ↔ Discriminates O F := by
  constructor
  · rintro ⟨y, ⟨w₁, hw₁F, hw₁⟩, -, hne⟩
    obtain ⟨w, hwF, hw⟩ := not_subset.1 hne
    have hread : O.read w ≠ y := fun h => hw ⟨hwF, h⟩
    exact ⟨w, hwF, w₁, hw₁F, by rw [hw₁]; exact hread⟩
  · rintro ⟨w₁, h₁, w₂, h₂, hne⟩
    refine ⟨O.read w₁, ⟨w₁, h₁, rfl⟩, refine_refines _ _ _, ?_⟩
    intro hsub
    exact hne (hsub h₂).2.symm

/-! ## §2 Resolving a consumer collision -/

/-- The probe resolves the consumer's question: whatever it returns, the
consumer coordinate is determined afterwards. -/
def ResolvesFor (O : Channel Ω Y) (F : Set Ω) (c : Ω → C) : Prop :=
  ∀ y, Determines (refine F O y) c

/-- If the consumer coordinate factors through the probe read-out, the probe
resolves the collision. -/
theorem resolves_of_factors {O : Channel Ω Y} {F : Set Ω} {c : Ω → C} {g : Y → C}
    (hfac : ∀ w, c w = g (O.read w)) : ResolvesFor O F c := by
  intro y
  exact ⟨g y, fun w hw => by rw [hfac w, hw.2]⟩

/-- A resolving probe on an inhabited fibre both closes the consumer's question
and leaves an inhabited fibre. -/
theorem resolving_probe_closes {O : Channel Ω Y} {F : Set Ω} {c : Ω → C} {w : Ω}
    (hw : w ∈ F) (h : ResolvesFor O F c) :
    (refine F O (O.read w)).Nonempty ∧ Determines (refine F O (O.read w)) c :=
  ⟨refine_nonempty_of_truth hw, h _⟩

/-- A probe that is constant on the fibre changes nothing: the collision persists. -/
theorem collision_persists_of_constant {O : Channel Ω Y} {F : Set Ω} {c : Ω → C} {y : Y}
    (hconst : ∀ w ∈ F, O.read w = y) (hcol : Collision F c) : Collision (refine F O y) c := by
  obtain ⟨w₁, h₁, w₂, h₂, hne⟩ := hcol
  exact ⟨w₁, ⟨h₁, hconst w₁ h₁⟩, w₂, ⟨h₂, hconst w₂ h₂⟩, hne⟩

/-- **Separating worlds is weaker than answering the question.**  A probe can
discriminate on the fibre and still leave the consumer coordinate open. -/
theorem discriminating_probe_need_not_resolve :
    ∃ (F : Set (Bool × Bool)) (O : Channel (Bool × Bool) Bool) (c : Bool × Bool → Bool),
      Discriminates O F ∧ ¬ ResolvesFor O F c := by
  refine ⟨univ, ⟨Prod.snd⟩, Prod.fst, ⟨(true, true), mem_univ _, (true, false), mem_univ _, by
    simp⟩, ?_⟩
  intro h
  obtain ⟨v, hv⟩ := h true
  have h1 : (true, true).1 = v := hv _ ⟨mem_univ _, rfl⟩
  have h2 : (false, true).1 = v := hv _ ⟨mem_univ _, rfl⟩
  rw [← h2] at h1
  exact Bool.noConfusion h1

/-! ## §3 Probe sequences -/

/-- The events a list of achievable readings contributes. -/
def readingEvents (O : Channel Ω Y) (ys : List Y) : List (Set Ω) := ys.map (event O)

theorem refineAll_readingEvents_refines (F : Set Ω) (O : Channel Ω Y) (ys : List Y) :
    Refines (refineAll F (readingEvents O ys)) F := refineAll_refines _ _

/-! ## §4 The AND-node terminal bug -/

/-- A leaf of an AND node: the list of observation events discharging it.  An
*unknown empirical* leaf is recorded with `targets = []`, which is precisely the
confusion this section refuses. -/
structure Leaf (Ω : Type*) where
  /-- The observation events this leaf would contribute if discharged. -/
  targets : List (Set Ω)

/-- An AND node is its list of leaves. -/
structure AndNode (Ω : Type*) where
  /-- The conjuncts. -/
  leaves : List (Leaf Ω)

/-- Everything the node actually contributes to the residual fibre. -/
def AndNode.contribution (n : AndNode Ω) (F : Set Ω) : Set Ω :=
  refineAll F (n.leaves.flatMap Leaf.targets)

/-- The buggy criterion: a leaf with no targets is a successful terminal. -/
def AndNode.vacuouslySucceeds (n : AndNode Ω) : Prop := ∀ l ∈ n.leaves, l.targets = []

/-- The honest criterion: the node's contribution determines the consumer coordinate. -/
def AndNode.Resolves (n : AndNode Ω) (F : Set Ω) (c : Ω → C) : Prop :=
  Determines (n.contribution F) c

theorem AndNode.contribution_refines (n : AndNode Ω) (F : Set Ω) :
    Refines (n.contribution F) F := refineAll_refines _ _

theorem flatMap_targets_eq_nil {ls : List (Leaf Ω)} (h : ∀ l ∈ ls, l.targets = []) :
    ls.flatMap Leaf.targets = [] := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
      have hl : l.targets = [] := h l (by simp)
      have hls : ∀ l' ∈ ls, l'.targets = [] := fun l' hl' => h l' (by simp [hl'])
      simp [List.flatMap_cons, hl, ih hls]

theorem AndNode.contribution_eq_of_vacuous {n : AndNode Ω} (h : n.vacuouslySucceeds)
    (F : Set Ω) : n.contribution F = F := by
  simp [AndNode.contribution, flatMap_targets_eq_nil h]

/-- **Unknown empirical leaf ≠ empty target list.**  A node whose leaves all
carry no targets is reported successful by the vacuity convention, while the
consumer collision it was supposed to settle is untouched. -/
theorem vacuous_success_is_not_resolution :
    ∃ (n : AndNode (Bool × Bool)) (F : Set (Bool × Bool)) (c : Bool × Bool → Bool),
      n.vacuouslySucceeds ∧ Collision F c ∧ ¬ n.Resolves F c := by
  refine ⟨⟨[⟨[]⟩, ⟨[]⟩]⟩, univ, Prod.fst, ?_, ⟨(true, true), mem_univ _, (false, true),
    mem_univ _, by simp⟩, ?_⟩
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> rfl
  · intro h
    rw [AndNode.Resolves, AndNode.contribution_eq_of_vacuous (by
      intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> rfl)] at h
    obtain ⟨v, hv⟩ := h
    have h1 : (true, true).1 = v := hv _ (mem_univ _)
    have h2 : (false, true).1 = v := hv _ (mem_univ _)
    rw [← h2] at h1
    exact Bool.noConfusion h1

/-- The same node shape with one genuine target does resolve the collision: the
failure above is the vacuity convention, not the node format. -/
theorem real_target_resolves :
    ∃ n : AndNode (Bool × Bool),
      n.Resolves (univ : Set (Bool × Bool)) Prod.fst := by
  refine ⟨⟨[⟨[{w | w.1 = true}]⟩]⟩, ⟨true, fun w hw => ?_⟩⟩
  simpa [AndNode.contribution, refineAll, refineBy] using hw.2

end Integration.Kernel.Probe
