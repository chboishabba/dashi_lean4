import Integration.Kernel.Loop

/-!
# Option cones: collective action and the productive dialectical join

Two governance instances of the kernel's order structure, both stated in terms
of the **option cone** — the set of actions available to an agent — rather than
in terms of labels.

## §1 Seven modes, none implying another

`ActionMode` lists participation, refusal, withdrawal, rule-change power,
viable exit, formal organisation and effective bargaining.
`modes_pairwise_independent` proves that for any two distinct modes there is a
situation exhibiting the first and not the second, so none of the seven is a
consequence of any other.  This is a logical independence statement about the
seven predicates, and nothing more.

## §2 Organisation is not the theorem; expansion is

* `StrictExpansion O₀ O₁ : O₀ ⊂ O₁` — new actions become reachable.
* `organisation_without_expansion` — a situation with formal organisation
  present and no expansion at all: **"a union exists" is not the theorem.**
* `EffectiveOrganisation` bundles organisation *with* the strict expansion, and
  `effectiveOrganisation_expands` / `effective_organisation_exists` show the
  bundle is non-vacuous.
* `expansion_is_not_refinement` — option-cone growth is the *opposite* order to
  residual-fibre narrowing; the kernel's `Refines` never holds across a strict
  expansion.  So affordance expansion and epistemic refinement are different
  monotonicities and must not be conflated.

## §3 Productive dialectical joins

`ProductiveDialecticalJoin` is a structure that can only be built by supplying
proofs of: both inputs preserved, strict expansion over each input, and a
retained order residual (the two transports do not commute).  Then

* `join_irreducible` — the join equals neither input;
* `opposition_is_not_synthesis` — an opposed, order-residual pair whose union
  join fails the expansion requirement, so **opposition ⇏ synthesis**;
* `productive_join_exists` — the criterion is satisfiable.

**Claim boundary.** An option cone is a set; nothing here models bargaining,
labour, institutions or their history.  What is proved is which of the corpus's
governance slogans are theorems about that order and which are refused.
-/

namespace Integration.Kernel.Instances.CollectiveAction

open Set

/-! ## §1 Seven independent modes -/

/-- The seven modes the corpus insists on keeping apart. -/
inductive ActionMode
  /-- Taking part on the existing terms. -/
  | participation
  /-- Declining a particular demand. -/
  | refusal
  /-- Leaving the activity. -/
  | withdrawal
  /-- Power to change the rules. -/
  | ruleChange
  /-- A viable outside option. -/
  | exitOption
  /-- Formal organisation. -/
  | organisation
  /-- Effective bargaining. -/
  | bargaining
  deriving DecidableEq, Fintype, Repr

/-- A situation, indexed by the mode it exhibits. -/
abbrev Situation := ActionMode

/-- Which modes a situation exhibits. -/
def holds (m : ActionMode) (s : Situation) : Prop := m = s

/-- **No mode implies any other.** -/
theorem modes_pairwise_independent (m₁ m₂ : ActionMode) (h : m₁ ≠ m₂) :
    ∃ s : Situation, holds m₁ s ∧ ¬ holds m₂ s :=
  ⟨m₁, rfl, fun hc => h hc.symm⟩

/-! ## §2 Option cones -/

variable {A : Type*}

/-- Collective organisation is theorem-bearing only when new actions become
reachable. -/
def StrictExpansion (O₀ O₁ : Set A) : Prop := O₀ ⊂ O₁

/-- **Organisation present, nothing gained.** -/
theorem organisation_without_expansion :
    ∃ (s : Situation) (O₀ O₁ : Set Bool),
      holds ActionMode.organisation s ∧ O₁ = O₀ ∧ ¬ StrictExpansion O₀ O₁ :=
  ⟨ActionMode.organisation, {true}, {true}, rfl, rfl, fun h => h.ne rfl⟩

/-- Organisation *with* a proof that the option cone strictly expanded. -/
structure EffectiveOrganisation (A : Type*) where
  /-- The options available before. -/
  before : Set A
  /-- The options available after. -/
  after : Set A
  /-- Formal organisation is present. -/
  organised : Situation
  /-- It is the organisation mode. -/
  organised_is : holds ActionMode.organisation organised
  /-- New safe actions became reachable. -/
  expands : StrictExpansion before after

theorem effectiveOrganisation_expands (E : EffectiveOrganisation A) : E.before ⊂ E.after :=
  E.expands

theorem effective_organisation_exists : Nonempty (EffectiveOrganisation Bool) :=
  ⟨{ before := {true}
     after := univ
     organised := ActionMode.organisation
     organised_is := rfl
     expands := by
       refine ⟨subset_univ _, fun h => ?_⟩
       have : (false : Bool) ∈ ({true} : Set Bool) := h (mem_univ _)
       exact Bool.noConfusion this }⟩

/-- Affordance expansion is the opposite monotonicity to epistemic refinement:
the kernel's `Refines` never holds across a strict expansion. -/
theorem expansion_is_not_refinement {O₀ O₁ : Set A} (h : StrictExpansion O₀ O₁) :
    ¬ Integration.Kernel.ResidualFibre.Refines O₁ O₀ := fun hr => h.ne (Subset.antisymm h.subset hr)

/-! ## §3 Productive dialectical joins -/

/-- A join that earns the word "productive": both inputs preserved, strictly
expanded over each, and the order residual of the two transports retained. -/
structure ProductiveDialecticalJoin (A S : Type*) where
  /-- The left input's option cone. -/
  optL : Set A
  /-- The right input's option cone. -/
  optR : Set A
  /-- The joint option cone. -/
  optJ : Set A
  /-- The left transport. -/
  tL : S → S
  /-- The right transport. -/
  tR : S → S
  /-- The left input is preserved and strictly expanded. -/
  leftStrict : optL ⊂ optJ
  /-- The right input is preserved and strictly expanded. -/
  rightStrict : optR ⊂ optJ
  /-- The order in which the two are applied still matters. -/
  orderResidual : ∃ s, tL (tR s) ≠ tR (tL s)

variable {S : Type*}

theorem join_preserves_inputs (J : ProductiveDialecticalJoin A S) :
    J.optL ⊆ J.optJ ∧ J.optR ⊆ J.optJ := ⟨J.leftStrict.subset, J.rightStrict.subset⟩

/-- The join is irreducible to either side. -/
theorem join_irreducible (J : ProductiveDialecticalJoin A S) :
    J.optJ ≠ J.optL ∧ J.optJ ≠ J.optR :=
  ⟨fun h => J.leftStrict.ne h.symm, fun h => J.rightStrict.ne h.symm⟩

/-- **Opposition ⇏ synthesis.**  Two sides with a genuine order residual whose
union join adds nothing: the productivity requirement fails, so the pair being
"opposed" does not manufacture a productive join. -/
theorem opposition_is_not_synthesis :
    ∃ (optL optR : Set Bool) (tL tR : Bool → Bool),
      (∃ s, tL (tR s) ≠ tR (tL s)) ∧ ¬ StrictExpansion optL (optL ∪ optR) := by
  refine ⟨{true}, {true}, not, fun _ => true, ⟨true, by simp⟩, ?_⟩
  intro h
  exact h.ne (by simp)

/-- The criterion is satisfiable. -/
theorem productive_join_exists : Nonempty (ProductiveDialecticalJoin Bool Bool) :=
  ⟨{ optL := {true}
     optR := {false}
     optJ := univ
     tL := not
     tR := fun _ => true
     leftStrict := by
       refine ⟨subset_univ _, fun h => ?_⟩
       have : (false : Bool) ∈ ({true} : Set Bool) := h (mem_univ _)
       exact Bool.noConfusion this
     rightStrict := by
       refine ⟨subset_univ _, fun h => ?_⟩
       have : (true : Bool) ∈ ({false} : Set Bool) := h (mem_univ _)
       exact Bool.noConfusion this
     orderResidual := ⟨true, by simp⟩ }⟩

end Integration.Kernel.Instances.CollectiveAction
