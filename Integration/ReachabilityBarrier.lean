import Integration.CoordinateSufficiency

/-!
# Reachability under a declared action language, and what a barrier means

`Agda/DASHI/Core/AdmissibleReachability.agda` defines the reflexive–transitive
closure of proof-bearing admissible actions (`Reachable`), the same-trace
execution relation (`Executes`), and proves `executesImpliesReachable`.  It does
not ask the question that every lane using it eventually asks: **what does it
mean that a state is not reachable?**

The answer is that unreachability is never a property of the state pair alone.
It is a property of the pair *together with the declared action language*, and
enlarging the language can only add reachable pairs.  So

> currently unreachable

and

> unreachable after the action language is refined

are different statements, and only the first is ever established by exhibiting
an invariant.  This file owns that distinction.

## Contents

* `ActionSystem`, `Reachable`, `Executes` — mirrors of the Agda definitions,
  with the admissibility record inlined as its precondition and postcondition;
* `executes_implies_reachable` — the Agda lemma, re-proved;
* `reachable_trans` — the composition the Agda module does not state;
* `reachable_of_weaker_precondition` — **monotonicity in the action language**:
  weakening the preconditions (or enlarging the postcondition relation) can only
  add reachable pairs;
* `not_reachable_of_invariant` — the only general way to prove unreachability:
  an invariant preserved by every admissible transition, true at the source and
  false at the target;
* `barrier_is_language_relative` — the separation, on an explicit system: with
  one action the target is unreachable (by a parity invariant), and with the
  action language extended by one more action it is reachable in two steps;
* `unreachability_never_survives_extension` — and the general statement of which
  that is an instance: no invariant argument in a smaller language is evidence
  of unreachability in a larger one.

Nothing here is a claim about planning, governance, development or capability.
The carriers are `ℕ` and `Bool`.
-/

namespace Integration.ReachabilityBarrier

/-! ## The system -/

variable {State Action : Type}

/-- Mirror of the Agda `DependentActionSystem`, dropping the `String` label. -/
structure ActionSystem (State Action : Type) where
  /-- When an action may be attempted in a state. -/
  Precondition : State → Action → Prop
  /-- Which successor states an action may produce. -/
  Postcondition : State → Action → State → Prop

/-- Mirror of the Agda `Reachable`: the reflexive–transitive closure of
admissible transitions.  The Agda `AdmissibleAction` record is inlined as its
precondition, its successor and its postcondition. -/
inductive Reachable (S : ActionSystem State Action) : State → State → Prop
  /-- Every state reaches itself. -/
  | refl (s : State) : Reachable S s s
  /-- One admissible action, then the rest of the path. -/
  | step {before after target : State} (a : Action)
      (hpre : S.Precondition before a) (hpost : S.Postcondition before a after)
      (rest : Reachable S after target) : Reachable S before target

/-- Mirror of the Agda `Executes`: reachability along a *named* action trace. -/
inductive Executes (S : ActionSystem State Action) : List Action → State → State → Prop
  /-- The empty trace. -/
  | nil (s : State) : Executes S [] s s
  /-- One admissible action of the trace, then the rest. -/
  | cons {before after target : State} {a : Action} {as : List Action}
      (hpre : S.Precondition before a) (hpost : S.Postcondition before a after)
      (rest : Executes S as after target) : Executes S (a :: as) before target

/-- The Agda `executesImpliesReachable`, re-proved. -/
theorem executes_implies_reachable {S : ActionSystem State Action} {as : List Action}
    {x y : State} (h : Executes S as x y) : Reachable S x y := by
  induction h with
  | nil s => exact .refl s
  | cons hpre hpost _ ih => exact .step _ hpre hpost ih

/-- Reachability composes.  The Agda module does not state this. -/
theorem reachable_trans {S : ActionSystem State Action} {x y z : State}
    (h₁ : Reachable S x y) (h₂ : Reachable S y z) : Reachable S x z := by
  induction h₁ with
  | refl s => exact h₂
  | step a hpre hpost _ ih => exact .step a hpre hpost (ih h₂)

/-! ## Monotonicity in the action language -/

/-- **Enlarging the action language can only add reachable pairs.**  If every
admissible transition of `S` is admissible in `T`, then everything `S` reaches
`T` reaches. -/
theorem reachable_of_weaker_precondition {S T : ActionSystem State Action}
    (hpre : ∀ x a, S.Precondition x a → T.Precondition x a)
    (hpost : ∀ x a y, S.Postcondition x a y → T.Postcondition x a y)
    {x y : State} (h : Reachable S x y) : Reachable T x y := by
  induction h with
  | refl s => exact .refl s
  | step a hp hq _ ih => exact .step a (hpre _ _ hp) (hpost _ _ _ hq) ih

/-- **The only general route to unreachability.**  An invariant preserved by
every admissible transition, holding at the source and failing at the target,
refutes reachability — and says nothing about any other action language. -/
theorem not_reachable_of_invariant {S : ActionSystem State Action} (P : State → Prop)
    (hpres : ∀ x a y, S.Precondition x a → S.Postcondition x a y → P x → P y)
    {x y : State} (hx : P x) (hy : ¬ P y) : ¬ Reachable S x y := by
  intro h
  induction h with
  | refl s => exact hy hx
  | step a hp hq _ ih => exact ih (hpres _ _ _ hp hq hx) hy

/-! ## An explicit barrier -/

/-- Two actions: `false` advances by two, `true` advances by one. -/
def stepSize : Bool → ℕ
  | false => 2
  | true => 1

/-- The counter system whose admissible actions are those in the declared
language `L`. -/
def counter (L : Bool → Prop) : ActionSystem ℕ Bool where
  Precondition := fun _ a => L a
  Postcondition := fun x a y => y = x + stepSize a

/-- The restricted language: only the two-step action. -/
def coarseLanguage : Bool → Prop := fun a => a = false

/-- The extended language: both actions. -/
def fullLanguage : Bool → Prop := fun _ => True

/-- Under the restricted language, evenness is an invariant. -/
theorem even_invariant (x : ℕ) (a : Bool) (y : ℕ)
    (hpre : (counter coarseLanguage).Precondition x a)
    (hpost : (counter coarseLanguage).Postcondition x a y) (hx : Even x) : Even y := by
  have ha : a = false := hpre
  subst ha
  have : y = x + 2 := hpost
  subst this
  exact hx.add (by decide)

/-- **The barrier is relative to the declared language.**  With only the
two-step action the odd target is unreachable; adding the one-step action makes
it reachable in two steps.  Neither statement contradicts the other, and the
first is not evidence for a claim about the second. -/
theorem barrier_is_language_relative :
    ¬ Reachable (counter coarseLanguage) 0 3 ∧ Reachable (counter fullLanguage) 0 3 := by
  constructor
  · exact not_reachable_of_invariant Even even_invariant (by decide) (by decide)
  · refine .step false trivial (show (2 : ℕ) = 0 + stepSize false from rfl) ?_
    exact .step true trivial (show (3 : ℕ) = 2 + stepSize true from rfl) (.refl 3)

/-- The extension really is an extension. -/
theorem coarse_subset_full (x : ℕ) (a : Bool) :
    (counter coarseLanguage).Precondition x a → (counter fullLanguage).Precondition x a :=
  fun _ => trivial

/-- **No unreachability result survives an extension of the action language.**
Whatever was reachable before is still reachable; so if a target becomes
reachable in the larger language, the earlier invariant argument was never
about it.  This is the general form of the barrier above. -/
theorem unreachability_never_survives_extension {S T : ActionSystem State Action}
    (hpre : ∀ x a, S.Precondition x a → T.Precondition x a)
    (hpost : ∀ x a y, S.Postcondition x a y → T.Postcondition x a y)
    {x y : State} (h : ¬ Reachable T x y) : ¬ Reachable S x y :=
  fun hS => h (reachable_of_weaker_precondition hpre hpost hS)

/-- And the converse fails, which is the content: `barrier_is_language_relative`
exhibits a pair unreachable in the smaller language and reachable in the
larger. -/
theorem converse_fails :
    ∃ (L L' : Bool → Prop) (x y : ℕ), (∀ z a, (counter L).Precondition z a →
      (counter L').Precondition z a) ∧ ¬ Reachable (counter L) x y ∧
        Reachable (counter L') x y :=
  ⟨coarseLanguage, fullLanguage, 0, 3, coarse_subset_full,
    barrier_is_language_relative.1, barrier_is_language_relative.2⟩

end Integration.ReachabilityBarrier
