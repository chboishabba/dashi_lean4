import Integration.CoordinateSufficiency

/-!
# Multi-objective outcomes: dominance, incomparability, and what a scalar loses

`Agda/DASHI/Environment/ParetoPlanning.agda` defines a genuine dominance
relation on vectors of directed objective scores — `scoreNoWorse`,
`scoreStrictlyBetter`, `VectorNoWorse`, `SomeStrictlyBetter`, `Dominates`,
`NonDominatedIn` — and proves nothing about it.  Its only inhabited value is a
record of five `Bool` flags, all set to `true`.

The relation is worth owning, because a vector-valued outcome with no canonical
total order is the same object in every lane that has one: several outcome
coordinates, no coordinate that determines the ranking, and a scalar summary
that manufactures an order the dominance relation does not have.

## Contents

### The relation, and its order properties

* `Direction`, `ObjectiveScore`, `scoreNoWorse`, `scoreStrictlyBetter` — mirrors
  of the Agda definitions, including the `⊥` clauses for mismatched directions;
* `scoreNoWorse_of_scoreStrictlyBetter`, `scoreNoWorse_trans`,
  `scoreStrictlyBetter_irrefl` — the single-objective facts;
* `noWorse_direction` — a consequence of the `⊥` clauses that the Agda module
  does not state: two scores are comparable **only** if their directions agree,
  so the relation is not a preorder on all of `ObjectiveScore`;
* `Dominates`, with `dominates_irrefl`, `dominates_asymm`, `dominates_trans` —
  dominance is a strict order.

### Incomparability, and the cost of a scalar

* `incomparable_pair` — two admissible outcomes, neither dominating the other:
  the order is genuinely partial;
* `no_coordinate_determines_dominance` — no single objective determines the
  dominance verdict;
* `total_collides_incomparable` and `total_not_determines_outcome` — the scalar
  sum identifies the incomparable pair, so it does not determine the outcome
  vector;
* `scalarisation_invents_order` — worse: the scalar strictly orders a pair the
  dominance relation leaves incomparable.  A weighted total is therefore not a
  refinement of the Pareto order in the sense of adding information; it replaces
  a partial order by a total one and the replacement is not recorded anywhere in
  the scalar.

### The corpus's boundary record

* `separation_flags_underdetermined` — the five `Bool` fields of the Agda
  `SelectionSeparationBoundary` are free: an inhabitant asserting all of them is
  no evidence for any of them.

Nothing here is a claim about planning, environment or policy.  The carriers are
a two-element direction type and `ℕ`.
-/

namespace Integration.ParetoOutcome

open Integration.CoordinateSufficiency

/-! ## Directed objective scores -/

/-- Mirror of the Agda `Direction`: whether the objective is to be minimised or
maximised. -/
inductive Direction
  /-- Smaller values are better. -/
  | minimise
  /-- Larger values are better. -/
  | maximise
  deriving DecidableEq, Repr, Fintype

/-- Mirror of the Agda `ObjectiveScore`, keeping the two fields the comparison
uses.  The string fields of the Agda record (identifier, unit label, evidence
reference) carry no mathematical content and are omitted. -/
structure ObjectiveScore where
  /-- Whether the objective is minimised or maximised. -/
  direction : Direction
  /-- The score. -/
  value : ℕ
  deriving DecidableEq, Repr

/-- Mirror of the Agda `scoreNoWorse`, including its two `⊥` clauses. -/
def scoreNoWorse (a b : ObjectiveScore) : Prop :=
  match a.direction, b.direction with
  | .minimise, .minimise => a.value ≤ b.value
  | .maximise, .maximise => b.value ≤ a.value
  | _, _ => False

/-- Mirror of the Agda `scoreStrictlyBetter`. -/
def scoreStrictlyBetter (a b : ObjectiveScore) : Prop :=
  match a.direction, b.direction with
  | .minimise, .minimise => a.value < b.value
  | .maximise, .maximise => b.value < a.value
  | _, _ => False

/-- **Comparability forces agreement of direction.**  The Agda `⊥` clauses mean
the relation is empty across a direction mismatch, so `scoreNoWorse` is not
reflexive on pairs and not a preorder on all scores: it is a preorder on each
direction class separately.  The module does not say so. -/
theorem noWorse_direction {a b : ObjectiveScore} (h : scoreNoWorse a b) :
    a.direction = b.direction := by
  obtain ⟨da, va⟩ := a; obtain ⟨db, vb⟩ := b
  cases da <;> cases db <;> simp only [scoreNoWorse] at h <;> first | exact h.elim | rfl

theorem scoreNoWorse_refl (a : ObjectiveScore) : scoreNoWorse a a := by
  obtain ⟨da, va⟩ := a
  cases da <;> simp only [scoreNoWorse] <;> omega

theorem scoreNoWorse_of_scoreStrictlyBetter {a b : ObjectiveScore}
    (h : scoreStrictlyBetter a b) : scoreNoWorse a b := by
  obtain ⟨da, va⟩ := a; obtain ⟨db, vb⟩ := b
  cases da <;> cases db <;> simp only [scoreStrictlyBetter] at h <;>
    simp only [scoreNoWorse] <;> first | exact h.elim | omega

theorem scoreStrictlyBetter_irrefl (a : ObjectiveScore) : ¬ scoreStrictlyBetter a a := by
  obtain ⟨da, va⟩ := a
  cases da <;> intro h <;> simp only [scoreStrictlyBetter] at h <;> omega

theorem scoreNoWorse_trans {a b c : ObjectiveScore}
    (h₁ : scoreNoWorse a b) (h₂ : scoreNoWorse b c) : scoreNoWorse a c := by
  obtain ⟨da, va⟩ := a; obtain ⟨db, vb⟩ := b; obtain ⟨dc, vc⟩ := c
  cases da <;> cases db <;> cases dc <;>
    simp only [scoreNoWorse] at h₁ h₂ ⊢ <;> first | exact h₁.elim | exact h₂.elim | omega

/-- A strict improvement followed by a weak one is strict. -/
theorem scoreStrictlyBetter_of_strict_noWorse {a b c : ObjectiveScore}
    (h₁ : scoreStrictlyBetter a b) (h₂ : scoreNoWorse b c) : scoreStrictlyBetter a c := by
  obtain ⟨da, va⟩ := a; obtain ⟨db, vb⟩ := b; obtain ⟨dc, vc⟩ := c
  cases da <;> cases db <;> cases dc <;>
    simp only [scoreStrictlyBetter] at h₁ ⊢ <;> simp only [scoreNoWorse] at h₂ <;>
      first | exact h₁.elim | exact h₂.elim | omega

/-- A weak improvement cannot be reversed strictly. -/
theorem not_strict_of_noWorse {a b : ObjectiveScore}
    (h₁ : scoreNoWorse a b) (h₂ : scoreStrictlyBetter b a) : False := by
  obtain ⟨da, va⟩ := a; obtain ⟨db, vb⟩ := b
  cases da <;> cases db <;> simp only [scoreNoWorse] at h₁ <;>
    simp only [scoreStrictlyBetter] at h₂ <;> first | exact h₁.elim | exact h₂.elim | omega

/-! ## Outcome vectors and dominance -/

variable {n : ℕ}

/-- An outcome is a vector of directed scores. -/
abbrev Outcome (n : ℕ) : Type := Fin n → ObjectiveScore

/-- Mirror of the Agda `VectorNoWorse`, as a pointwise statement. -/
def NoWorse (a b : Outcome n) : Prop := ∀ i, scoreNoWorse (a i) (b i)

/-- Mirror of the Agda `SomeStrictlyBetter`. -/
def SomeStrictlyBetter (a b : Outcome n) : Prop := ∃ i, scoreStrictlyBetter (a i) (b i)

/-- Mirror of the Agda `Dominates`, with the two admissibility fields dropped:
they are `Bool` equalities on the plan record and carry no order content. -/
def Dominates (a b : Outcome n) : Prop := NoWorse a b ∧ SomeStrictlyBetter a b

theorem noWorse_refl (a : Outcome n) : NoWorse a a := fun i => scoreNoWorse_refl (a i)

theorem noWorse_trans {a b c : Outcome n} (h₁ : NoWorse a b) (h₂ : NoWorse b c) :
    NoWorse a c := fun i => scoreNoWorse_trans (h₁ i) (h₂ i)

/-- Dominance is irreflexive. -/
theorem dominates_irrefl (a : Outcome n) : ¬ Dominates a a := by
  rintro ⟨-, i, hi⟩
  exact scoreStrictlyBetter_irrefl (a i) hi

/-- Dominance is asymmetric. -/
theorem dominates_asymm {a b : Outcome n} (h : Dominates a b) : ¬ Dominates b a := by
  rintro ⟨-, i, hi⟩
  exact not_strict_of_noWorse (h.1 i) hi

/-- Dominance is transitive. -/
theorem dominates_trans {a b c : Outcome n} (h₁ : Dominates a b) (h₂ : Dominates b c) :
    Dominates a c := by
  obtain ⟨hn₁, i, hi⟩ := h₁
  refine ⟨noWorse_trans hn₁ h₂.1, ⟨i, scoreStrictlyBetter_of_strict_noWorse hi (h₂.1 i)⟩⟩

/-! ## Incomparability -/

/-- A minimised score. -/
def mo (v : ℕ) : ObjectiveScore := ⟨.minimise, v⟩

/-- A two-objective outcome, both objectives minimised. -/
def pair (x y : ℕ) : Outcome 2 := ![mo x, mo y]

@[simp] theorem pair_zero (x y : ℕ) : pair x y 0 = mo x := by simp [pair]

@[simp] theorem pair_one (x y : ℕ) : pair x y 1 = mo y := by simp [pair]

/-- **The dominance order is genuinely partial.**  Neither of these two outcomes
dominates the other: each is better on one objective. -/
theorem incomparable_pair :
    ¬ Dominates (pair 0 2) (pair 2 0) ∧ ¬ Dominates (pair 2 0) (pair 0 2) := by
  constructor
  · rintro ⟨hn, -⟩
    have h := hn 1
    simp only [pair_one, mo, scoreNoWorse] at h
    omega
  · rintro ⟨hn, -⟩
    have h := hn 0
    simp only [pair_zero, mo, scoreNoWorse] at h
    omega

/-- And dominance is not vacuous: the componentwise smaller outcome dominates. -/
theorem dominates_example : Dominates (pair 0 0) (pair 0 2) := by
  refine ⟨fun i => ?_, ⟨1, ?_⟩⟩
  · fin_cases i <;> simp [pair, mo, scoreNoWorse]
  · simp [pair, mo, scoreStrictlyBetter]

/-- **No single objective determines the dominance verdict.**  Reading only the
first objective, the dominating pair and an incomparable pair look identical. -/
theorem no_coordinate_determines_dominance :
    pair 0 0 0 = pair 0 2 0 ∧ Dominates (pair 0 0) (pair 0 2) ∧
      ¬ Dominates (pair 0 2) (pair 2 0) :=
  ⟨by simp, dominates_example, incomparable_pair.1⟩

/-! ## What a scalar summary destroys -/

/-- The unweighted total of a two-objective outcome. -/
def total (a : Outcome 2) : ℕ := (a 0).value + (a 1).value

/-- The scalar identifies the incomparable pair. -/
theorem total_collides_incomparable : total (pair 0 2) = total (pair 2 0) := by
  simp [total, mo]

/-- Hence the scalar does not determine the outcome vector: the first objective
cannot be read off the total. -/
theorem total_not_determines_outcome :
    ¬ Determines total (fun a : Outcome 2 => a 0) :=
  not_determines_of_collision (x₁ := pair 0 2) (x₂ := pair 2 0)
    total_collides_incomparable (by simp [mo])

/-- **A scalar summary invents an order.**  The dominance relation leaves this
pair incomparable in both directions, and the total strictly orders it.  The
ordering is therefore a choice made by the aggregate, not a fact about the
outcomes, and nothing in the scalar records that a choice was made. -/
theorem scalarisation_invents_order :
    ¬ Dominates (pair 1 1) (pair 0 3) ∧ ¬ Dominates (pair 0 3) (pair 1 1) ∧
      total (pair 1 1) < total (pair 0 3) := by
  refine ⟨?_, ?_, by simp [total, mo]⟩
  · rintro ⟨hn, -⟩
    have h := hn 0
    simp only [pair_zero, mo, scoreNoWorse] at h
    omega
  · rintro ⟨hn, -⟩
    have h := hn 1
    simp only [pair_one, mo, scoreNoWorse] at h
    omega

/-! ## The corpus's boundary record -/

/-- Mirror of the Agda `SelectionSeparationBoundary`: five free `Bool`s. -/
structure SelectionSeparationBoundary where
  /-- Whether MDL is declared to select explanation or model complexity. -/
  mdlSelectsExplanationOrModelComplexity : Bool
  /-- Whether Pareto is declared to select among admissible plans. -/
  paretoSelectsAmongAdmissiblePlans : Bool
  /-- Whether weights are declared not to erase reported tradeoffs. -/
  weightsDoNotEraseReportedTradeoffs : Bool
  /-- Whether infeasible plans are declared unable to dominate. -/
  infeasiblePlansCannotDominate : Bool
  /-- Whether objective units are declared to require declaration. -/
  objectiveUnitsMustBeDeclared : Bool
  deriving DecidableEq, Repr

/-- **The boundary flags are free.**  Two inhabitants agree on four fields and
disagree on the fifth, so the canonical all-`true` inhabitant of the Agda module
is a declaration and not evidence.  In particular
`weightsDoNotEraseReportedTradeoffs = true` is asserted there, while
`scalarisation_invents_order` above shows what a weighted total actually does to
a tradeoff. -/
theorem separation_flags_underdetermined :
    ∃ p q : SelectionSeparationBoundary,
      p.mdlSelectsExplanationOrModelComplexity = q.mdlSelectsExplanationOrModelComplexity ∧
        p.paretoSelectsAmongAdmissiblePlans = q.paretoSelectsAmongAdmissiblePlans ∧
          p.weightsDoNotEraseReportedTradeoffs ≠ q.weightsDoNotEraseReportedTradeoffs :=
  ⟨⟨true, true, true, true, true⟩, ⟨true, true, false, true, true⟩, rfl, rfl,
    Bool.false_ne_true.symm⟩

end Integration.ParetoOutcome
