import Integration.Kernel.Quotient

/-!
# Weld: situated mediation, with two carriers rather than one generic witness

The generic statement "the same global input does not determine the local
result" already exists in this kernel as a finite witness
(`Integration.Kernel.Instances.SituatedValuation`, for word meaning).  A generic
witness, though, only shows the shape is inhabited.  This file makes mediation
an **interface** with a proof obligation and instantiates it twice, on carriers
from two different donor lanes:

* a **process-integration** carrier — one global recipe, several local
  geometries, different realised local results;
* a **situated-effect** carrier of the social/legal kind — one global rule,
  several situations, different realised local effects.

It then proves the two instances are *not* relabellings of one another, which
is the reason to keep them as separate carriers of a shared interface rather
than to collapse them into a single abstraction.

## What is proved

* `Mediates` — the interface: an effect map `G → S → E` together with the
  obligation that some global input has two situations with different effects.
  `Mediates.effect_does_not_descend_through_global` derives the non-descent
  generically, so any instance inherits it.
* `processMediates`, `ruleMediates` — both carriers discharge the obligation.
* `process_pair_is_the_right_index`, `rule_pair_is_the_right_index` — in both,
  the (global, situation) pair does determine the effect: mediation refines the
  global reading, it does not contradict it.
* **`carriers_are_not_relabellings`** — there is no pair of maps (situations to
  situations, outcomes to outcomes with the outcome map injective) carrying the
  process carrier onto the rule carrier: the process carrier separates three
  local results where the rule carrier has only two outcomes.  The two
  instances share the interface and nothing more.

**Claim boundary.**  Recipes, geometries, rules, situations and outcomes are
finite labels stipulated in this file, and each effect table is a definition,
not a measurement.  Nothing here is an empirical claim about any fabrication
process, and nothing is a claim about any legal system, case or institution.
-/

namespace Integration.Kernel.Welds.SituatedMediationCarriers

open Integration.Kernel.Quotient

/-! ## §1 The interface -/

/-- A mediating carrier: a global input, a situation, a local effect, and the
obligation that the global input alone does not fix the effect. -/
structure Mediates (G S E : Type) where
  /-- The realised local effect of a global input in a situation. -/
  effect : G → S → E
  /-- Some global input is mediated: two situations, two different effects. -/
  mediated : ∃ (g : G) (s s' : S), effect g s ≠ effect g s'

namespace Mediates

variable {G S E : Type}

/-- **The global input does not determine the local effect**, for any instance
of the interface. -/
theorem effect_does_not_descend_through_global (M : Mediates G S E) :
    ¬ DescendsThrough (fun p : G × S => M.effect p.1 p.2) (fun p : G × S => p.1) := by
  obtain ⟨g, s, s', h⟩ := M.mediated
  exact not_descendsThrough_of_collision (x := (g, s)) (y := (g, s')) rfl h

/-- And the pair does determine it: mediation is a refinement of the global
reading, not a refutation of it. -/
theorem effect_descends_through_pair (M : Mediates G S E) :
    DescendsThrough (fun p : G × S => M.effect p.1 p.2) id :=
  ⟨fun p => M.effect p.1 p.2, fun _ => rfl⟩

end Mediates

/-! ## §2 Carrier I: process integration -/

/-- A global process recipe. -/
inductive Recipe : Type
  /-- The nominal recipe. -/
  | nominal
  /-- The recipe with the step extended. -/
  | extended
  deriving DecidableEq, Repr

/-- The local geometry the same recipe meets. -/
inductive Geometry : Type
  /-- An open planar area. -/
  | planar
  /-- A narrow trench. -/
  | trench
  /-- A re-entrant corner. -/
  | reentrant
  deriving DecidableEq, Repr

/-- The realised local result, as a stipulated finite label. -/
inductive LocalResult : Type
  /-- The intended local result. -/
  | onTarget
  /-- Less than intended. -/
  | thin
  /-- More than intended. -/
  | thick
  deriving DecidableEq, Repr

/-- The stipulated process table: the same recipe realises differently in
different local geometries. -/
def processEffect : Recipe → Geometry → LocalResult
  | .nominal, .planar => .onTarget
  | .nominal, .trench => .thin
  | .nominal, .reentrant => .thick
  | .extended, .planar => .thick
  | .extended, .trench => .onTarget
  | .extended, .reentrant => .thick

/-- The process carrier is a mediating carrier. -/
def processMediates : Mediates Recipe Geometry LocalResult where
  effect := processEffect
  mediated := ⟨.nominal, .planar, .trench, by decide⟩

/-- The process carrier's non-descent, inherited from the interface. -/
theorem process_effect_does_not_descend_through_recipe :
    ¬ DescendsThrough (fun p : Recipe × Geometry => processEffect p.1 p.2)
        (fun p : Recipe × Geometry => p.1) :=
  processMediates.effect_does_not_descend_through_global

theorem process_pair_is_the_right_index :
    DescendsThrough (fun p : Recipe × Geometry => processEffect p.1 p.2) id :=
  processMediates.effect_descends_through_pair

/-- Under the nominal recipe the three geometries realise three different local
results. -/
theorem process_separates_three :
    processEffect .nominal .planar ≠ processEffect .nominal .trench ∧
      processEffect .nominal .planar ≠ processEffect .nominal .reentrant ∧
        processEffect .nominal .trench ≠ processEffect .nominal .reentrant := by decide

/-! ## §3 Carrier II: a situated social/legal effect -/

/-- A global rule. -/
inductive Rule : Type
  /-- The rule as written. -/
  | asWritten
  /-- The rule with an exception attached. -/
  | withException
  deriving DecidableEq, Repr

/-- The situation the same rule meets. -/
inductive Situation : Type
  /-- The situation the rule was drafted for. -/
  | typical
  /-- A situation with a competing prior obligation. -/
  | competingObligation
  /-- A situation where the addressee cannot comply. -/
  | unableToComply
  deriving DecidableEq, Repr

/-- The realised local effect, as a stipulated finite label. -/
inductive Effect : Type
  /-- The rule bites. -/
  | binds
  /-- The rule does not bite. -/
  | inoperative
  deriving DecidableEq, Repr

/-- The stipulated situated-effect table. -/
def ruleEffect : Rule → Situation → Effect
  | .asWritten, .typical => .binds
  | .asWritten, .competingObligation => .binds
  | .asWritten, .unableToComply => .inoperative
  | .withException, .typical => .binds
  | .withException, .competingObligation => .inoperative
  | .withException, .unableToComply => .inoperative

/-- The rule carrier is a mediating carrier. -/
def ruleMediates : Mediates Rule Situation Effect where
  effect := ruleEffect
  mediated := ⟨.asWritten, .typical, .unableToComply, by decide⟩

theorem rule_effect_does_not_descend_through_rule :
    ¬ DescendsThrough (fun p : Rule × Situation => ruleEffect p.1 p.2)
        (fun p : Rule × Situation => p.1) :=
  ruleMediates.effect_does_not_descend_through_global

theorem rule_pair_is_the_right_index :
    DescendsThrough (fun p : Rule × Situation => ruleEffect p.1 p.2) id :=
  ruleMediates.effect_descends_through_pair

/-! ## §4 The two carriers are not relabellings of one another -/

/-- In a two-valued outcome type, three elements cannot be pairwise distinct. -/
theorem two_of_three_eq (a b c : Effect) : a = b ∨ a = c ∨ b = c := by
  cases a <;> cases b <;> cases c <;> simp

/-- **Shared interface, different carriers.**  No relabelling of situations
together with an injective relabelling of outcomes carries the nominal process
row onto a rule row: the process carrier separates three local results and the
rule carrier has only two effects. -/
theorem carriers_are_not_relabellings :
    ¬ ∃ (r : Rule) (phi : Geometry → Situation) (psi : LocalResult → Effect),
        Function.Injective psi ∧
          ∀ g : Geometry, ruleEffect r (phi g) = psi (processEffect .nominal g) := by
  rintro ⟨r, phi, psi, hpsi, hcomm⟩
  have h1 := hcomm .planar
  have h2 := hcomm .trench
  have h3 := hcomm .reentrant
  rcases two_of_three_eq (ruleEffect r (phi .planar)) (ruleEffect r (phi .trench))
      (ruleEffect r (phi .reentrant)) with h | h | h
  · have hEq : processEffect .nominal .planar = processEffect .nominal .trench :=
      hpsi (by rw [← h1, ← h2]; exact h)
    exact absurd hEq (by decide)
  · have hEq : processEffect .nominal .planar = processEffect .nominal .reentrant :=
      hpsi (by rw [← h1, ← h3]; exact h)
    exact absurd hEq (by decide)
  · have hEq : processEffect .nominal .trench = processEffect .nominal .reentrant :=
      hpsi (by rw [← h2, ← h3]; exact h)
    exact absurd hEq (by decide)

/-- Both carriers do inhabit the interface, which is the positive half of the
same statement. -/
theorem both_carriers_mediate :
    (∃ _ : Mediates Recipe Geometry LocalResult, True) ∧
      (∃ _ : Mediates Rule Situation Effect, True) :=
  ⟨⟨processMediates, trivial⟩, ⟨ruleMediates, trivial⟩⟩

end Integration.Kernel.Welds.SituatedMediationCarriers
