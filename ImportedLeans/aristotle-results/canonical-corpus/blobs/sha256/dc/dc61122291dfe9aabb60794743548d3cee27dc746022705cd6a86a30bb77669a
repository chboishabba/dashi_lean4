import Mathlib
import Integration.ChemistryKernelSocket

/-!
# Discharging the chemistry candidate bridge

`Integration.ChemistryKernelSocket` files the corpus's reachability flag as an
**open socket** (`goalReachable_underdetermined`: the flag is a free `Bool`, not
a function of the transition system) and offers a **candidate bridge**
(`flag_determined_of_sound`: given a decision procedure the flag is sound for,
the flag *is* determined).  `flagSound_not_automatic` shows the hypothesis is
not free.

This file supplies the missing side.  It gives

* a genuine bounded reachability procedure `reachB` on a finite state type,
* a soundness theorem (`reachB_sound`) and a completeness theorem at a
  **checkable fixpoint hypothesis** (`reachB_complete_of_fixpoint`), so the
  procedure is proved to decide reflexive-transitive reachability exactly when
  one extra iteration adds nothing — a condition that is `decide`-able for any
  concrete finite graph,
* a concrete four-state graph on which the fixpoint hypothesis is discharged by
  kernel computation (`cstepSaturates`), together with a positive and a
  **negative** reachability witness,
* and hence `chemistryFlagSound`, an actual inhabitant of
  `ChemistryKernelSocket.FlagSound`, which upgrades the candidate bridge to
  `chemistryFlag_determined` on the class of correctly-populated problems.

## Claim boundary

`V` is a finite label type and `step` is a `Bool`-valued relation on it.
Nothing here is about molecules, reactions, chemical species or laboratory
procedure; the words "reachability" and "transition system" are used in their
graph-theoretic sense only.  The corpus's own flag remains underdetermined: what
is proved is that *if* a problem is populated so that its flag agrees with
reachability, *then* the flag is a function of the system — and that the class
of such problems is non-empty, because the procedure exists and is correct.
-/

namespace Integration.ChemistryReachability

open Integration.ChemistryKernelSocket

/-! ## A bounded reachability procedure -/

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The one-step relation induced by a `Bool`-valued step function. -/
abbrev stepRel (step : V → V → Bool) : V → V → Prop := fun a b => step a b = true

/-- `reachB step n a b` is `true` when `b` is reachable from `a` in at most `n`
steps.  Decidable by construction. -/
def reachB (step : V → V → Bool) : ℕ → V → V → Bool
  | 0, a, b => a == b
  | (n + 1), a, b =>
      (a == b) || decide (∃ c : V, step a c = true ∧ reachB step n c b = true)

@[simp] theorem reachB_zero (step : V → V → Bool) (a b : V) :
    reachB step 0 a b = (a == b) := rfl

theorem reachB_succ (step : V → V → Bool) (n : ℕ) (a b : V) :
    reachB step (n + 1) a b =
      ((a == b) || decide (∃ c : V, step a c = true ∧ reachB step n c b = true)) := rfl

/-- The procedure always sees the empty path. -/
theorem reachB_refl (step : V → V → Bool) (n : ℕ) (a : V) : reachB step n a a = true := by
  cases n with
  | zero => simp
  | succ n => simp [reachB_succ]

/-- **Soundness.**  Anything the procedure accepts really is reachable. -/
theorem reachB_sound (step : V → V → Bool) :
    ∀ (n : ℕ) (a b : V), reachB step n a b = true → Relation.ReflTransGen (stepRel step) a b := by
  intro n
  induction n with
  | zero =>
      intro a b h
      simp only [reachB_zero, beq_iff_eq] at h
      exact h ▸ Relation.ReflTransGen.refl
  | succ n ih =>
      intro a b h
      rw [reachB_succ, Bool.or_eq_true] at h
      rcases h with h | h
      · simp only [beq_iff_eq] at h
        exact h ▸ Relation.ReflTransGen.refl
      · obtain ⟨c, hc, hcb⟩ := of_decide_eq_true h
        exact Relation.ReflTransGen.head hc (ih c b hcb)

/-- One more iteration never accepts less. -/
theorem reachB_mono (step : V → V → Bool) :
    ∀ (n : ℕ) (a b : V), reachB step n a b = true → reachB step (n + 1) a b = true := by
  intro n
  induction n with
  | zero =>
      intro a b h
      simp only [reachB_zero, beq_iff_eq] at h
      subst h
      exact reachB_refl step 1 a
  | succ n ih =>
      intro a b h
      rw [reachB_succ, Bool.or_eq_true] at h
      rcases h with h | h
      · rw [reachB_succ, h, Bool.true_or]
      · obtain ⟨c, hc, hcb⟩ := of_decide_eq_true h
        rw [reachB_succ, Bool.or_eq_true]
        exact Or.inr (decide_eq_true ⟨c, hc, ih c b hcb⟩)

/-- **Completeness at a fixpoint.**  If one further iteration accepts nothing
new, the procedure has already found every reachable pair.  The hypothesis is a
finite `Bool` identity, so it is `decide`-able for any concrete graph. -/
theorem reachB_complete_of_fixpoint (step : V → V → Bool) (n : ℕ)
    (hfix : ∀ a b : V, reachB step (n + 1) a b = reachB step n a b)
    {a b : V} (h : Relation.ReflTransGen (stepRel step) a b) :
    reachB step n a b = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact reachB_refl step n b
  | head hac _ ih =>
      rename_i x c _
      have : reachB step (n + 1) x b = true := by
        rw [reachB_succ, Bool.or_eq_true]
        exact Or.inr (decide_eq_true ⟨c, hac, ih⟩)
      rwa [hfix] at this

/-- At a fixpoint the procedure **decides** reachability. -/
theorem reachB_iff_of_fixpoint (step : V → V → Bool) (n : ℕ)
    (hfix : ∀ a b : V, reachB step (n + 1) a b = reachB step n a b) (a b : V) :
    reachB step n a b = true ↔ Relation.ReflTransGen (stepRel step) a b :=
  ⟨reachB_sound step n a b, reachB_complete_of_fixpoint step n hfix⟩

/-! ## A concrete finite transition system -/

/-- The transition-system datum: a step relation with a start and a goal. -/
structure FiniteTS (V : Type) where
  /-- The one-step relation. -/
  step : V → V → Bool
  /-- The start state. -/
  start : V
  /-- The goal state. -/
  goal : V

/-- Reachability of the goal from the start, as a proposition. -/
def TSReach (t : FiniteTS V) : Prop :=
  Relation.ReflTransGen (stepRel t.step) t.start t.goal

/-- A four-state graph: a three-cycle `0 → 1 → 2 → 0` together with an isolated
state `3`. -/
def cstep : Fin 4 → Fin 4 → Bool
  | 0, 1 => true
  | 1, 2 => true
  | 2, 0 => true
  | _, _ => false

/-- **The checkable hypothesis, discharged.**  Three iterations already saturate
this graph, so `reachB cstep 3` decides its reachability. -/
theorem cstepSaturates : ∀ a b : Fin 4, reachB cstep 4 a b = reachB cstep 3 a b := by
  decide

/-- Hence the procedure decides reachability on this graph. -/
theorem cstep_reach_iff (a b : Fin 4) :
    reachB cstep 3 a b = true ↔ Relation.ReflTransGen (stepRel cstep) a b :=
  reachB_iff_of_fixpoint cstep 3 cstepSaturates a b

/-- A positive witness: the far side of the cycle is reachable. -/
theorem cstep_reaches_two : Relation.ReflTransGen (stepRel cstep) 0 2 :=
  (cstep_reach_iff 0 2).mp (by decide)

/-- **A negative witness, as a first-class result**: the isolated state is not
reachable.  This is a genuine non-reachability proof, not an unset flag. -/
theorem cstep_not_reaches_three : ¬ Relation.ReflTransGen (stepRel cstep) 0 3 := by
  intro h
  have : reachB cstep 3 0 3 = true := (cstep_reach_iff 0 3).mpr h
  exact absurd this (by decide)

/-! ## Discharging the bridge -/

/-- The decision procedure, packaged as the `reach : S → Bool` the socket asks
for, with `S := FiniteTS (Fin 4)`. -/
def chemistryReach (t : FiniteTS (Fin 4)) : Bool := reachB t.step 3 t.start t.goal

/-- The class of **correctly populated** problems: those on the concrete graph
whose `goalReachable` flag really does record reachability. -/
def CorrectlyPopulated (p : ReachabilityProblem (FiniteTS (Fin 4))) : Prop :=
  p.transitionSystem.step = cstep ∧ (p.goalReachable = true ↔ TSReach p.transitionSystem)

/-- **The bridge's hypothesis, supplied.**  On correctly populated problems the
flag agrees with the decision procedure. -/
theorem chemistryFlagSound : FlagSound chemistryReach CorrectlyPopulated := by
  rintro p ⟨hstep, hflag⟩
  have hiff : chemistryReach p.transitionSystem = true ↔ TSReach p.transitionSystem := by
    unfold chemistryReach TSReach
    rw [hstep]
    exact cstep_reach_iff _ _
  cases hgr : p.goalReachable with
  | true =>
      have := hflag.mp hgr
      exact (hiff.mpr this).symm
  | false =>
      cases hcr : chemistryReach p.transitionSystem with
      | true => exact absurd (hflag.mpr (hiff.mp hcr)) (by rw [hgr]; exact Bool.noConfusion)
      | false => rfl

/-- **The candidate bridge, discharged.**  On correctly populated problems the
reachability flag is a function of the transition system — no longer a free
`Bool`. -/
theorem chemistryFlag_determined {p q : ReachabilityProblem (FiniteTS (Fin 4))}
    (hp : CorrectlyPopulated p) (hq : CorrectlyPopulated q)
    (hs : p.transitionSystem = q.transitionSystem) :
    p.goalReachable = q.goalReachable :=
  flag_determined_of_sound chemistryFlagSound hp hq hs

/-- The class is non-empty, so the bridge is not vacuous: here is a correctly
populated problem whose flag is `true`, and one whose flag is `false`. -/
theorem correctlyPopulated_nonempty :
    CorrectlyPopulated ⟨⟨cstep, 0, 2⟩, true, true, true⟩ ∧
    CorrectlyPopulated ⟨⟨cstep, 0, 3⟩, false, true, true⟩ := by
  refine ⟨⟨rfl, ⟨fun _ => cstep_reaches_two, fun _ => rfl⟩⟩, ⟨rfl, ?_⟩⟩
  exact ⟨fun h => absurd h Bool.noConfusion, fun h => absurd h cstep_not_reaches_three⟩

/-- And the socket is still a socket: an *incorrectly* populated problem on the
same system carries the opposite flag, so the determination genuinely needs the
class restriction. -/
theorem correctness_restriction_is_needed :
    ∃ p q : ReachabilityProblem (FiniteTS (Fin 4)),
      p.transitionSystem = q.transitionSystem ∧
      CorrectlyPopulated p ∧ ¬ CorrectlyPopulated q ∧
      p.goalReachable ≠ q.goalReachable :=
  ⟨⟨⟨cstep, 0, 2⟩, true, true, true⟩, ⟨⟨cstep, 0, 2⟩, false, true, true⟩, rfl,
   ⟨rfl, ⟨fun _ => cstep_reaches_two, fun _ => rfl⟩⟩,
   (by
     rintro ⟨-, hiff⟩
     exact absurd (hiff.mpr cstep_reaches_two) Bool.noConfusion),
   Bool.noConfusion⟩

end Integration.ChemistryReachability
