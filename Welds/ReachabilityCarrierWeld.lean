/-
# Cross-lane weld: the chemistry decision procedure feeds the reachability carrier

Two lanes of the corpus encode reachability independently:

* `Integration.ReachabilityBarrier` — the **carrier**: an `ActionSystem` with a
  `Reachable` closure, language monotonicity
  (`reachable_of_weaker_precondition`), and the invariant route to a *negative*
  result (`not_reachable_of_invariant`).  `Integration.LanguageReachability`
  already factors through it (its `ReachableIn` is literally `Reachable` of the
  restricted system);
* `Integration.ChemistryReachability` — a **producer**: a bounded, decidable
  procedure `reachB` on a finite vertex type, proved sound and complete at a
  checkable fixpoint, but stated against `Relation.ReflTransGen (stepRel step)`
  and therefore not connected to the carrier at all.

Nothing in the corpus joined them, so the chemistry lane had no access to the
carrier's language index or to its invariant barrier, and the carrier had no
decidable producer.  This module is the weld, and it is an equivalence rather
than an analogy:

* `ofStep` — the `ActionSystem` presentation of a `Bool`-valued step relation
  (an action *is* the chosen successor vertex);
* `reachable_ofStep_iff_reflTransGen` — **the transport theorem**: the carrier's
  `Reachable (ofStep step)` and the chemistry lane's
  `Relation.ReflTransGen (stepRel step)` are the same relation;
* `reachable_ofStep_of_reachB` — hence the decidable procedure is a producer for
  the carrier: everything `reachB` accepts is `Reachable`;
* `reachB_of_reachable_ofStep_of_fixpoint` — and at the chemistry lane's own
  checkable fixpoint hypothesis the converse holds, so on saturated graphs the
  carrier relation is *decided* by `reachB`;
* `chemistry_barrier_of_invariant` — the reverse direction of reuse: the
  carrier's invariant route now refutes reachability in the chemistry lane's
  vocabulary, which that lane could not state;
* `reachB_step_not_language_relative` /
  `chemistry_language_index_available` — the language index the chemistry lane
  lacked, obtained for free by restricting `ofStep`, together with the retained
  negative: a bound-`n` acceptance is *not* a language-free fact once the
  language is narrowed.

Claim boundary unchanged from both sources: `V` is a finite label type, `step` a
`Bool`-valued relation on it.  Nothing here is about molecules, reactions or
laboratory procedure.
-/
import Integration.LanguageReachability
import Integration.ChemistryReachability

namespace Welds.ReachabilityCarrier

open Integration.ReachabilityBarrier Integration.LanguageReachability
open Integration.ChemistryReachability

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1.  The `ActionSystem` presentation of a `Bool`-valued step relation -/

/-- A `Bool`-valued step relation as an `ActionSystem` whose actions are the
chosen successor vertices. -/
def ofStep (step : V → V → Bool) : ActionSystem V V where
  Precondition := fun x a => step x a = true
  Postcondition := fun _ a y => y = a

/-! ## 2.  The transport theorem -/

omit [DecidableEq V] [Fintype V] in
/-- **The two lanes' reachability notions coincide.**  `Reachable (ofStep step)`
is `Relation.ReflTransGen (stepRel step)`. -/
theorem reachable_ofStep_iff_reflTransGen (step : V → V → Bool) (a b : V) :
    Reachable (ofStep step) a b ↔ Relation.ReflTransGen (stepRel step) a b := by
  constructor
  · intro h
    induction h with
    | refl s => exact Relation.ReflTransGen.refl
    | step c hpre hpost _ ih =>
        subst hpost
        exact Relation.ReflTransGen.head hpre ih
  · intro h
    induction h with
    | refl => exact Reachable.refl a
    | tail _ hstep ih =>
        exact reachable_trans ih
          (Reachable.step (S := ofStep step) _ hstep rfl (Reachable.refl _))

/-! ## 3.  The chemistry procedure as a carrier producer -/

/-- **Producer.**  Everything the bounded decision procedure accepts is
`Reachable` in the carrier. -/
theorem reachable_ofStep_of_reachB (step : V → V → Bool) (n : ℕ) (a b : V)
    (h : reachB step n a b = true) : Reachable (ofStep step) a b :=
  (reachable_ofStep_iff_reflTransGen step a b).2 (reachB_sound step n a b h)

/-- **Decision, at the lane's own fixpoint hypothesis.**  Where one further
iteration accepts nothing new, `reachB` decides the carrier relation. -/
theorem reachB_of_reachable_ofStep_of_fixpoint (step : V → V → Bool) (n : ℕ)
    (hfix : ∀ x y : V, reachB step (n + 1) x y = reachB step n x y) (a b : V)
    (h : Reachable (ofStep step) a b) : reachB step n a b = true :=
  reachB_complete_of_fixpoint step n hfix ((reachable_ofStep_iff_reflTransGen step a b).1 h)

/-- Consequently, on a saturated graph the carrier relation is decidable by
kernel computation, which is what the chemistry socket's soundness hypothesis
needs. -/
theorem reachable_ofStep_iff_reachB_of_fixpoint (step : V → V → Bool) (n : ℕ)
    (hfix : ∀ x y : V, reachB step (n + 1) x y = reachB step n x y) (a b : V) :
    Reachable (ofStep step) a b ↔ reachB step n a b = true :=
  ⟨reachB_of_reachable_ofStep_of_fixpoint step n hfix a b,
   reachable_ofStep_of_reachB step n a b⟩

/-! ## 4.  Reverse reuse: the carrier's barrier, in the chemistry vocabulary -/

omit [DecidableEq V] [Fintype V] in
/-- **The invariant barrier, transported.**  An invariant preserved by every
`step`-edge, true at `a` and false at `b`, refutes `ReflTransGen` reachability —
the negative route the chemistry lane had no way to state, obtained from the
carrier rather than re-proved. -/
theorem chemistry_barrier_of_invariant (step : V → V → Bool) (P : V → Prop)
    (hpres : ∀ x y, step x y = true → P x → P y) {a b : V} (ha : P a) (hb : ¬ P b) :
    ¬ Relation.ReflTransGen (stepRel step) a b := fun h =>
  not_reachable_of_invariant (S := ofStep step) P
    (fun x c _ hpre hpost hx => hpost ▸ hpres x c hpre hx) ha hb
    ((reachable_ofStep_iff_reflTransGen step a b).2 h)

/-- …and therefore the procedure must reject such a pair, at every bound. -/
theorem reachB_false_of_invariant (step : V → V → Bool) (P : V → Prop)
    (hpres : ∀ x y, step x y = true → P x → P y) {a b : V} (ha : P a) (hb : ¬ P b) (n : ℕ) :
    reachB step n a b = false := by
  rcases Bool.eq_false_or_eq_true (reachB step n a b) with h | h
  · exact absurd (reachB_sound step n a b h) (chemistry_barrier_of_invariant step P hpres ha hb)
  · exact h

/-! ## 5.  The language index, for free -/

/-- The chemistry lane inherits the language index: reachability of the same
graph under a declared sub-language of edges. -/
def ReachableInLanguage (step : V → V → Bool) (L : V → Prop) (a b : V) : Prop :=
  ReachableIn (ofStep step) L a b

omit [DecidableEq V] [Fintype V] in
/-- Language monotonicity for the chemistry lane, inherited from the carrier. -/
theorem chemistry_language_index_available (step : V → V → Bool) {L₁ L₂ : V → Prop}
    (hL : ∀ a, L₁ a → L₂ a) {a b : V} (h : ReachableInLanguage step L₁ a b) :
    ReachableInLanguage step L₂ a b := reachableIn_mono hL h

/-- **The retained negative.**  Acceptance by the unrestricted procedure does
*not* give reachability in a narrowed language: on the two-vertex graph with the
single edge `0 → 1`, the empty language reaches nothing new. -/
theorem reachB_accept_not_language_free :
    ∃ (step : Fin 2 → Fin 2 → Bool) (L : Fin 2 → Prop) (a b : Fin 2),
      reachB step 1 a b = true ∧ ¬ ReachableInLanguage step L a b := by
  refine ⟨fun x y => x = 0 && y = 1, fun _ => False, 0, 1, by decide, ?_⟩
  intro h
  cases h with
  | step a hpre _ _ => exact hpre.1

end Welds.ReachabilityCarrier
