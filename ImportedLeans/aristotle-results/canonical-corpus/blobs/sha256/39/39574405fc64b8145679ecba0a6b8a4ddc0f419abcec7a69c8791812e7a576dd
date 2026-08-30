import Integration.ReachabilityBarrier

/-!
# Language-indexed reachability

`Integration.ReachabilityBarrier` mirrors the corpus's `Reachable` and proves
that enlarging the admissible transitions can only add reachable pairs.  The
recurring Level-II shape needs one more index: the same underlying dynamics
examined under **different declared action languages**, so that a reachability
claim carries the language it is relative to.

This file adds that index without introducing a second reachability notion: the
language is applied to the existing `ActionSystem` as a restriction of its
precondition, and `Reachable_L` is *defined* as the existing `Reachable` of the
restricted system.

## Contents

* `restrict`, `ReachableIn` — the language index;
* `reachableIn_mono` — **`L₁ ⊆ L₂` and `Reachable_{L₁} x y` give
  `Reachable_{L₂} x y`**, with the language inclusion an explicit hypothesis;
* `reachableIn_trans`, `reachableIn_step` — the usual closure properties;
* `notReachable_not_antitone` — **the negative that is retained**:
  `¬ Reachable_{L₁} x y` does *not* give `¬ Reachable_{L₂} x y`.  A barrier is a
  statement about a language, never about the states alone;
* `not_reachableIn_of_invariant` — the only general route to a barrier: an
  invariant preserved by every action *in the declared language*;
* `barrier_needs_the_language` — and the invariant route itself is
  language-relative: the same invariant argument fails verbatim once the
  language grows;
* `counterLanguages` — the witness: a counter with a two-step and a one-step
  action, unreachable target under the restricted language and reachable under
  the full one;
* `barrier_report` — the packaged honest report of a barrier: the language, the
  invariant, the proof, and the explicit statement that no claim is made for any
  larger language.

The carriers are `ℕ` and `Bool`.  Nothing here is a claim about capability,
planning, development or any process.
-/

namespace Integration.LanguageReachability

open Integration.ReachabilityBarrier

variable {State Action : Type}

/-! ## The language index -/

/-- The system `S` restricted to the actions the language `L` admits. -/
def restrict (S : ActionSystem State Action) (L : Action → Prop) :
    ActionSystem State Action where
  Precondition := fun x a => L a ∧ S.Precondition x a
  Postcondition := S.Postcondition

/-- **Language-indexed reachability**: reachability of the system restricted to
the declared language.  This is the existing `Reachable`, not a new relation. -/
def ReachableIn (S : ActionSystem State Action) (L : Action → Prop) (x y : State) : Prop :=
  Reachable (restrict S L) x y

theorem reachableIn_refl (S : ActionSystem State Action) (L : Action → Prop) (x : State) :
    ReachableIn S L x x := Reachable.refl x

theorem reachableIn_trans {S : ActionSystem State Action} {L : Action → Prop}
    {x y z : State} (h₁ : ReachableIn S L x y) (h₂ : ReachableIn S L y z) :
    ReachableIn S L x z := reachable_trans h₁ h₂

/-- One admissible step of the declared language. -/
theorem reachableIn_step {S : ActionSystem State Action} {L : Action → Prop}
    {x y z : State} (a : Action) (ha : L a) (hpre : S.Precondition x a)
    (hpost : S.Postcondition x a y) (rest : ReachableIn S L y z) : ReachableIn S L x z :=
  Reachable.step (S := restrict S L) a (show L a ∧ S.Precondition x a from ⟨ha, hpre⟩)
    (show S.Postcondition x a y from hpost) rest

/-! ## Monotonicity in the language -/

/-- **Enlarging the declared language only adds reachable pairs.**  The language
inclusion is an explicit hypothesis and is never assumed silently. -/
theorem reachableIn_mono {S : ActionSystem State Action} {L₁ L₂ : Action → Prop}
    (hL : ∀ a, L₁ a → L₂ a) {x y : State} (h : ReachableIn S L₁ x y) :
    ReachableIn S L₂ x y :=
  reachable_of_weaker_precondition (S := restrict S L₁) (T := restrict S L₂)
    (fun x a (hp : L₁ a ∧ S.Precondition x a) =>
      show L₂ a ∧ S.Precondition x a from ⟨hL a hp.1, hp.2⟩)
    (fun _ _ _ hq => hq) h

/-- Positive reachability facts therefore transfer up the language order… -/
theorem reachableIn_of_subset {S : ActionSystem State Action} {L₁ L₂ : Action → Prop}
    (hL : ∀ a, L₁ a → L₂ a) : ∀ x y, ReachableIn S L₁ x y → ReachableIn S L₂ x y :=
  fun _ _ => reachableIn_mono hL

/-! ## The invariant route to a barrier -/

/-- **The only general route to unreachability.**  An invariant preserved by
every action the *declared language* admits, true at the source and false at the
target. -/
theorem not_reachableIn_of_invariant {S : ActionSystem State Action} {L : Action → Prop}
    (P : State → Prop)
    (hstep : ∀ x a y, L a → S.Precondition x a → S.Postcondition x a y → P x → P y)
    {x y : State} (hx : P x) (hy : ¬ P y) : ¬ ReachableIn S L x y :=
  not_reachable_of_invariant (S := restrict S L) P
    (fun u a v (hpre : L a ∧ S.Precondition u a) hpost hu =>
      hstep u a v hpre.1 hpre.2 hpost hu) hx hy

/-! ## The witness -/

/-- The counter system with both actions available at the level of the
postcondition; the language decides which may be used. -/
def counterSystem : ActionSystem ℕ Bool where
  Precondition := fun _ _ => True
  Postcondition := fun x a y => y = x + stepSize a

/-- The restricted language: only the two-step action. -/
def evenOnly : Bool → Prop := fun a => a = false

/-- The full language. -/
def allActions : Bool → Prop := fun _ => True

theorem evenOnly_subset_all : ∀ a, evenOnly a → allActions a := fun _ _ => trivial

/-- Under the restricted language evenness is an invariant. -/
theorem even_invariant_evenOnly (x : ℕ) (a : Bool) (y : ℕ) (ha : evenOnly a)
    (_hpre : True) (hpost : y = x + stepSize a) (hx : x % 2 = 0) : y % 2 = 0 := by
  subst hpost
  cases a
  · simp only [stepSize]; omega
  · exact absurd ha (by simp [evenOnly])

/-- **Unreachable under the restricted language.** -/
theorem not_reachable_evenOnly : ¬ ReachableIn counterSystem evenOnly 0 3 := by
  refine not_reachableIn_of_invariant (fun n => n % 2 = 0) ?_ (by norm_num) (by norm_num)
  intro x a y ha hpre hpost hx
  exact even_invariant_evenOnly x a y ha hpre hpost hx

/-- **Reachable under the full language.** -/
theorem reachable_allActions : ReachableIn counterSystem allActions 0 3 := by
  refine reachableIn_step true trivial trivial (y := 1) rfl ?_
  refine reachableIn_step false trivial trivial (y := 3) rfl ?_
  exact reachableIn_refl _ _ _

/-- **The retained negative.**  Language inclusion transports reachability
upwards, and transports *un*reachability nowhere: here the same pair is
unreachable in the smaller language and reachable in the larger one.  So a
barrier is never a property of the states. -/
theorem notReachable_not_antitone :
    (∀ a, evenOnly a → allActions a) ∧
      ¬ ReachableIn counterSystem evenOnly 0 3 ∧
      ReachableIn counterSystem allActions 0 3 :=
  ⟨evenOnly_subset_all, not_reachable_evenOnly, reachable_allActions⟩

/-- Stated as the failure of the implication a reader might expect. -/
theorem unreachability_does_not_transfer :
    ¬ (∀ (S : ActionSystem ℕ Bool) (L₁ L₂ : Bool → Prop), (∀ a, L₁ a → L₂ a) →
        ∀ x y, ¬ ReachableIn S L₁ x y → ¬ ReachableIn S L₂ x y) := by
  intro h
  exact h counterSystem evenOnly allActions evenOnly_subset_all 0 3
    not_reachable_evenOnly reachable_allActions

/-- **The invariant argument is itself language-relative.**  Evenness is
preserved by every action of the restricted language and not by every action of
the full one, so the barrier proof does not survive the extension either. -/
theorem barrier_needs_the_language :
    (∀ x a y, evenOnly a → counterSystem.Postcondition x a y → x % 2 = 0 → y % 2 = 0) ∧
      ¬ (∀ x a y, allActions a → counterSystem.Postcondition x a y → x % 2 = 0 →
          y % 2 = 0) := by
  constructor
  · intro x a y ha hpost hx
    exact even_invariant_evenOnly x a y ha trivial hpost hx
  · intro h
    have := h 0 true 1 trivial (by simp [counterSystem, stepSize]) (by norm_num)
    omega

/-! ## The honest form of a barrier claim -/

/-- A barrier report: the declared language, the invariant, and the proof.  The
record cannot be built without the proof, and it says nothing about any other
language — which is the whole point of carrying the language in the type. -/
structure BarrierReport (S : ActionSystem State Action) (x y : State) where
  /-- The declared action language the barrier is relative to. -/
  language : Action → Prop
  /-- The invariant used. -/
  invariant : State → Prop
  /-- It is preserved by every action of the declared language. -/
  preserved : ∀ u a v, language a → S.Precondition u a → S.Postcondition u a v →
    invariant u → invariant v
  /-- It holds at the source. -/
  atSource : invariant x
  /-- It fails at the target. -/
  atTarget : ¬ invariant y

/-- A barrier report proves exactly the language-relative statement, and
`unreachability_does_not_transfer` shows it proves nothing more. -/
theorem BarrierReport.not_reachable {S : ActionSystem State Action} {x y : State}
    (r : BarrierReport S x y) : ¬ ReachableIn S r.language x y :=
  not_reachableIn_of_invariant r.invariant r.preserved r.atSource r.atTarget

/-- The witness as a report. -/
def counterBarrier : BarrierReport counterSystem 0 3 where
  language := evenOnly
  invariant := fun n => n % 2 = 0
  preserved := fun u a v ha hpre hpost hu => even_invariant_evenOnly u a v ha hpre hpost hu
  atSource := by norm_num
  atTarget := by norm_num

end Integration.LanguageReachability
