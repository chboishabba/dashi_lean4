import Integration.Kernel.Loop

/-!
# Weld: deliberative moves as constructors of the existing action loop

`Integration.Kernel.Loop` already has a move type — `refineMove` and
`mergeMove` — and an adaptive rule choosing between them.  The deliberative
vocabulary (*ask*, *listen*, *reformulate*) was floating beside it as a separate
list of words.  This file makes the vocabulary an **extension of that move
type**, with a semantics on the same residual fibre, and proves what the extra
moves do that a probe cannot.

## What is proved

* `EpistemicMove`, `search` — the extension.  `search_injective` and
  `ask_is_not_a_search_move` (with its two companions) show the embedding of the
  existing moves is injective and proper: the deliberative moves are genuinely
  new constructors, not renamings.
* `strategyE`, **`strategyE_extends_strategy`** — the existing adaptive rule is
  recovered exactly by composing with the embedding, so the extension is
  conservative: nothing the loop already decided changes.
* `act` — the semantics on an `Inquiry` (a live fibre together with the
  consumer coordinate in play).  `search_refines`, `ask_refines`,
  `listen_refines` — all three narrowing moves refine the fibre, and
  `reformulate_preserves_fibre` — reformulation does not.
* **`listening_can_do_what_no_probe_can`** — the substantive one.  There is an
  inquiry on which the policy's channel is constant, so every `search` step
  leaves the fibre unchanged, and yet `listen` strictly narrows it.  Uptake from
  another inquirer is not a special case of probing.
* **`reformulation_can_close_without_narrowing`** — dually, `reformulate` leaves
  the fibre exactly as it was and turns an undetermined consumer coordinate into
  a determined one: the question closes without any new observation.  This is
  `Integration.Kernel.Loop.closure_is_consumer_relative` acquiring a move.
* `the_four_moves_are_not_interchangeable` — on one inquiry the four moves have
  pairwise distinct effects.

**Claim boundary.**  An `Inquiry` is a subset of a carrier together with a
function out of it; "ask", "listen" and "reformulate" are names for three
stipulated operations on that pair.  Nothing models an actual dialogue,
interlocutor or speech act.
-/

namespace Integration.Kernel.Welds.DeliberativeMoves

open Set Integration.Kernel.ResidualFibre Integration.Kernel.Loop

/-! ## §1 The extended move type -/

/-- The moves of the loop, extended by the deliberative ones. -/
inductive EpistemicMove : Type
  /-- One of the existing search moves. -/
  | search (m : Move)
  /-- Put a question to another inquirer and take the reply as an event. -/
  | ask
  /-- Take up another inquirer's live fibre. -/
  | listen
  /-- Change the consumer coordinate the inquiry is answering. -/
  | reformulate
  deriving DecidableEq, Repr

theorem search_injective : Function.Injective EpistemicMove.search := by
  intro m n h
  cases m <;> cases n <;> simp_all

theorem ask_is_not_a_search_move : ∀ m, EpistemicMove.search m ≠ .ask := by
  intro m; cases m <;> simp

theorem listen_is_not_a_search_move : ∀ m, EpistemicMove.search m ≠ .listen := by
  intro m; cases m <;> simp

theorem reformulate_is_not_a_search_move : ∀ m, EpistemicMove.search m ≠ .reformulate := by
  intro m; cases m <;> simp

/-- The existing adaptive rule, read into the extended type. -/
def strategyE (s : Sensitivity) (o : Integration.Kernel.Reopen.Origin) : EpistemicMove :=
  .search (strategy s o)

/-- **The extension is conservative.**  On the coordinates the loop already
had, the extended rule is the old rule. -/
theorem strategyE_extends_strategy (s : Sensitivity) (o : Integration.Kernel.Reopen.Origin) :
    strategyE s o = .search (strategy s o) := rfl

theorem strategyE_never_deliberates (s : Sensitivity) (o : Integration.Kernel.Reopen.Origin) :
    strategyE s o ≠ .ask ∧ strategyE s o ≠ .listen ∧ strategyE s o ≠ .reformulate :=
  ⟨ask_is_not_a_search_move _, listen_is_not_a_search_move _,
    reformulate_is_not_a_search_move _⟩

/-! ## §2 Semantics on an inquiry -/

variable {Ω Y C : Type*}

/-- The state a move acts on: the live fibre and the consumer coordinate the
inquiry is currently answering. -/
structure Inquiry (Ω C : Type*) where
  /-- The hypotheses still live. -/
  fibre : Set Ω
  /-- The coordinate the inquiry has to settle. -/
  consumer : Ω → C

/-- The effect of a move.  `search` takes one turn of the existing loop; `ask`
intersects with the event the reply picks out; `listen` intersects with another
inquirer's live fibre; `reformulate` replaces the consumer coordinate and leaves
the fibre alone. -/
def act (P : Policy Ω Y) (w : Ω) (reply : Set Ω) (other : Set Ω) (c' : Ω → C) :
    EpistemicMove → Inquiry Ω C → Inquiry Ω C
  | .search _, I => { I with fibre := step P w I.fibre }
  | .ask, I => { I with fibre := I.fibre ∩ reply }
  | .listen, I => { I with fibre := I.fibre ∩ other }
  | .reformulate, I => { I with consumer := c' }

theorem search_refines (P : Policy Ω Y) (w : Ω) (reply other : Set Ω) (c' : Ω → C)
    (m : Move) (I : Inquiry Ω C) :
    Refines (act P w reply other c' (.search m) I).fibre I.fibre := step_refines _ _ _

theorem ask_refines (P : Policy Ω Y) (w : Ω) (reply other : Set Ω) (c' : Ω → C)
    (I : Inquiry Ω C) :
    Refines (act P w reply other c' .ask I).fibre I.fibre := inter_subset_left

theorem listen_refines (P : Policy Ω Y) (w : Ω) (reply other : Set Ω) (c' : Ω → C)
    (I : Inquiry Ω C) :
    Refines (act P w reply other c' .listen I).fibre I.fibre := inter_subset_left

theorem reformulate_preserves_fibre (P : Policy Ω Y) (w : Ω) (reply other : Set Ω) (c' : Ω → C)
    (I : Inquiry Ω C) :
    (act P w reply other c' .reformulate I).fibre = I.fibre := rfl

/-- Uptake never discards the actual world if the other inquirer has not. -/
theorem listen_keeps_truth {P : Policy Ω Y} {reply other : Set Ω} {c' : Ω → C}
    {I : Inquiry Ω C} {w : Ω} (hw : w ∈ I.fibre) (ho : w ∈ other) :
    w ∈ (act P w reply other c' .listen I).fibre := ⟨hw, ho⟩

/-! ## §3 What the new moves add -/

/-- A policy whose only channel reads nothing. -/
def blindPolicy : Policy Bool Unit := ⟨fun _ => ⟨fun _ => ()⟩⟩

/-- The inquiry with both hypotheses live and the identity consumer. -/
def openInquiry : Inquiry Bool Bool := ⟨univ, id⟩

/-- **Listening is not a probe.**  Against a policy whose channel is constant,
every `search` move leaves the fibre exactly as it was, while `listen` strictly
narrows it. -/
theorem listening_can_do_what_no_probe_can (m : Move) :
    (act blindPolicy true ∅ {true} id (.search m) openInquiry).fibre = openInquiry.fibre ∧
      (act blindPolicy true ∅ {true} id .listen openInquiry).fibre ⊂ openInquiry.fibre := by
  constructor
  · ext b
    simp [act, step, refine, refineBy, event, blindPolicy, openInquiry]
  · refine ⟨inter_subset_left, fun hsub => ?_⟩
    have : (false : Bool) ∈ (univ : Set Bool) ∩ {true} := hsub (mem_univ false)
    exact Bool.noConfusion this.2

/-- **Reformulating can close the question without narrowing anything.**  The
fibre is unchanged and the new consumer coordinate is determined on it, while
the old one was not. -/
theorem reformulation_can_close_without_narrowing :
    (act blindPolicy true ∅ {true} (fun _ => true) .reformulate openInquiry).fibre =
        openInquiry.fibre ∧
      ¬ Determines openInquiry.fibre openInquiry.consumer ∧
        Determines (act blindPolicy true ∅ {true} (fun _ => true) .reformulate openInquiry).fibre
          (act blindPolicy true ∅ {true} (fun _ => true) .reformulate openInquiry).consumer := by
  refine ⟨rfl, ?_, ⟨true, fun _ _ => rfl⟩⟩
  rintro ⟨v, hv⟩
  have h1 : (true : Bool) = v := hv true (mem_univ _)
  have h2 : (false : Bool) = v := hv false (mem_univ _)
  rw [← h2] at h1
  exact Bool.noConfusion h1

/-- One deployment of the semantics: the blind policy, a reply picking out
`false`, another inquirer live only at `true`, and a constant reformulation. -/
def deployed : EpistemicMove → Inquiry Bool Bool → Inquiry Bool Bool :=
  act blindPolicy true {false} {true} (fun _ => true)

theorem search_fibre (m : Move) :
    (deployed (.search m) openInquiry).fibre = (univ : Set Bool) := by
  ext b
  simp [deployed, act, step, refine, refineBy, event, blindPolicy, openInquiry]

theorem ask_fibre : (deployed .ask openInquiry).fibre = ({false} : Set Bool) := by
  simp [deployed, act, openInquiry]

theorem listen_fibre : (deployed .listen openInquiry).fibre = ({true} : Set Bool) := by
  simp [deployed, act, openInquiry]

/-- **The four move kinds are not interchangeable.**  On one inquiry, with one
reply, one other inquirer and one reformulation, the four results are pairwise
distinct. -/
theorem the_four_moves_are_not_interchangeable :
    (deployed (.search .refineMove) openInquiry).fibre ≠ (deployed .ask openInquiry).fibre ∧
      (deployed .ask openInquiry).fibre ≠ (deployed .listen openInquiry).fibre ∧
        (deployed .listen openInquiry).fibre ≠
            (deployed (.search .refineMove) openInquiry).fibre ∧
          (deployed .reformulate openInquiry).consumer ≠
            (deployed .listen openInquiry).consumer := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [search_fibre, ask_fibre]
    intro h
    have hmem : (true : Bool) ∈ ({false} : Set Bool) := by rw [← h]; exact mem_univ true
    exact Bool.noConfusion hmem
  · rw [ask_fibre, listen_fibre]
    intro h
    have hmem : (false : Bool) ∈ ({true} : Set Bool) := by rw [← h]; rfl
    exact Bool.noConfusion hmem
  · rw [listen_fibre, search_fibre]
    intro h
    have hmem : (false : Bool) ∈ ({true} : Set Bool) := by rw [h]; exact mem_univ false
    exact Bool.noConfusion hmem
  · intro h
    have := congrFun h false
    exact Bool.noConfusion this

end Integration.Kernel.Welds.DeliberativeMoves
