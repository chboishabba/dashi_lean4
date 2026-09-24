import Integration.Kernel.Quotient

/-!
# Query-relative residuals: cutset → first residual → obligation → producer → work

`Agda/DASHI/Cognition/PNF/SensibLawIssueIndexedAdjudicativeHyperfabricExact.agda`
(in the 6 September tranche archive shipped with this project) contains a
pipeline this corpus keeps rebuilding by hand:
`firstAdjudicativeResidual : AdjudicativeQuery → AdjudicativeCutset →
AdjudicativeResidual`, then `obligationFor`, `discriminatorFor` and
`workKindFor`.  The Agda version is a genuine executable function — a nested
`with` cascade over the five queries and the Boolean closure fields, with
`discriminatorFor` and `workKindFor` total pattern matches — but it is written
out for one fixed legal coordinate vocabulary, and it carries no theorems about
the compiler itself.

This file is the generic owner.  The cutset is a `List Coord` per query, the
closure state is a `Coord → Bool`, and the pipeline is the composite.  What is
added over the Agda module is everything about *the pipeline as such*: that the
first residual is a genuine open coordinate of the query's own cutset, that
closure is exactly the absence of one, that resolving a residual removes it, and
— the point of the exercise — that the residual is a function of the
query-and-state **pair** and of neither coordinate alone.

## What is proved

* `firstResidual_mem_cutset`, `firstResidual_isOpen` — the residual returned is
  in this query's cutset and is actually unresolved.
* **`closed_iff_all_closed`** — `Closed` (no residual) iff every coordinate of
  the query's cutset is closed.  With `no_work_when_closed`, this is the "stop"
  condition of the loop layer.
* **`resolve_removes_residual`** — closing a coordinate removes it from the
  answer: the compiler cannot return the same residual twice.
  `resolve_preserves_closed` says resolving never re-opens anything.
* `work_factors_through_first_residual` and
  `same_residual_same_work` — the whole obligation/producer/work tail is a
  function of the first residual, so all query-dependence is concentrated in
  that one step.
* **`residual_does_not_descend_through_state`** and
  **`residual_does_not_descend_through_query`** — the headline pair, both
  instances of `Integration.Kernel.Quotient.not_descendsThrough_of_collision`:
  two queries over the *same* state expose different first residuals, and one
  query over two states does too.  `residual_is_query_relative` is the explicit
  fixture (a burden query already closed while a liability query is still
  open).  Together with `residual_descends_through_pair` this says the
  query/state pair is exactly the right index — the complement of
  consumer-relative quotienting in `Integration.Kernel.Quotient`.

**Claim boundary.**  `Query`, `Coord`, `Obligation`, `Producer` and `Work` are
arbitrary types and the compiler is arbitrary data; the fixture in §4 uses three
numbered coordinates and two Boolean queries.  Nothing is claimed about any
legal, scientific or engineering question.
-/

namespace Integration.Kernel.QueryResidual

open Integration.Kernel.Quotient

universe u v w x y

variable {Query : Type u} {Coord : Type v} {Obligation : Type w} {Producer : Type x}
  {Work : Type y}

/-! ## §1 The compiler -/

/-- A query-indexed residual compiler: which coordinates each query depends on,
in priority order, and what work an open coordinate turns into. -/
structure Compiler (Query : Type u) (Coord : Type v) (Obligation : Type w)
    (Producer : Type x) (Work : Type y) where
  /-- The coordinates this query needs, in the order they are attacked. -/
  cutset : Query → List Coord
  /-- The proof obligation an open coordinate raises. -/
  obligationFor : Coord → Obligation
  /-- The producer that could discharge an obligation. -/
  producerFor : Obligation → Producer
  /-- The kind of epistemic work that producer is. -/
  workFor : Producer → Work

/-- Which coordinates are currently closed. -/
abbrev State (Coord : Type v) : Type v := Coord → Bool

variable (K : Compiler Query Coord Obligation Producer Work)

/-- The first coordinate of this query's cutset that is still open. -/
def firstResidual (q : Query) (s : State Coord) : Option Coord :=
  (K.cutset q).find? fun c => !s c

/-- The obligation raised by the first residual. -/
def obligation (q : Query) (s : State Coord) : Option Obligation :=
  (firstResidual K q s).map K.obligationFor

/-- The producer to run next. -/
def producer (q : Query) (s : State Coord) : Option Producer :=
  (obligation K q s).map K.producerFor

/-- The kind of work to do next. -/
def work (q : Query) (s : State Coord) : Option Work :=
  (producer K q s).map K.workFor

/-- The query is closed in this state: nothing in its cutset is open. -/
def Closed (q : Query) (s : State Coord) : Prop := firstResidual K q s = none

/-! ## §2 The compiler behaves -/

variable {K}

theorem firstResidual_mem_cutset {q : Query} {s : State Coord} {c : Coord}
    (h : firstResidual K q s = some c) : c ∈ K.cutset q :=
  List.mem_of_find?_eq_some h

/-- The coordinate returned really is unresolved. -/
theorem firstResidual_isOpen {q : Query} {s : State Coord} {c : Coord}
    (h : firstResidual K q s = some c) : s c = false := by
  have := List.find?_some h
  simpa using this

/-- **Closure is exactly the absence of a residual.** -/
theorem closed_iff_all_closed {q : Query} {s : State Coord} :
    Closed K q s ↔ ∀ c ∈ K.cutset q, s c = true := by
  unfold Closed firstResidual
  rw [List.find?_eq_none]
  constructor
  · intro h c hc
    simpa using h c hc
  · intro h c hc
    simpa using h c hc

theorem no_work_when_closed {q : Query} {s : State Coord} (h : Closed K q s) :
    work K q s = none := by
  unfold Closed at h
  simp [work, producer, obligation, h]

theorem work_isSome_of_residual {q : Query} {s : State Coord} {c : Coord}
    (h : firstResidual K q s = some c) :
    work K q s = some (K.workFor (K.producerFor (K.obligationFor c))) := by
  simp [work, producer, obligation, h]

/-- The obligation/producer/work tail is a function of the first residual alone:
all query-dependence sits in `firstResidual`. -/
theorem work_factors_through_first_residual (q : Query) (s : State Coord) :
    work K q s =
      (firstResidual K q s).map (fun c => K.workFor (K.producerFor (K.obligationFor c))) := by
  cases h : firstResidual K q s <;> simp [work, producer, obligation, h]

theorem same_residual_same_work {q q' : Query} {s s' : State Coord}
    (h : firstResidual K q s = firstResidual K q' s') : work K q s = work K q' s' := by
  rw [work_factors_through_first_residual, work_factors_through_first_residual, h]

/-! ## §3 Resolving a coordinate -/

variable [DecidableEq Coord]

/-- Close one coordinate. -/
def resolve (s : State Coord) (c : Coord) : State Coord := fun d => if d = c then true else s d

@[simp] theorem resolve_self (s : State Coord) (c : Coord) : resolve s c c = true := by
  simp [resolve]

theorem resolve_of_ne {s : State Coord} {c d : Coord} (h : d ≠ c) : resolve s c d = s d := by
  simp [resolve, h]

/-- Resolving never re-opens a coordinate. -/
theorem resolve_preserves_closed {s : State Coord} {c d : Coord} (h : s d = true) :
    resolve s c d = true := by
  by_cases hd : d = c <;> simp [resolve, hd, h]

/-- **The compiler cannot return the same residual twice.**  After the residual
is closed, it is no longer the answer. -/
theorem resolve_removes_residual (q : Query) (s : State Coord) (c : Coord) :
    firstResidual K q (resolve s c) ≠ some c := by
  intro h
  have := firstResidual_isOpen h
  rw [resolve_self] at this
  exact Bool.noConfusion this

/-- Resolving a coordinate can only shrink the open set, so a closed query stays
closed. -/
theorem closed_of_closed_resolve {q : Query} {s : State Coord} {c : Coord}
    (h : Closed K q s) : Closed K q (resolve s c) := by
  rw [closed_iff_all_closed] at h ⊢
  exact fun d hd => resolve_preserves_closed (h d hd)

/-! ## §4 The residual is query-relative

Three coordinates and two queries with different cutsets.  In the state where
coordinate `0` is closed and `1` is not, the first query is finished and the
second is not. -/

/-- Two queries: `true` needs only coordinate `0`; `false` needs `0` then `1`. -/
def twoQueryCompiler : Compiler Bool (Fin 3) (Fin 3) (Fin 3) (Fin 3) where
  cutset q := if q then [0] else [0, 1]
  obligationFor := id
  producerFor := id
  workFor := id

/-- Coordinate `0` closed, the others open. -/
def partialState : State (Fin 3) := fun c => c == 0

/-- **The first residual is query-relative.**  One query is closed in this
state; the other still has an open coordinate. -/
theorem residual_is_query_relative :
    firstResidual twoQueryCompiler true partialState = none ∧
      firstResidual twoQueryCompiler false partialState = some 1 := by
  constructor <;> rfl

/-- **The residual is not a function of the state.**  Forgetting which question
is being asked destroys the answer, even though the state is unchanged. -/
theorem residual_does_not_descend_through_state :
    ¬ DescendsThrough
        (fun p : Bool × State (Fin 3) => firstResidual twoQueryCompiler p.1 p.2)
        (fun p : Bool × State (Fin 3) => p.2) :=
  not_descendsThrough_of_collision (x := (true, partialState)) (y := (false, partialState))
    rfl (by decide)

/-- And not a function of the query either: the same question over two states
has two different first residuals. -/
theorem residual_does_not_descend_through_query :
    ¬ DescendsThrough
        (fun p : Bool × State (Fin 3) => firstResidual twoQueryCompiler p.1 p.2)
        (fun p : Bool × State (Fin 3) => p.1) :=
  not_descendsThrough_of_collision (x := (false, partialState))
    (y := (false, fun _ => false)) rfl (by decide)

/-- The pair, on the other hand, is exactly the right index. -/
theorem residual_descends_through_pair :
    DescendsThrough
      (fun p : Bool × State (Fin 3) => firstResidual twoQueryCompiler p.1 p.2)
      (fun p : Bool × State (Fin 3) => p) :=
  ⟨fun p => firstResidual twoQueryCompiler p.1 p.2, fun _ => rfl⟩

end Integration.Kernel.QueryResidual
