import Integration.StructureMorphism

/-!
# Paths, transport, and monotone obstructions

Machine execution, reachability in a transition system, proof search and scale
dynamics all want the same substrate: a state graph, composition of paths, and a
map that respects the path structure.  This file owns it.

Contents.

* `Path` — `Relation.ReflTransGen` of a step relation, with identity and
  composition (`path_refl`, `path_trans`);
* `Simulation`, `path_transport` — an observer that carries each step to a step
  carries every path to a path.  This is the relational form of the exact
  square, and `simulation_of_exact` derives it from a functional one, with
  `path_of_reaches` and `reaches_of_path` identifying the deterministic case
  with `Integration.StructureMorphism.Reaches`;
* `mono_le_of_path`, `not_path_of_lt` — **the monotone obstruction**: an
  invariant that never decreases along a step cannot decrease along a path, so a
  target of strictly smaller invariant is unreachable.  This is the generic
  irreversibility mechanism: deposited history, accumulated damage, monotone
  resource consumption and monotone knowledge all instantiate it;
* `persistent_obstruction` — the Boolean form: a residue that is never erased
  makes any residue-free state unreachable;
* `ProofSystem`, `Provable`, `provable_transport` — the AND/OR specialisation.
  A hyperedge is an AND-branch (all children must be provable) and the choice of
  hyperedge is the OR.  A simulation of hyperedges transports provability, which
  is the proof-search lane's version of `path_transport`;
* `provable_sound_of_simulation` — and it is exactly what makes the property
  `Provable` sound for a quotient, connecting to
  `Integration.StructureMorphism.Sound`.

Everything here is about arbitrary relations; no finiteness and no metric.
-/

namespace Integration.PathTransport

open Integration.StructureMorphism

variable {X Y : Type*}

/-! ## Paths -/

/-- A finite path in the state graph. -/
def Path (step : X → X → Prop) : X → X → Prop := Relation.ReflTransGen step

theorem path_refl (step : X → X → Prop) (x : X) : Path step x x :=
  Relation.ReflTransGen.refl

theorem path_single {step : X → X → Prop} {x y : X} (h : step x y) : Path step x y :=
  Relation.ReflTransGen.single h

theorem path_trans {step : X → X → Prop} {x y z : X} (h₁ : Path step x y)
    (h₂ : Path step y z) : Path step x z := h₁.trans h₂

/-! ## Transport along an observer -/

/-- The observer carries each step to a step. -/
def Simulation (π : X → Y) (step : X → X → Prop) (step' : Y → Y → Prop) : Prop :=
  ∀ x y, step x y → step' (π x) (π y)

/-- **Paths transport.** -/
theorem path_transport {π : X → Y} {step : X → X → Prop} {step' : Y → Y → Prop}
    (hs : Simulation π step step') {x y : X} (h : Path step x y) : Path step' (π x) (π y) :=
  Relation.ReflTransGen.lift π (fun _ _ hab => hs _ _ hab) h

/-- A functional exact square is a simulation of the graphs of the two maps. -/
theorem simulation_of_exact {π : X → Y} {f : X → X} {g : Y → Y} (h : Exact π f g) :
    Simulation π (fun a b => f a = b) (fun a b => g a = b) := by
  rintro x y rfl
  exact (h x).symm

/-- In the deterministic case, `Path` is `Reaches`. -/
theorem path_of_reaches {f : X → X} {x y : X} (h : Reaches f x y) :
    Path (fun a b => f a = b) x y := by
  obtain ⟨n, rfl⟩ := h
  induction n with
  | zero => exact path_refl _ _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.tail rfl

theorem reaches_of_path {f : X → X} {x y : X} (h : Path (fun a b => f a = b) x y) :
    Reaches f x y := by
  induction h with
  | refl => exact reaches_refl f x
  | tail _ hstep ih => exact reaches_trans ih ⟨1, hstep⟩

/-! ## Monotone obstructions to reversibility -/

variable {α : Type*} [Preorder α]

/-- **A monotone invariant does not decrease along a path.** -/
theorem mono_le_of_path {step : X → X → Prop} {I : X → α}
    (hmono : ∀ x y, step x y → I x ≤ I y) {x y : X} (h : Path step x y) : I x ≤ I y := by
  induction h with
  | refl => exact le_refl _
  | tail _ hstep ih => exact le_trans ih (hmono _ _ hstep)

/-- **Hence a strictly smaller target is unreachable.**  This is the generic
irreversibility mechanism. -/
theorem not_path_of_lt {step : X → X → Prop} {I : X → α}
    (hmono : ∀ x y, step x y → I x ≤ I y) {x y : X} (hlt : I y < I x) : ¬ Path step x y :=
  fun h => absurd (mono_le_of_path hmono h) (not_le_of_gt hlt)

/-- The Boolean form: a residue that no transition erases makes every
residue-free state unreachable. -/
theorem persistent_obstruction {step : X → X → Prop} {r : X → Prop}
    (hpersist : ∀ x y, step x y → r x → r y) {x y : X} (hx : r x) (hy : ¬ r y) :
    ¬ Path step x y := by
  intro h
  refine hy ?_
  clear hy
  induction h with
  | refl => exact hx
  | tail _ hstep ih => exact hpersist _ _ hstep ih

/-! ## The AND/OR specialisation: proof search -/

/-- A hypergraph proof system: `edge x ts` says that the goal `x` is reduced by
one inference to the list of subgoals `ts`.  Choosing the edge is the OR; the
subgoals of an edge are the AND. -/
structure ProofSystem (X : Type*) where
  /-- The hyperedges out of a goal. -/
  edge : X → List X → Prop

/-- Provability: the least predicate closed under the hyperedges. -/
inductive Provable {X : Type*} (P : ProofSystem X) : X → Prop
  /-- Close the goal `x` by an edge all of whose subgoals are provable. -/
  | mk (x : X) (ts : List X) (h : P.edge x ts) (all : ∀ t ∈ ts, Provable P t) : Provable P x

/-- An axiom (an edge with no subgoals) is provable. -/
theorem provable_of_leaf {P : ProofSystem X} {x : X} (h : P.edge x []) : Provable P x :=
  Provable.mk x [] h (by simp)

/-- **Provability transports along a simulation of hyperedges.** -/
theorem provable_transport {P : ProofSystem X} {Q : ProofSystem Y} (π : X → Y)
    (hsim : ∀ x ts, P.edge x ts → Q.edge (π x) (ts.map π)) {x : X} (h : Provable P x) :
    Provable Q (π x) := by
  induction h with
  | mk x ts hedge _ ih =>
    refine Provable.mk (π x) (ts.map π) (hsim x ts hedge) ?_
    intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    exact ih t' ht'

/-- And then provability of the image is a sound property of the quotient: this
is the `QuotientSound` witness the proof-search lane requires before
transporting a proof. -/
theorem provable_sound_of_simulation {Q : ProofSystem Y} (π : X → Y) :
    Sound π (fun x => Provable Q (π x)) :=
  sound_of_factors π (fun y => Provable Q y)

end Integration.PathTransport
