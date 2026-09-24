import Integration.Kernel.ResidualFibre

/-!
# Consumer quotients, descent, and consumer-relative inverses

The kernel's residual calculus (`Integration.Kernel.ResidualFibre`) takes an
observation *value* and narrows a fibre.  This file supplies the layer the
domain lanes keep rebuilding underneath it: the **consumer quotient** itself.

The Agda snapshot in `Agda/DASHI/Core/ObserverRefinementLatticeExact.agda`
declares `Observer`, `ObservationalEq`, `Refines`, `StrictRefinement` and
`pairObserver`, and `Agda/DASHI/Core/ResidualObserverDependencyExact.agda` adds
`DependencyCodeDescendsAt` with the proof that a hidden residual dependency
blocks descent.  Those are genuine Agda definitions with checked proof terms,
but they are stated as *implications between observers*; what is missing there,
and supplied here, is the **equivalence between descent and refinement**, which
is what makes "the consumer only sees a quotient" a theorem rather than a
convention.

## What is proved

* `ObsEq Q x y ↔ Q x = Q y` is an equivalence relation; `fibre` is its class,
  and `fibre_eq_refine_univ` identifies that class with the kernel's own
  backward refinement by the observation event.  So *quotient class* and
  *residual fibre* are literally the same object, not an analogy.
* **`descendsThrough_iff_refinedBy`** — a consumer `C` factors through the
  quotient `Q` (∃ f, f ∘ Q = C) **iff** `Q` separates at least as much as `C`.
  The left-to-right direction is free; the right-to-left direction is where the
  factoring map is built (and needs the consumer's value type to be inhabited,
  `no_descent_to_empty_consumer` showing the hypothesis is load-bearing).
* `descent_is_consumer_relative` — one consumer descends through a quotient
  while another does not: descent is a property of the *pair*, never of the
  quotient alone.
* `not_descendsThrough_of_collision` — the exact obstruction: one pair of states
  the quotient identifies and the consumer separates refutes descent.  Its
  contrapositive `determines_of_descends` is the payoff for the loop layer.
* Adding a coordinate: `pair`, `refinedBy_pair_left`, `StrictlyRefines`,
  `strictlyRefines_pair_of_separates`, `fibre_pair_subset` and
  `refinement_is_not_refutation` — a new observation coordinate *refines* the
  old quotient; the coarse reading stays a correct function of the fine one, so
  refinement is not a retraction of the coarse claim.
* Dynamics: `MapDescends`, `mapDescends_iff_classPreserving`, and
  `dynamics_need_not_descend`.
* Consumer-relative inverse: `InvertsFor`, `invertsFor_of_inverts`,
  **`invertsFor_not_inverts`** (a transform can be exactly invertible for one
  consumer and destroy the state for everyone else), and
  `invertsFor_of_descends` (consumer-relative inversion transports *down* to
  coarser consumers, never up).

**Claim boundary.** Everything here is a statement about functions out of an
arbitrary type.  "Consumer", "observation" and "state" are names for the three
arguments; nothing is claimed about any physical, clinical, financial, legal or
algorithmic system.
-/

namespace Integration.Kernel.Quotient

open Set

universe u v w

variable {Ω : Type u} {V : Type v} {W : Type w}

/-! ## §1 The quotient of a state space by a consumer's observation -/

/-- Consumer indistinguishability: `x ∼_Q y` iff `Q x = Q y`. -/
def ObsEq (Q : Ω → V) (x y : Ω) : Prop := Q x = Q y

theorem obsEq_iff {Q : Ω → V} {x y : Ω} : ObsEq Q x y ↔ Q x = Q y := Iff.rfl

theorem obsEq_equivalence (Q : Ω → V) : Equivalence (ObsEq Q) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩

/-- The setoid a consumer imposes on the fine state space. -/
def obsSetoid (Q : Ω → V) : Setoid Ω := ⟨ObsEq Q, obsEq_equivalence Q⟩

/-- The class of `x`: the states the consumer cannot tell apart from `x`. -/
def fibre (Q : Ω → V) (x : Ω) : Set Ω := {y | Q y = Q x}

@[simp] theorem mem_fibre {Q : Ω → V} {x y : Ω} : y ∈ fibre Q x ↔ Q y = Q x := Iff.rfl

theorem self_mem_fibre (Q : Ω → V) (x : Ω) : x ∈ fibre Q x := rfl

/-- The consumer's class is exactly the kernel's residual fibre after reading
the consumer's own channel: quotient class and residual fibre are one object. -/
theorem fibre_eq_refine_univ (Q : Ω → V) (x : Ω) :
    fibre Q x = ResidualFibre.refine univ ⟨Q⟩ (Q x) := by
  ext y; simp [fibre, ResidualFibre.refine, ResidualFibre.refineBy,
    ResidualFibre.event]

/-! ## §2 Refinement and descent -/

/-- `RefinedBy C Q`: the quotient `Q` separates at least as much as the consumer
coordinate `C`. -/
def RefinedBy (C : Ω → W) (Q : Ω → V) : Prop := ∀ x y, Q x = Q y → C x = C y

/-- `DescendsThrough C Q`: the consumer coordinate factors through the quotient. -/
def DescendsThrough (C : Ω → W) (Q : Ω → V) : Prop := ∃ f : V → W, ∀ x, f (Q x) = C x

@[refl] theorem refinedBy_refl (Q : Ω → V) : RefinedBy Q Q := fun _ _ h => h

theorem refinedBy_trans {U : Type*} {C : Ω → W} {Q : Ω → V} {R : Ω → U}
    (h₁ : RefinedBy C Q) (h₂ : RefinedBy Q R) : RefinedBy C R :=
  fun x y h => h₁ x y (h₂ x y h)

theorem refinedBy_of_descends {C : Ω → W} {Q : Ω → V} (h : DescendsThrough C Q) :
    RefinedBy C Q := by
  obtain ⟨f, hf⟩ := h
  intro x y hxy
  rw [← hf x, ← hf y, hxy]

/-- **Descent is refinement.**  A consumer coordinate factors through a quotient
exactly when the quotient never identifies two states the consumer separates. -/
theorem descendsThrough_iff_refinedBy [Nonempty W] (C : Ω → W) (Q : Ω → V) :
    DescendsThrough C Q ↔ RefinedBy C Q := by
  refine ⟨refinedBy_of_descends, fun h => ?_⟩
  classical
  refine ⟨fun v => if hv : ∃ x, Q x = v then C hv.choose else Classical.arbitrary W, ?_⟩
  intro x
  have hx : ∃ x', Q x' = Q x := ⟨x, rfl⟩
  show (if hv : ∃ x', Q x' = Q x then C hv.choose else Classical.arbitrary W) = C x
  rw [dif_pos hx]
  exact h _ _ hx.choose_spec

/-- The inhabitedness hypothesis in `descendsThrough_iff_refinedBy` is
load-bearing: over an empty state space every consumer is refined by every
quotient, and yet nothing factors through a quotient with no values to send
anywhere. -/
theorem no_descent_to_empty_consumer :
    ∃ (Ω V W : Type) (C : Ω → W) (Q : Ω → V),
      RefinedBy C Q ∧ ¬ DescendsThrough C Q := by
  refine ⟨Empty, Unit, Empty, fun e => e, fun _ => (), fun x => x.elim, ?_⟩
  rintro ⟨f, -⟩
  exact (f ()).elim

/-- The exact obstruction to descent: a quotient collision the consumer
separates. -/
theorem not_descendsThrough_of_collision {C : Ω → W} {Q : Ω → V} {x y : Ω}
    (hQ : Q x = Q y) (hC : C x ≠ C y) : ¬ DescendsThrough C Q :=
  fun h => hC (refinedBy_of_descends h x y hQ)

/-- Conversely, if the consumer descends then its value is constant on every
class — the fibre *determines* the consumer coordinate, in the sense of
`Integration.Kernel.ResidualFibre.Determines`. -/
theorem determines_of_descends {C : Ω → W} {Q : Ω → V} (h : DescendsThrough C Q)
    (x : Ω) : ResidualFibre.Determines (fibre Q x) C :=
  ⟨C x, fun y hy => refinedBy_of_descends h y x hy⟩

theorem descends_of_determines_all [Nonempty W] {C : Ω → W} {Q : Ω → V}
    (h : ∀ x, ResidualFibre.Determines (fibre Q x) C) : DescendsThrough C Q := by
  rw [descendsThrough_iff_refinedBy]
  intro x y hxy
  obtain ⟨v, hv⟩ := h y
  rw [hv x hxy, hv y (self_mem_fibre Q y)]

/-- **Descent is consumer-relative.**  One consumer descends through the
quotient; another, on the same states and the same quotient, does not. -/
theorem descent_is_consumer_relative :
    ∃ (Ω V W : Type) (Q : Ω → V) (C₁ C₂ : Ω → W),
      DescendsThrough C₁ Q ∧ ¬ DescendsThrough C₂ Q := by
  refine ⟨Bool × Bool, Bool, Bool, Prod.fst, Prod.fst, Prod.snd, ⟨id, fun _ => rfl⟩, ?_⟩
  exact not_descendsThrough_of_collision (x := (true, true)) (y := (true, false)) rfl
    (by simp)

/-! ## §3 Refining a quotient by a new coordinate -/

/-- Observing one more coordinate. -/
def pair (Q : Ω → V) (E : Ω → W) : Ω → V × W := fun x => (Q x, E x)

theorem refinedBy_pair_left (Q : Ω → V) (E : Ω → W) : RefinedBy Q (pair Q E) :=
  fun _ _ h => congrArg Prod.fst h

theorem refinedBy_pair_right (Q : Ω → V) (E : Ω → W) : RefinedBy E (pair Q E) :=
  fun _ _ h => congrArg Prod.snd h

/-- **Refinement is not refutation.**  After a new coordinate is added, the old
coarse reading is still a correct function of the new one: the coarse
representation was a quotient, not an error. -/
theorem refinement_is_not_refutation (Q : Ω → V) (E : Ω → W) :
    DescendsThrough Q (pair Q E) := ⟨Prod.fst, fun _ => rfl⟩

/-- `Q` is refined by `R` and the refinement is proper: some collision of `Q` is
separated by `R`. -/
structure StrictlyRefines (Q : Ω → V) {U : Type*} (R : Ω → U) : Prop where
  /-- Every distinction the coarse observer makes is made by the fine one. -/
  law : RefinedBy Q R
  /-- A pair the coarse observer identifies and the fine one separates. -/
  witness : ∃ x y, Q x = Q y ∧ R x ≠ R y

theorem strictlyRefines_pair_of_separates (Q : Ω → V) (E : Ω → W) {x y : Ω}
    (hQ : Q x = Q y) (hE : E x ≠ E y) : StrictlyRefines Q (pair Q E) :=
  { law := refinedBy_pair_left Q E
    witness := ⟨x, y, hQ, fun h => hE (congrArg Prod.snd h)⟩ }

theorem fibre_pair_subset (Q : Ω → V) (E : Ω → W) (x : Ω) :
    fibre (pair Q E) x ⊆ fibre Q x := fun _ h => congrArg Prod.fst h

theorem fibre_pair_ssubset {Q : Ω → V} {E : Ω → W} {x y : Ω}
    (hQ : Q y = Q x) (hE : E y ≠ E x) : fibre (pair Q E) x ⊂ fibre Q x := by
  refine ⟨fibre_pair_subset Q E x, fun hsub => ?_⟩
  exact hE (congrArg Prod.snd (hsub (show y ∈ fibre Q x from hQ)))

/-- The residual coordinate of a strict refinement never descends through the
coarse quotient: this is the Lean form of
`hiddenResidualDependencyBlocksDescent`. -/
theorem residual_does_not_descend {Q : Ω → V} {E : Ω → W} {x y : Ω}
    (hQ : Q x = Q y) (hE : E x ≠ E y) : ¬ DescendsThrough E Q :=
  not_descendsThrough_of_collision hQ hE

/-! ## §4 Descent of dynamics -/

/-- A transformation of the fine state descends to the quotient. -/
def MapDescends (Q : Ω → V) (f : Ω → Ω) : Prop := ∃ F : V → V, ∀ x, F (Q x) = Q (f x)

theorem mapDescends_iff_classPreserving [Nonempty V] (Q : Ω → V) (f : Ω → Ω) :
    MapDescends Q f ↔ ∀ x y, Q x = Q y → Q (f x) = Q (f y) :=
  descendsThrough_iff_refinedBy (C := fun x => Q (f x)) (Q := Q)

/-- Dynamics need not descend: a map can be perfectly well defined on the fine
state and yet send two states with the same reading to different readings. -/
theorem dynamics_need_not_descend :
    ∃ (Ω V : Type) (Q : Ω → V) (f : Ω → Ω), ¬ MapDescends Q f := by
  refine ⟨Bool × Bool, Bool, Prod.fst, fun p => (p.2, p.2), ?_⟩
  rintro ⟨F, hF⟩
  have h₁ : F true = true := hF (true, true)
  have h₂ : F true = false := hF (true, false)
  rw [h₁] at h₂
  exact Bool.noConfusion h₂

/-! ## §5 Consumer-relative inverses -/

/-- `g` inverts `f` outright. -/
def Inverts (f g : Ω → Ω) : Prop := ∀ x, g (f x) = x

/-- `g` inverts `f` *as far as the consumer `C` can tell*. -/
def InvertsFor (C : Ω → W) (f g : Ω → Ω) : Prop := ∀ x, C (g (f x)) = C x

theorem invertsFor_of_inverts (C : Ω → W) {f g : Ω → Ω} (h : Inverts f g) :
    InvertsFor C f g := fun x => by rw [h x]

/-- **A consumer-relative inverse is not a semantic inverse.**  There is a
transform and a candidate inverse that are exactly inverse for one consumer and
lose the state entirely. -/
theorem invertsFor_not_inverts :
    ∃ (Ω W : Type) (C : Ω → W) (f g : Ω → Ω),
      InvertsFor C f g ∧ ¬ Inverts f g := by
  refine ⟨Bool × Bool, Bool, Prod.fst, fun p => (p.1, true), id, fun _ => rfl, ?_⟩
  intro h
  have := h (true, false)
  simp at this

/-- Consumer-relative inversion transports **down**: if `D` descends through `C`
then an inverse for `C` is an inverse for `D`.  (It does not transport up — that
is `invertsFor_not_inverts` with `C` the trivial consumer.) -/
theorem invertsFor_of_descends {U : Type*} {C : Ω → W} {D : Ω → U} {f g : Ω → Ω}
    (hD : DescendsThrough D C) (h : InvertsFor C f g) : InvertsFor D f g := by
  obtain ⟨k, hk⟩ := hD
  intro x
  rw [← hk (g (f x)), ← hk x, h x]

/-! ## §6 Coarse quotient plus relative-fine residual: exact reopening -/

/-- A **coarse/relative-fine reopening geometry**: a coarse consumer quotient, a
retained relative-fine coordinate, and a rule that puts a state back together
from the two.  This mirrors `CoarseFineReopening` of
`Agda/DASHI/Core/CoarseFineRelativeFibreExact.agda`. -/
structure Reopening (Ω : Type u) (V : Type v) (W : Type w) where
  /-- The coarse consumer quotient. -/
  coarse : Ω → V
  /-- The retained relative-fine coordinate. -/
  relativeFine : Ω → W
  /-- Putting the state back together. -/
  reopen : V → W → Ω
  /-- Reopening is exact on every state. -/
  reopen_exact : ∀ x, reopen (coarse x) (relativeFine x) = x

namespace Reopening

variable (R : Reopening Ω V W)

/-- Coarse reading and retained residual together determine the state. -/
theorem pair_injective : Function.Injective (pair R.coarse R.relativeFine) := by
  intro x y h
  have hc : R.coarse x = R.coarse y := congrArg Prod.fst h
  have hf : R.relativeFine x = R.relativeFine y := congrArg Prod.snd h
  rw [← R.reopen_exact x, ← R.reopen_exact y, hc, hf]

/-- Inside a coarse class, two distinct states must differ in the retained
residual: the residual is exactly what the coarse quotient dropped. -/
theorem relativeFine_separates_inside_coarse_class {x y : Ω}
    (hc : R.coarse x = R.coarse y) (hxy : x ≠ y) : R.relativeFine x ≠ R.relativeFine y :=
  fun hf => hxy (R.pair_injective (Prod.ext hc hf))

/-- The refined class is a singleton: after reopening nothing is left open. -/
theorem fibre_pair_eq_singleton (x : Ω) :
    fibre (pair R.coarse R.relativeFine) x = {x} := by
  ext y
  refine ⟨fun h => R.pair_injective h, fun h => ?_⟩
  rw [show y = x from h]
  exact self_mem_fibre _ x

end Reopening

/-- **Exact reopening is available exactly when the pair observer separates.**
The forward direction is `Reopening.pair_injective`; this is the converse, which
builds the reopening rule from the separation. -/
theorem exists_reopening_of_injective [Nonempty Ω] {Q : Ω → V} {F : Ω → W}
    (h : Function.Injective (pair Q F)) :
    ∃ R : Reopening Ω V W, R.coarse = Q ∧ R.relativeFine = F := by
  classical
  refine ⟨⟨Q, F, fun v w => Function.invFun (pair Q F) (v, w), fun x => ?_⟩, rfl, rfl⟩
  exact Function.leftInverse_invFun h x

end Integration.Kernel.Quotient
