import Integration.Kernel.Probe
import Integration.CoordinateSufficiency

/-!
# The corpus's own sufficiency calculus is the kernel, fibrewise

`Integration.CoordinateSufficiency` (and, beneath it,
`Integration.LeastSufficient`) is the domain-neutral owner that most of the
corpus already routes through: `Determines O C` says the consumer is constant on
the fibres of the observation, `Refines o o'` orders observers by information,
`FactorsOn S C` is the coordinate version, and `Essential j C` is the two-state
witness that a coordinate cannot be forgotten.

Those are *global* statements — quantified over all states.  The kernel's
`Determines F c` is *local*: it asks whether one residual fibre settles one
consumer question.  This file proves the two are the same thing, taken over all
fibres:

* **`determines_iff_fibrewise`** — `Determines O C` holds exactly when every
  event of the channel `O` closes the consumer question in the kernel's sense;
* **`refines_iff_event_subset`** — the information order on observers is exactly
  containment of their events: `o` refines `o'` iff each `o`-event sits inside
  the corresponding `o'`-event;
* **`refine_join`** — refining by the join of two observers is refining by each
  in turn, so `join` is the kernel's sequential composition of probes;
* **`factorsOn_iff_fibrewise`** — the coordinate version, through the projection
  channel;
* **`essential_iff_fibre_collision`** — a coordinate is essential exactly when
  some fibre of the forget-that-coordinate channel carries a kernel collision.

The honest boundary is `one_fibre_closure_is_not_global_sufficiency`: closure on
a *single* fibre is strictly weaker than global sufficiency.  Kernel closure is
consumer- *and* fibre-relative, which is exactly why the loop in
`Integration.Kernel.Loop` can terminate without identifying the world.
-/

namespace Integration.Kernel.Instances.CoordinateSufficiencyBridge

open Set Integration.Kernel.ResidualFibre Integration.Kernel.Probe

/-! ## §1 Global sufficiency is fibrewise closure -/

section General

variable {X Y Z : Type*}

/-- An observation function as a kernel channel. -/
def obsChannel (O : X → Y) : Channel X Y := ⟨O⟩

@[simp] theorem mem_obsChannel_event {O : X → Y} {y : Y} {x : X} :
    x ∈ event (obsChannel O) y ↔ O x = y := Iff.rfl

/-- **Global sufficiency is exactly kernel closure on every fibre.** -/
theorem determines_iff_fibrewise [Nonempty Z] (O : X → Y) (C : X → Z) :
    Integration.CoordinateSufficiency.Determines O C ↔
      ∀ y : Y, Determines (event (obsChannel O) y) C := by
  classical
  constructor
  · intro h y
    by_cases hne : (event (obsChannel O) y).Nonempty
    · obtain ⟨x₀, hx₀⟩ := hne
      exact ⟨C x₀, fun x hx => h x x₀ (by rw [mem_obsChannel_event.1 hx, mem_obsChannel_event.1 hx₀])⟩
    · exact ⟨Classical.arbitrary Z, fun x hx => absurd ⟨x, hx⟩ hne⟩
  · intro h x₁ x₂ hx
    obtain ⟨v, hv⟩ := h (O x₁)
    rw [hv x₁ rfl, hv x₂ hx.symm]

/-- **The information order is containment of events.**  `o` refines `o'`
exactly when each `o`-event is contained in the corresponding `o'`-event. -/
theorem refines_iff_event_subset [Nonempty Z] (o : X → Y) (o' : X → Z) :
    Integration.LeastSufficient.Refines o o' ↔
      ∀ x : X, event (obsChannel o) (o x) ⊆ event (obsChannel o') (o' x) := by
  classical
  constructor
  · rintro ⟨f, hf⟩ x x' hx'
    have : o x' = o x := hx'
    show o' x' = o' x
    rw [hf x', hf x, this]
  · intro h
    refine ⟨fun y => if hy : ∃ x, o x = y then o' hy.choose else Classical.arbitrary Z,
      fun x => ?_⟩
    have hex : ∃ x', o x' = o x := ⟨x, rfl⟩
    show o' x = if hy : ∃ x', o x' = o x then o' hy.choose else Classical.arbitrary Z
    rw [dif_pos hex]
    exact (h x hex.choose_spec).symm

/-- **The join of two observers is sequential kernel refinement.** -/
theorem refine_join (F : Set X) (O₁ : X → Y) (O₂ : X → Z) (y : Y) (z : Z) :
    refine F (obsChannel (Integration.CoordinateSufficiency.join O₁ O₂)) (y, z) =
      refine (refine F (obsChannel O₁) y) (obsChannel O₂) z := by
  ext x
  simp only [refine, refineBy, mem_inter_iff, mem_obsChannel_event,
    Integration.CoordinateSufficiency.join, Prod.mk.injEq, and_assoc]

end General

/-! ## §2 The coordinate version -/

section Coordinates

variable {I : Type*} {A : I → Type*} {Z : Type*}

/-- The projection onto a set of coordinates, as a kernel channel. -/
def projChannel (S : Set I) : Channel (∀ i, A i) (∀ i : S, A i.1) :=
  ⟨fun x i => x i.1⟩

theorem agreeOn_iff_proj_eq (S : Set I) (x y : ∀ i, A i) :
    Integration.CoordinateSufficiency.AgreeOn S x y ↔
      (projChannel (A := A) S).read x = (projChannel (A := A) S).read y := by
  constructor
  · intro h
    exact funext fun i => h i.1 i.2
  · intro h i hi
    exact congrFun h ⟨i, hi⟩

/-- Coordinate factorisation is the global sufficiency of the projection
channel. -/
theorem factorsOn_iff_determines (S : Set I) (C : (∀ i, A i) → Z) :
    Integration.CoordinateSufficiency.FactorsOn S C ↔
      Integration.CoordinateSufficiency.Determines (projChannel (A := A) S).read C := by
  constructor
  · intro h x y hxy
    exact h x y ((agreeOn_iff_proj_eq S x y).2 hxy)
  · intro h x y hxy
    exact h x y ((agreeOn_iff_proj_eq S x y).1 hxy)

/-- **The coordinate version of the weld**: factoring through a set of
coordinates is kernel closure on every fibre of the projection channel. -/
theorem factorsOn_iff_fibrewise [Nonempty Z] (S : Set I) (C : (∀ i, A i) → Z) :
    Integration.CoordinateSufficiency.FactorsOn S C ↔
      ∀ v : ∀ i : S, A i.1, Determines (event (projChannel (A := A) S) v) C := by
  rw [factorsOn_iff_determines]
  exact determines_iff_fibrewise _ _

/-- **A coordinate is essential exactly when a fibre carries a collision.**
The two-state witness of `Essential` is precisely a kernel collision inside one
fibre of the channel that forgets that coordinate. -/
theorem essential_iff_fibre_collision (j : I) (C : (∀ i, A i) → Z) :
    Integration.CoordinateSufficiency.Essential j C ↔
      ∃ v, Collision (event (projChannel (A := A) ({j}ᶜ : Set I)) v) C := by
  constructor
  · rintro ⟨x, y, hagree, hC⟩
    refine ⟨(projChannel (A := A) ({j}ᶜ : Set I)).read x, x, rfl, y, ?_, hC⟩
    exact ((agreeOn_iff_proj_eq _ y x).1 fun i hi => (hagree i hi).symm)
  · rintro ⟨v, x, hx, y, hy, hC⟩
    refine ⟨x, y, ?_, hC⟩
    have : (projChannel (A := A) ({j}ᶜ : Set I)).read x =
        (projChannel (A := A) ({j}ᶜ : Set I)).read y := by
      rw [mem_event.1 hx, mem_event.1 hy]
    exact fun i hi => (agreeOn_iff_proj_eq _ x y).2 this i hi

end Coordinates

/-! ## §3 The honest boundary -/

/-- **Closure on one fibre is not global sufficiency.**  A consumer can be
settled inside the fibre actually reached and still fail to factor through the
observation.  This is why the kernel's closure predicate is fibre-relative, and
why terminating the loop of `Integration.Kernel.Loop` is not identification. -/
theorem one_fibre_closure_is_not_global_sufficiency :
    ∃ (O : Bool × Bool → Bool) (C : Bool × Bool → Bool) (y : Bool),
      Determines (event (obsChannel O) y) C ∧
        ¬ Integration.CoordinateSufficiency.Determines O C := by
  refine ⟨Prod.fst, fun p => p.1 && p.2, false, ⟨false, ?_⟩, ?_⟩
  · rintro ⟨a, b⟩ hx
    have ha : a = false := hx
    subst ha
    rfl
  · intro h
    have := h (true, true) (true, false) rfl
    exact absurd this (by simp)

end Integration.Kernel.Instances.CoordinateSufficiencyBridge
