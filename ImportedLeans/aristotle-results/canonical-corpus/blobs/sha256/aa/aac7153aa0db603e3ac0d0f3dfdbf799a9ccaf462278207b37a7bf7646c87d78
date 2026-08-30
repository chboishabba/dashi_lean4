import Integration.StructureMorphism

/-!
# Equivariant equivalence forces orbit invariants to agree

A proposed identification of two carriers that both carry an action of the same
group is not merely a bijection: it must intertwine the actions.  Once it does,
every orbit-theoretic invariant is forced to agree, and a mismatch of orbit data
kills the identification before any further analysis.  This file owns that
argument.

Contents.

* `EquivariantEquivalence` — a bijection intertwining two actions of the same
  group;
* `fixed_iff`, `stabilizer_eq`, `period_iff` — the invariants that are forced to
  agree: fixed-point sets correspond, stabilizers are literally equal, and the
  period/order spectrum is preserved;
* `orbit_image` — orbits correspond;
* `no_equivariant_of_free_and_fixed` — **the no-go**: a free action admits no
  equivariant equivalence with an action that has a fixed point of a nontrivial
  element;
* `translation_free`, `trivial_fixed`,
  `card_equal_but_not_equivariantly_equivalent` — the concrete instance on two
  three-element carriers: the free `C₃` translation and the trivial `C₃` action.
  They have equal cardinality, so the obstruction really is orbit structure and
  not counting;
* `translation_free_group`, `no_equivariant_free_shift_to_ramified` — the `5 × 3`
  case: the free translation action of `C₅ × C₃` on itself admits no equivariant
  equivalence with *any* action of the same group having a fixed point of a
  nontrivial element.  The target carrier is arbitrary, so no counting argument
  is involved.

Every statement is about an arbitrary monoid or group action; the instance uses
`ZMod 3`.
-/

namespace Integration.EquivarianceObstruction

variable {G X Y : Type*}

/-! ## The structure -/

/-- A bijection that intertwines two actions of the same group. -/
structure EquivariantEquivalence (G X Y : Type*) (act : G → X → X) (act' : G → Y → Y) where
  /-- The underlying bijection. -/
  toEquiv : X ≃ Y
  /-- It intertwines the actions. -/
  equivariant : ∀ g x, toEquiv (act g x) = act' g (toEquiv x)

namespace EquivariantEquivalence

variable {act : G → X → X} {act' : G → Y → Y}

/-- **Fixed points correspond.** -/
theorem fixed_iff (E : EquivariantEquivalence G X Y act act') (g : G) (x : X) :
    act g x = x ↔ act' g (E.toEquiv x) = E.toEquiv x := by
  constructor
  · intro h
    rw [← E.equivariant g x, h]
  · intro h
    have := E.equivariant g x
    rw [h] at this
    exact E.toEquiv.injective this

/-- **Stabilizers are equal.** -/
theorem stabilizer_eq (E : EquivariantEquivalence G X Y act act') (x : X) :
    {g : G | act g x = x} = {g : G | act' g (E.toEquiv x) = E.toEquiv x} := by
  ext g
  exact E.fixed_iff g x

/-- **The period spectrum is preserved.** -/
theorem period_iff (E : EquivariantEquivalence G X Y act act') (g : G) (x : X) (n : ℕ) :
    (act g)^[n] x = x ↔ (act' g)^[n] (E.toEquiv x) = E.toEquiv x := by
  have hcomm : ∀ m : ℕ, ∀ y : X, E.toEquiv ((act g)^[m] y) = (act' g)^[m] (E.toEquiv y) := by
    intro m
    induction m with
    | zero => intro y; rfl
    | succ m ih =>
      intro y
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih (act g y),
        E.equivariant g y]
  constructor
  · intro h
    rw [← hcomm n x, h]
  · intro h
    exact E.toEquiv.injective ((hcomm n x).trans h)

/-- **Orbits correspond.** -/
theorem orbit_image (E : EquivariantEquivalence G X Y act act') (x y : X) :
    (∃ g, act g x = y) ↔ ∃ g, act' g (E.toEquiv x) = E.toEquiv y := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, (E.equivariant g x).symm⟩
  · rintro ⟨g, hg⟩
    refine ⟨g, E.toEquiv.injective ?_⟩
    rw [E.equivariant g x, hg]

end EquivariantEquivalence

/-! ## The no-go -/

/-- The action has no nontrivial fixed points. -/
def Free (act : G → X → X) (e : G) : Prop := ∀ g x, g ≠ e → act g x ≠ x

/-- **The obstruction.**  A free action is not equivariantly equivalent to one
with a fixed point of a nontrivial element. -/
theorem no_equivariant_of_free_and_fixed {act : G → X → X} {act' : G → Y → Y} {e : G}
    (hfree : Free act e) {g₀ : G} {y₀ : Y} (hg₀ : g₀ ≠ e) (hfix : act' g₀ y₀ = y₀) :
    IsEmpty (EquivariantEquivalence G X Y act act') := by
  constructor
  intro E
  have hx : act g₀ (E.toEquiv.symm y₀) = E.toEquiv.symm y₀ := by
    rw [E.fixed_iff g₀ (E.toEquiv.symm y₀), Equiv.apply_symm_apply]
    exact hfix
  exact hfree g₀ (E.toEquiv.symm y₀) hg₀ hx

/-! ## The concrete instance: equal cardinality, different orbit structure -/

/-- The free translation action of `C₃` on itself. -/
def translation (g : ZMod 3) (x : ZMod 3) : ZMod 3 := g + x

/-- The trivial action of `C₃` on the same carrier. -/
def trivialAct (_ : ZMod 3) (x : ZMod 3) : ZMod 3 := x

/-- Translation is free. -/
theorem translation_free : Free translation 0 := by
  intro g x hg h
  apply hg
  have : g = 0 := by
    have := congrArg (fun z => z - x) h
    simpa [translation, sub_eq_add_neg] using this
  exact this

/-- The trivial action fixes everything, in particular a nontrivial element has
a fixed point. -/
theorem trivial_fixed : trivialAct 1 0 = 0 := rfl

/-- **Equal cardinality is not enough.**  Both carriers are the same
three-element set, yet there is no equivariant equivalence: the obstruction is
the orbit structure. -/
theorem card_equal_but_not_equivariantly_equivalent :
    Nat.card (ZMod 3) = 3 ∧
      IsEmpty (EquivariantEquivalence (ZMod 3) (ZMod 3) (ZMod 3) translation trivialAct) :=
  ⟨by simp, no_equivariant_of_free_and_fixed translation_free (by decide) trivial_fixed⟩

/-! ## The `5 × 3` shift: a free translation cannot be labelled by a ramified
action -/

/-- Left translation of any additive group on itself is free. -/
theorem translation_free_group {A : Type*} [AddGroup A] :
    Free (fun g x : A => g + x) 0 := by
  intro g x hg h
  exact hg (by simpa using congrArg (fun z => z - x) h)

/-- **The `5 × 3` no-go.**  The free translation action of `C₅ × C₃` on itself
admits no equivariant equivalence with *any* action of the same group that has a
fixed point of a nontrivial element — in particular with a class action carrying
a unique fixed/ramified point.  The target carrier is arbitrary, so no counting
argument is involved: the obstruction is purely the presence of a fixed
point. -/
theorem no_equivariant_free_shift_to_ramified {Y : Type*}
    (act' : ZMod 5 × ZMod 3 → Y → Y) {g₀ : ZMod 5 × ZMod 3} {y₀ : Y}
    (hg₀ : g₀ ≠ 0) (hfix : act' g₀ y₀ = y₀) :
    IsEmpty (EquivariantEquivalence (ZMod 5 × ZMod 3) (ZMod 5 × ZMod 3) Y
      (fun g x => g + x) act') :=
  no_equivariant_of_free_and_fixed translation_free_group hg₀ hfix

/-- The carrier really has fifteen elements, so the no-go above is not a
cardinality statement in disguise. -/
theorem card_shift_carrier : Nat.card (ZMod 5 × ZMod 3) = 15 := by simp

/-! ## The map-level obstruction

`no_equivariant_of_free_and_fixed` refutes an *equivalence*.  Often the honest
statement is stronger and cheaper: there is no equivariant **function** at all,
in either direction, as soon as one side's self-map has a fixed point and the
other's has none.  This is the obstruction behind
`Integration.Ontology.no_polarity_equivariant_forcing`. -/

/-- A self-map with no fixed point. -/
def FixedPointFree {B : Type*} (τ : B → B) : Prop := ∀ b, τ b ≠ b

/-- **No equivariant map from a fixed point into a fixed-point-free target.**
If `σ a = a` for some `a` and `τ` has no fixed point, then no `f : A → B`
satisfies `f ∘ σ = τ ∘ f`.  No bijectivity, finiteness or group structure is
assumed: `σ` and `τ` are arbitrary self-maps. -/
theorem no_equivariant_map_of_fixed_to_free {A B : Type*} {σ : A → A} {τ : B → B}
    {a : A} (ha : σ a = a) (hτ : FixedPointFree τ) :
    ¬ ∃ f : A → B, ∀ x, f (σ x) = τ (f x) := by
  rintro ⟨f, hf⟩
  exact hτ (f a) (by rw [← hf a, ha])

/-- Boolean negation is fixed-point free. -/
theorem fixedPointFree_not : FixedPointFree (fun b : Bool => !b) := fun b => Bool.not_ne_self b


end Integration.EquivarianceObstruction
