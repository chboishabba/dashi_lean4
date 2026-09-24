import Integration.FactorisationCollision

/-!
# Typed bridges: what a claimed identification has to carry, and its four statuses

The corpus already owns two halves of this.  `Spine.EqualCardinality` proves that
equal size never gives a canonical identification, and
`Integration.StructureMorphism` owns the commuting square once, in its exact,
approximate, sound and gauge tiers.  What is missing is the object in between:
a **bridge that declares what it preserves**, together with the classification of
what such a bridge can be.

A `System` here is a carrier with a dynamics and an observation.  A `Bridge`
between two systems is a map *plus* the two preservation laws

```
    obs₂ (f x) = obs₁ x                (the observation is preserved)
    f (step₁ x) = step₂ (f x)          (the dynamics is preserved)
```

so a bridge cannot be constructed from a map alone, and never from a shared name
or a shared cardinality.

## The four statuses

| status | condition | what it means |
|---|---|---|
| `IsEquivalence` | bijective | the two systems are interchangeable |
| `IsRefinement` | injective | the source's distinctions all survive |
| `IsQuotient` | surjective, not injective | controlled loss, with a residual |
| incompatible | no bridge exists | the desired identification is refuted |

Proved:

* `isEquivalence_iff` — a bridge is an equivalence exactly when it is both a
  refinement and onto, so the statuses are not independent labels;
* `IsQuotient.residual` — a quotient bridge *exhibits* its loss as an
  `Integration.FactorisationCollision.Collision`, hence
  `IsQuotient.state_not_recoverable`: no reading of the target returns the source
  state;
* `IsRefinement.reflects` — a refinement reflects every property of the target,
  which is the transport a refinement licenses and a quotient does not;
* `Bridge.transport_reachability` — the dynamics law gives transport of the whole
  orbit, `f (step₁^[n] x) = step₂^[n] (f x)`;
* `no_bridge_of_fixed_point_mismatch` — the incompatible case with a proof: if the
  source dynamics has a fixed point and the target's is fixed-point free, **no**
  map satisfies the dynamics law, whatever else it preserves;
* `no_bridge_of_observation_mismatch` — likewise if some observed value of the
  source is not observed anywhere in the target;
* `map_without_laws_is_not_a_bridge` — and the point of the whole file: two
  systems can be joined by a bijection of carriers while no bridge exists
  between them;
* `bridge_existence_is_directional` — on that same pair, a bridge does exist the
  other way, so "these correspond" is not a symmetric relation.

Everything is generic; the carriers in the witnesses are `Bool` and `Fin 3`.
-/

namespace Integration.BridgeStatus

open Integration.FactorisationCollision

/-- A carrier with a dynamics and an observation into a shared language. -/
structure System (O : Type) where
  /-- The state space. -/
  carrier : Type
  /-- One step of the dynamics. -/
  step : carrier → carrier
  /-- What an observer reads off a state. -/
  obs : carrier → O

variable {O : Type}

/-- A **bridge**: a map together with the laws it preserves.  There is no way to
build one out of a map alone. -/
structure Bridge (S T : System O) where
  /-- The underlying map. -/
  map : S.carrier → T.carrier
  /-- It preserves what observers see. -/
  preserves_obs : ∀ x, T.obs (map x) = S.obs x
  /-- It intertwines the two dynamics. -/
  preserves_step : ∀ x, map (S.step x) = T.step (map x)

namespace Bridge

variable {S T : System O}

/-- The dynamics law iterates: a bridge transports whole orbits. -/
theorem transport_orbit (b : Bridge S T) (n : Nat) (x : S.carrier) :
    b.map (S.step^[n] x) = T.step^[n] (b.map x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, b.preserves_step]

/-- Reachability transports along a bridge. -/
theorem transport_reachability (b : Bridge S T) {x y : S.carrier} {n : Nat}
    (h : S.step^[n] x = y) : T.step^[n] (b.map x) = b.map y := by
  rw [← transport_orbit b n x, h]

/-- The bridge is an **equivalence**: the two systems are interchangeable. -/
def IsEquivalence (b : Bridge S T) : Prop := Function.Bijective b.map

/-- The bridge is a **refinement**: every distinction of the source survives. -/
def IsRefinement (b : Bridge S T) : Prop := Function.Injective b.map

/-- The bridge is a **quotient**: onto, but losing distinctions. -/
def IsQuotient (b : Bridge S T) : Prop :=
  Function.Surjective b.map ∧ ¬ Function.Injective b.map

/-- The statuses are not independent labels: an equivalence is exactly a
refinement that is onto. -/
theorem isEquivalence_iff (b : Bridge S T) :
    b.IsEquivalence ↔ b.IsRefinement ∧ Function.Surjective b.map :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- A bridge cannot be both an equivalence and a quotient. -/
theorem not_equivalence_and_quotient (b : Bridge S T) :
    ¬ (b.IsEquivalence ∧ b.IsQuotient) := by
  rintro ⟨he, -, hni⟩
  exact hni he.1

/-- **A refinement reflects.**  Any property of target states pulls back, and a
refinement never identifies two source states, so the pullback is faithful. -/
theorem IsRefinement.reflects {b : Bridge S T} (h : b.IsRefinement)
    {x y : S.carrier} (hxy : b.map x = b.map y) : x = y := h hxy

/-- **A quotient exhibits its loss.**  Its residual is a collision of the bridge
map against the source state itself. -/
noncomputable def IsQuotient.residual {b : Bridge S T} (h : b.IsQuotient) :
    Collision b.map (id : S.carrier → S.carrier) :=
  Collision.ofNotInjective h.2

/-- Hence the source state is not recoverable from the target: no reading of the
target returns it. -/
theorem IsQuotient.state_not_recoverable {b : Bridge S T} (h : b.IsQuotient)
    (r : T.carrier → S.carrier) : ¬ ∀ x, x = r (b.map x) :=
  (IsQuotient.residual h).no_reading r

end Bridge

/-! ## The incompatible case -/

/-- **A dynamical obstruction refutes every bridge.**  If the source dynamics has
a fixed point and the target's has none, no map satisfies the dynamics law — so
no bridge exists, however suggestive the two systems look. -/
theorem no_bridge_of_fixed_point_mismatch {S T : System O}
    {x : S.carrier} (hx : S.step x = x) (hT : ∀ y, T.step y ≠ y) :
    IsEmpty (Bridge S T) := by
  constructor
  intro b
  have h := b.preserves_step x
  rw [hx] at h
  exact hT (b.map x) h.symm

/-- **An observational obstruction refutes every bridge.**  If some value the
source observes is observed nowhere in the target, no bridge exists. -/
theorem no_bridge_of_observation_mismatch {S T : System O}
    (x : S.carrier) (h : ∀ y : T.carrier, T.obs y ≠ S.obs x) :
    IsEmpty (Bridge S T) := by
  constructor
  intro b
  exact h (b.map x) (b.preserves_obs x)

/-! ## A bijection of carriers is not a bridge -/

/-- Two states, the identity dynamics, both observed as `true`. -/
def fixedSystem : System Bool where
  carrier := Bool
  step := id
  obs := fun _ => true

/-- Two states, the flip dynamics, both observed as `true`. -/
def flipSystem : System Bool where
  carrier := Bool
  step := not
  obs := fun _ => true

/-- The carriers are the same type and the observations agree everywhere. -/
theorem carriers_are_bijective : Function.Bijective (id : Bool → Bool) :=
  Function.bijective_id

/-- **Yet there is no bridge.**  The identity dynamics has fixed points and the
flip has none, so nothing intertwines them: matching carriers, matching
observation language and matching cardinality do not make an identification. -/
theorem map_without_laws_is_not_a_bridge : IsEmpty (Bridge fixedSystem flipSystem) :=
  no_bridge_of_fixed_point_mismatch (x := true) rfl
    (by intro y; cases y <;> simp [flipSystem])

/-- In the *other* direction a bridge does exist: the constant map intertwines the
flip with the identity, because the identity absorbs it. -/
def flipToFixed : Bridge flipSystem fixedSystem where
  map := fun _ => true
  preserves_obs := fun _ => rfl
  preserves_step := fun _ => rfl

/-- It is of course not a refinement — it is exactly the loss the flip suffers. -/
theorem flipToFixed_not_refinement : ¬ flipToFixed.IsRefinement := by
  intro h
  exact Bool.noConfusion (h (a₁ := true) (a₂ := false) rfl)

/-- **Bridge existence is directional.**  Between the very same pair of carriers,
with the very same observation language, a bridge exists one way and provably not
the other.  So "these two systems correspond" is not a symmetric relation, and a
bridge found in one direction licenses nothing in the other. -/
theorem bridge_existence_is_directional :
    Nonempty (Bridge flipSystem fixedSystem) ∧ IsEmpty (Bridge fixedSystem flipSystem) :=
  ⟨⟨flipToFixed⟩, map_without_laws_is_not_a_bridge⟩

/-! ## A genuine quotient -/

/-- Three states cycling, observed by nothing (a one-point language). -/
def cycleSystem : System Unit where
  carrier := Bool
  step := not
  obs := fun _ => ()

/-- One state, observed by nothing. -/
def pointSystem : System Unit where
  carrier := Unit
  step := id
  obs := fun _ => ()

/-- The collapse to a point is a bridge … -/
def collapse : Bridge cycleSystem pointSystem where
  map := fun _ => ()
  preserves_obs := fun _ => rfl
  preserves_step := fun _ => rfl

/-- … and it is a quotient: onto, and not injective. -/
theorem collapse_isQuotient : collapse.IsQuotient := by
  constructor
  · intro y; exact ⟨true, by cases y; rfl⟩
  · intro h
    exact Bool.noConfusion (h (a₁ := true) (a₂ := false) rfl)

/-- So the state is not recoverable through it, and — the useful corollary — a
system can be observationally indistinguishable from a point while its dynamics
is not the point's. -/
theorem collapse_loses_the_state (r : Unit → Bool) :
    ¬ ∀ x, x = r (collapse.map x) :=
  Bridge.IsQuotient.state_not_recoverable collapse_isQuotient r

end Integration.BridgeStatus
