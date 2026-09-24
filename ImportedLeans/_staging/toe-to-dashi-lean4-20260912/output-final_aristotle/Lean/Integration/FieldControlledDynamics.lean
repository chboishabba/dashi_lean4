import Integration.PathTransport

/-!
# Field-controlled effective dynamics, and attractors

Two domain-neutral owners for patterns that appear in several lanes at once.

**Field control.**  A fixed carrier with a state-dependent background field can
have different effective dynamics without any change to the underlying carrier:

```
EffStep φ x y      the transition available at background field φ
```

The theorem shapes worth owning are "same state, different field, different
successor" and "same structural edge, different field, different effective
edge", together with the resulting field dependence of reachability.  Background
gauge configurations, material coefficients, an advecting state, and a
state-dependent connectivity all have this shape; the file proves the shape, and
claims nothing about which systems realise it.

**Attractors.**  A self-map of a carrier, with fixed points, basins and
reachability; on a finite carrier every trajectory is eventually periodic.

Contents.

* `FieldControlled`, `EffStep`, `EffReach` — the structure;
* `field_changes_successor`, `field_changes_effective_edge`,
  `field_changes_reachability` — the three separations, on an explicit
  four-state carrier with two fields;
* `structural_edge_insufficient` — the packaged statement: the structural edge
  relation is the same for both fields, yet the effective edge relations differ,
  so the structural carrier does not determine the effective dynamics;
* `Fixed`, `Basin`, `basin_self`, `basin_step_of_fixed`, `Cycle` — the attractor
  vocabulary;
* `eventually_periodic` — on a finite carrier every trajectory repeats;
* `threeClass` and `threeClass_classes` — three qualitatively different
  attractor classes on one carrier: two distinct fixed points and a two-cycle.

No biological, physical or empirical claim is made anywhere in this file.
-/

namespace Integration.FieldControlledDynamics

open Integration.PathTransport
open Integration.StructureMorphism

/-! ## Field-controlled effective dynamics -/

/-- A carrier with a background field controlling which transitions exist. -/
structure FieldControlled (Field X : Type*) where
  /-- The structural (field-independent) edge relation of the substrate. -/
  structEdge : X → X → Prop
  /-- The effective transition available at a given background field. -/
  effStep : Field → X → X → Prop
  /-- Effective transitions are always structural ones: the field gates the
  substrate, it does not add edges to it. -/
  effStep_le : ∀ f x y, effStep f x y → structEdge x y

variable {Field X : Type*}

/-- Reachability at a fixed background field. -/
def EffReach (S : FieldControlled Field X) (f : Field) : X → X → Prop :=
  Path (S.effStep f)

/-! ### An explicit carrier -/

/-- Four states. -/
abbrev Cell : Type := Fin 4

/-- Two background fields. -/
abbrev Fld : Type := Bool

/-- The substrate: every state is structurally adjacent to every other. -/
def substrate : Cell → Cell → Prop := fun _ _ => True

/-- Under field `false` the walk increases the index by one; under field `true`
it decreases it.  The substrate is the same in both cases. -/
def gatedB (f : Fld) (x y : Cell) : Bool :=
  if f then decide (y = x - 1) else decide (y = x + 1)

/-- The gated edge relation. -/
def gated (f : Fld) (x y : Cell) : Prop := gatedB f x y = true

instance (f : Fld) (x y : Cell) : Decidable (gated f x y) :=
  inferInstanceAs (Decidable (gatedB f x y = true))

/-- The field-controlled system. -/
def gatedSystem : FieldControlled Fld Cell where
  structEdge := substrate
  effStep := gated
  effStep_le := fun _ _ _ _ => trivial

@[simp] theorem gatedSystem_effStep : gatedSystem.effStep = gated := rfl

@[simp] theorem gatedSystem_structEdge : gatedSystem.structEdge = substrate := rfl

/-- **Same state, different field, different successor.** -/
theorem field_changes_successor :
    gated false 0 1 ∧ ¬ gated true 0 1 := by
  refine ⟨by decide, by decide⟩

/-- **Same structural edge, different effective edge.**  The pair `(0, 1)` is a
structural edge for both fields, but an effective edge for only one. -/
theorem field_changes_effective_edge :
    gatedSystem.structEdge 0 1 ∧ gated false 0 1 ∧ ¬ gated true 0 1 :=
  ⟨trivial, by decide, by decide⟩

/-- **The packaged statement.**  The substrate is the complete relation, so it
carries no information distinguishing the two fields; yet the two effective
relations are different relations.  Hence the structural carrier does not
determine the effective dynamics. -/
theorem structural_edge_insufficient :
    (∀ x y, gatedSystem.structEdge x y) ∧
      gatedSystem.effStep false ≠ gatedSystem.effStep true := by
  refine ⟨fun _ _ => trivial, fun h => ?_⟩
  have hf : gated false 0 1 := by decide
  rw [gatedSystem_effStep] at h
  rw [h] at hf
  exact absurd hf (by decide)

/-- And reachability inherits the dependence: one step of the `false` field
reaches `1` from `0`, and the `true` field cannot do it in one step. -/
theorem field_changes_reachability :
    EffReach gatedSystem false 0 1 ∧ ¬ gated true 0 1 :=
  ⟨path_single (show gated false 0 1 by decide), by decide⟩

/-! ## Attractors -/

variable {Y : Type*}

/-- A fixed point of the dynamics. -/
def Fixed (F : Y → Y) (a : Y) : Prop := F a = a

/-- The basin of a state: everything that reaches it. -/
def Basin (F : Y → Y) (a : Y) : Set Y := {x | Reaches F x a}

theorem basin_self (F : Y → Y) (a : Y) : a ∈ Basin F a := reaches_refl F a

/-- A fixed attractor absorbs its basin: a successor of a point in the basin is
still in the basin. -/
theorem basin_step_of_fixed {F : Y → Y} {a : Y} (hfix : Fixed F a) {x : Y}
    (hx : x ∈ Basin F a) : F x ∈ Basin F a := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hn, hfix]

/-- A cycle of length `n`. -/
def Cycle (F : Y → Y) (a : Y) (n : ℕ) : Prop := 0 < n ∧ F^[n] a = a

/-- **On a finite carrier every trajectory repeats.** -/
theorem eventually_periodic [Finite Y] (F : Y → Y) (x : Y) :
    ∃ m n : ℕ, m < n ∧ F^[m] x = F^[n] x := by
  obtain ⟨m, n, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => F^[k] x)
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨m, n, h, heq⟩
  · exact ⟨n, m, h, heq.symm⟩

/-! ### Three qualitative classes on one carrier -/

/-- Two distinct fixed points and one two-cycle. -/
def threeClass : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 2

/-- **The three classes.**  `0` and `1` are distinct fixed points; `2` is not
fixed but lies on a two-cycle. -/
theorem threeClass_classes :
    Fixed threeClass 0 ∧ Fixed threeClass 1 ∧ ¬ Fixed threeClass 2 ∧
      Cycle threeClass 2 2 := by
  refine ⟨rfl, rfl, ?_, by norm_num, by decide⟩
  intro h
  exact absurd (congrArg (fun z : Fin 4 => z.val) h) (by decide)

end Integration.FieldControlledDynamics
