import Integration.PhaseQuotient
import Integration.ObserverQuotient

/-!
# Symmetry reduction as a typed structure: `π (g · x) = ḡ · π x`

The integration spine already contains several projections that are usually
described informally as "symmetry reductions": the free `C₃` output-phase
quotient `27 → 9` of `TernaryEndomorphismPhaseQuotientExact.agda`, the polarity
quotient `Trit → Bool` of the magnitude observer, and the SSP orientation action
on lane states.  This file gives that pattern **one structure** so that being a
symmetry reduction is a typed obligation rather than a description, and then
inhabits it.

* `EquivariantQuotient G Rich Coarse` — a monoid action on each layer, a
  surjective projection, and the commuting square
  `proj (g · x) = g · proj x`.  Nothing else; in particular the coarse action is
  *data*, so an instance must exhibit the reduced action rather than assert one
  exists.
* `orbit_invariant` — if the coarse action is trivial then the projection is
  constant on orbits, which is the "quotient by a symmetry" case.
* `phaseReduction` — the `27 → 9` free `C₃` output-phase quotient, with trivial
  coarse action.  This is the reduction that produces the nine-state carrier;
  `Integration.PhaseQuotient.q9_nonary_group_iso_impossible` is about the two
  *algebras* the nine labels carry, and does not bear on this reduction.
* `polarReduction` — the magnitude observer `Trit → Bool` for the SSP
  orientation action, again with trivial coarse action.
* `laneReduction` — an instance with **nontrivial** coarse action: the SSP
  orientation acts diagonally on a pair of lane states and the first-coordinate
  projection intertwines it with the same action downstairs.  So the structure is
  not vacuously satisfied by trivial-action examples only.
* `support_no_equivariant_action` — the **boundary**, stated at the right level:
  the native-chart support observer admits *no* coarse action at all making the
  square commute, for the single generating symmetry.  This is a strictly
  stronger and better-scoped negative than "support is not a homomorphism for
  boolean OR": the failure is already at the unary symmetry, before any binary
  law is considered, and it is a property of that particular observer, not of the
  SSP layer.

Scope: these are finite carriers and finite monoid actions.  No statement about
Hecke operators or Monster representations is made here; the corresponding
square for a prime-indexed representation action is recorded in the registry as
an open socket, not as a theorem.
-/

namespace Integration.SymmetryReduction

open Integration.PhaseQuotient
open Integration.SSPWeave
open Integration.ObserverQuotient
open AgdaMirror.DASHIAlgebra (Trit)
open Synthesis.Hyperfabric (support)

/-! ## The structure -/

/-- A **symmetry reduction**: monoid actions on a rich and a coarse layer,
together with a surjective projection intertwining them.  The coarse action is a
field, so inhabiting this structure means exhibiting the reduced action. -/
structure EquivariantQuotient (G Rich Coarse : Type) [Monoid G] where
  /-- The action on the rich layer. -/
  actRich : G → Rich → Rich
  /-- The induced action on the coarse layer. -/
  actCoarse : G → Coarse → Coarse
  /-- The reduction map. -/
  proj : Rich → Coarse
  /-- The rich action is unital. -/
  rich_one : ∀ x, actRich 1 x = x
  /-- The rich action is multiplicative. -/
  rich_mul : ∀ g h x, actRich (g * h) x = actRich g (actRich h x)
  /-- The coarse action is unital. -/
  coarse_one : ∀ y, actCoarse 1 y = y
  /-- The coarse action is multiplicative. -/
  coarse_mul : ∀ g h y, actCoarse (g * h) y = actCoarse g (actCoarse h y)
  /-- The reduction is onto. -/
  proj_surjective : Function.Surjective proj
  /-- The commuting square `π (g · x) = ḡ · π x`. -/
  square : ∀ g x, proj (actRich g x) = actCoarse g (proj x)

variable {G Rich Coarse : Type} [Monoid G]

/-- The square iterates: a word in the symmetry acts the same way on both
layers. -/
theorem square_mul (Q : EquivariantQuotient G Rich Coarse) (g h : G) (x : Rich) :
    Q.proj (Q.actRich g (Q.actRich h x)) = Q.actCoarse g (Q.actCoarse h (Q.proj x)) := by
  rw [← Q.rich_mul, Q.square, Q.coarse_mul]

/-- If the induced action is trivial then the reduction is constant on orbits:
this is the "quotient by a symmetry" special case. -/
theorem orbit_invariant (Q : EquivariantQuotient G Rich Coarse)
    (htriv : ∀ g y, Q.actCoarse g y = y) (g : G) (x : Rich) :
    Q.proj (Q.actRich g x) = Q.proj x := by
  rw [Q.square, htriv]

/-! ## Instance 1: the free `C₃` output-phase reduction `27 → 9` -/

/-- Composition of output-phase rotations. -/
def phaseCompose : Phase3 → Phase3 → Phase3
  | .p0, q => q
  | .p1, .p0 => .p1 | .p1, .p1 => .p2 | .p1, .p2 => .p0
  | .p2, .p0 => .p2 | .p2, .p1 => .p0 | .p2, .p2 => .p1

instance instMonoidPhase3 : Monoid Phase3 where
  mul := phaseCompose
  one := .p0
  mul_assoc a b c := by revert a b c; decide
  one_mul a := rfl
  mul_one a := by cases a <;> rfl

theorem phase_mul_eq (a b : Phase3) : a * b = phaseCompose a b := rfl

theorem rotateByPhase_one (c : LevelTwoCode) : rotateByPhase 1 c = c := rfl

theorem rotateByPhase_mul (a b : Phase3) (c : LevelTwoCode) :
    rotateByPhase (a * b) c = rotateByPhase a (rotateByPhase b c) := by
  revert a b c; decide

theorem phaseQuotient_invariant (a : Phase3) (c : LevelTwoCode) :
    (phaseEquiv (rotateByPhase a c)).2 = (phaseEquiv c).2 := by
  revert a c; decide

/-- **The `27 → 9` symmetry reduction.**  The free `C₃` output-phase action on
the ternary endomorphism codes, projected to the nine-element orbit carrier, with
the induced action trivial. -/
def phaseReduction : EquivariantQuotient Phase3 LevelTwoCode PhaseQuotient9 where
  actRich := rotateByPhase
  actCoarse := fun _ y => y
  proj := fun c => (phaseEquiv c).2
  rich_one := rotateByPhase_one
  rich_mul := rotateByPhase_mul
  coarse_one := fun _ => rfl
  coarse_mul := fun _ _ _ => rfl
  proj_surjective := by decide
  square := phaseQuotient_invariant

/-! ## Instance 2: the polarity/magnitude reduction `Trit → Bool` -/

theorem tritAction_one (t : Trit) : tritAction 1 t = t := by cases t <;> rfl

/-- **The magnitude reduction.**  The SSP orientation action on a ternary digit
projects to the polarity-invariant Boolean observer, with trivial induced
action. -/
def polarReduction : EquivariantQuotient FibreOrientation Trit Bool where
  actRich := tritAction
  actCoarse := fun _ y => y
  proj := polarPresence
  rich_one := tritAction_one
  rich_mul := fun g h t => tritAction_comp g h t
  coarse_one := fun _ => rfl
  coarse_mul := fun _ _ _ => rfl
  proj_surjective := polarPresence_surjective
  square := fun g t => polarPresence_equivariant g t

/-! ## Instance 3: a reduction with nontrivial induced action -/

/-- **A symmetry reduction whose induced action is not trivial.**  The SSP
orientation acts diagonally on a pair of lane states and the first-coordinate
projection intertwines it with the same action on a single lane state.  This
witnesses that `EquivariantQuotient` is not satisfiable only by orbit maps. -/
def laneReduction : EquivariantQuotient FibreOrientation (Trit × Trit) Trit where
  actRich := fun g p => (tritAction g p.1, tritAction g p.2)
  actCoarse := tritAction
  proj := Prod.fst
  rich_one := fun p => by
    cases p with | mk a b => simp [tritAction_one]
  rich_mul := fun g h p => by
    cases p with | mk a b => simp [tritAction_comp, HMul.hMul, Mul.mul]
  coarse_one := tritAction_one
  coarse_mul := fun g h t => tritAction_comp g h t
  proj_surjective := fun t => ⟨(t, t), rfl⟩
  square := fun _ _ => rfl

theorem laneReduction_action_nontrivial :
    ∃ g t, laneReduction.actCoarse g t ≠ t :=
  ⟨.inverse, Trit.neg, by decide⟩

/-! ## The boundary, correctly scoped -/

/-- **Boundary: the native-chart support observer is not a symmetry reduction at
all.**  There is no map on the Boolean layer — not merely no *sensible* one —
making the square commute for the polarity generator.  The failure is at the
unary symmetry, so it is prior to, and stronger than, the failure of `support` to
be a homomorphism for a binary law; and it is a statement about this observer's
choice of origin, not about the SSP layer, whose action does descend
(`polarReduction`). -/
theorem support_no_equivariant_action :
    ¬ ∃ f : Bool → Bool, ∀ t : Trit, support (Trit.inv t) = f (support t) := by
  rintro ⟨f, h⟩
  have h1 := h Trit.zer
  have h2 := h Trit.pos
  rcases Bool.eq_false_or_eq_true (f true) with hf | hf <;>
    simp [support, hf] at h1 h2 <;> revert h1 h2 <;> decide

/-- The same statement for the whole orientation monoid: no `EquivariantQuotient`
structure on the SSP orientation action can have `support` as its projection. -/
theorem support_not_a_reduction :
    ¬ ∃ Q : EquivariantQuotient FibreOrientation Trit Bool,
        Q.actRich = tritAction ∧ Q.proj = support := by
  rintro ⟨Q, hact, hproj⟩
  refine support_no_equivariant_action ⟨Q.actCoarse .inverse, fun t => ?_⟩
  have := Q.square .inverse t
  rw [hact, hproj] at this
  rwa [tritAction_inverse] at this

/-! ## Summary -/

/-- The four facts of this file in one statement: the phase reduction, the
magnitude reduction, a reduction with nontrivial induced action, and the failure
of the native-chart support observer to be any reduction at all. -/
theorem symmetry_reduction_summary :
    (∀ (a : Phase3) (c : LevelTwoCode),
        phaseReduction.proj (phaseReduction.actRich a c) = phaseReduction.proj c) ∧
      (∀ (g : FibreOrientation) (t : Trit),
        polarReduction.proj (polarReduction.actRich g t) = polarReduction.proj t) ∧
      (∃ g t, laneReduction.actCoarse g t ≠ t) ∧
      (¬ ∃ Q : EquivariantQuotient FibreOrientation Trit Bool,
        Q.actRich = tritAction ∧ Q.proj = support) :=
  ⟨fun a c => orbit_invariant phaseReduction (fun _ _ => rfl) a c,
    fun g t => orbit_invariant polarReduction (fun _ _ => rfl) g t,
    laneReduction_action_nontrivial,
    support_not_a_reduction⟩

end Integration.SymmetryReduction
