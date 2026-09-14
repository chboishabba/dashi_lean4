import Synthesis.SpinCoverBridge
import Integration.RecordConstraintAdequacy

/-!
# Repairing the three vacuous physics contracts

`Synthesis.PhysicsInterfaces` proved that three physics-facing interface records
constrain nothing:

* `AgdaMirror.GaugeGroupContract.UniquenessClaim` is satisfied by an emergence
  picking a non-Standard-Model group, because its own `admissible` predicate may
  be empty;
* `AgdaMirror.SpinEmergence.SpinEmergenceAxioms` has a field *named*
  `SpinIsDoubleCover` whose type is a bare map, and the bundle is inhabited with
  that map injective;
* `AgdaMirror.QuantumUnitary.Unitary` is satisfied by every invertible operator
  over the supplied trivial scalar carrier.

Those are countermodels, and by
`Integration.RecordConstraintAdequacy.adequate_iff_no_countermodel` a countermodel
is exactly a proof that a contract is not adequate for the property it is named
for.  This file supplies the **repairs**: strengthened contracts for which the
same countermodels are refuted, and which are still inhabited by the intended
models — the two halves that `Audited` demands.

The repairs are deliberately minimal; each is accompanied by the honest boundary
saying what it still does *not* give.

## Gauge

`SubstantiveUniquenessClaim` adds one field: an admissible state.

* `substantive_forces_SM` — a substantive claim really does force some state to
  pick `SM`; the original does not (`gauge_contract_permits_non_SM`).
* `nonSM_witness_impossible` — the old countermodel's admissibility predicate can
  never be completed to a substantive claim.
* `substantiveGaugeAudited` — the repaired contract is audited: sound for
  "some state picks `SM`", and witnessed.
* `substantive_still_permits_non_SM_elsewhere` — the boundary: a substantive
  claim may still pick `Other` on inadmissible states, so this is non-vacuity,
  not a uniqueness theorem.

## Spin

`DoubleCover` replaces the bare map by the property its name asserts: every
fibre has exactly two elements.

* `DoubleCover.not_injective`, `DoubleCover.surjective` — the property does the
  work: such a map is never injective and always onto.
* `q8DoubleCover` — the repaired contract is inhabited by the quaternion cover
  `Q8 → V4Rotation` of `Synthesis.SpinCoverBridge`, so it is not vacuous.
* `injective_cover_not_double`, `trivial_spin_not_double` — the countermodels of
  `Synthesis.PhysicsInterfaces` are refuted: an injective cover, and the trivial
  one-point bundle, cannot be given this structure.
* Boundary: `V4Rotation` is the Klein four-group, not `SO(3,1)`; the repair makes
  the *field* meaningful, not the model physical.

## Unitary

`SeparatingIPS` requires the scalar carrier to separate two points and the inner
product to detect a difference of vectors.

* `trivialIPS_not_separating` — the supplied trivial inner product fails it, which
  is precisely why `unitary_interface_trivially_satisfied` was possible.
* `realIPS` — the concrete real line with `⟪x,y⟫ = x*y` satisfies it, and there
  `unitary_preserves_square` forces `U x * U x = x * x`, hence
  `unitary_real_is_pm_id`: `U x = x` for all `x`, or `U x = -x` for all `x`.
* `scaling_not_unitary` — and the map `x ↦ 2*x`, invertible, is *not* unitary
  there.  So over a separating inner product the record has content.
-/

namespace Synthesis.ContractRepair

open AgdaMirror.GaugeGroupContract
open AgdaMirror.SpinEmergence
open AgdaMirror.OperatorTypes
open AgdaMirror.QuantumUnitary
open Integration.RecordConstraintAdequacy

/-! ## Gauge: the admissible set must be inhabited -/

/-- The gauge contract with the missing field supplied: an actual admissible
state.  Everything else is the original record. -/
structure SubstantiveUniquenessClaim (State : Type) where
  /-- The emergence map. -/
  E : Emergence State
  /-- The admissibility predicate. -/
  admissible : State → Bool
  /-- **The added field**: a state the predicate accepts. -/
  witness : State
  /-- … and the proof that it accepts it. -/
  witness_admissible : admissible witness = true
  /-- The original uniqueness hypothesis. -/
  unique_SM : ∀ s, admissible s = true → E.pickGauge s = Gauge.SM

/-- Every substantive claim is a claim of the original kind. -/
def SubstantiveUniquenessClaim.toClaim {State : Type}
    (C : SubstantiveUniquenessClaim State) : UniquenessClaim State where
  E := C.E
  admissible := C.admissible
  unique_SM := C.unique_SM

/-- **The repair works.**  A substantive claim forces some state to pick the
Standard Model tag — the statement the original record failed to deliver. -/
theorem substantive_forces_SM {State : Type} (C : SubstantiveUniquenessClaim State) :
    ∃ s, C.E.pickGauge s = Gauge.SM :=
  ⟨C.witness, C.unique_SM C.witness C.witness_admissible⟩

/-- **The old countermodel is refuted.**  `Synthesis.PhysicsInterfaces.nonSMClaim`
takes the empty admissibility predicate; no substantive claim can use it. -/
theorem nonSM_witness_impossible {State : Type}
    (C : SubstantiveUniquenessClaim State) : C.admissible ≠ (fun _ => false) := by
  intro h
  have := C.witness_admissible
  rw [h] at this
  exact Bool.noConfusion this

/-- The repaired contract is still inhabited: the constant Standard-Model
emergence with the always-admissible predicate. -/
def constSMSubstantive (State : Type) (s : State) : SubstantiveUniquenessClaim State where
  E := ⟨fun _ => Gauge.SM⟩
  admissible := fun _ => true
  witness := s
  witness_admissible := rfl
  unique_SM := fun _ _ => rfl

/-- **The gauge repair passes the audit**: sound for "some state picks `SM`", and
witnessed by a model that has that property. -/
def substantiveGaugeAudited (State : Type) (s : State) :
    Audited (fun _ : SubstantiveUniquenessClaim State => True)
      (fun C => ∃ t, C.E.pickGauge t = Gauge.SM) where
  sound := fun C _ => substantive_forces_SM C
  witness := constSMSubstantive State s
  witness_satisfies := trivial
  witness_intended := ⟨s, rfl⟩

/-- **The boundary.**  A substantive claim may still pick `Other` on states its
predicate rejects, so the repair buys non-vacuity, not gauge uniqueness. -/
theorem substantive_still_permits_non_SM_elsewhere :
    ∃ C : SubstantiveUniquenessClaim Bool, ∃ s, C.E.pickGauge s = Gauge.Other := by
  refine ⟨{ E := ⟨fun b => if b then Gauge.SM else Gauge.Other⟩
            admissible := fun b => b
            witness := true
            witness_admissible := rfl
            unique_SM := ?_ }, false, rfl⟩
  intro s hs
  cases s with
  | false => exact absurd hs (by simp)
  | true => rfl

/-! ## Spin: the field must assert the fibre count -/

/-- The property the field `SpinIsDoubleCover` is named for: every point of the
base has exactly two preimages. -/
structure DoubleCover (Spin Base : Type) [Fintype Spin] [DecidableEq Base] where
  /-- The covering map. -/
  cover : Spin → Base
  /-- Every fibre has exactly two points. -/
  fibre_card : ∀ b : Base, (Finset.univ.filter (fun s : Spin => cover s = b)).card = 2

variable {Spin Base : Type} [Fintype Spin] [DecidableEq Base]

/-- A double cover is surjective. -/
theorem DoubleCover.surjective (c : DoubleCover Spin Base) : Function.Surjective c.cover := by
  intro b
  have h : (Finset.univ.filter (fun s : Spin => c.cover s = b)).Nonempty := by
    rw [← Finset.card_pos, c.fibre_card b]
    exact Nat.succ_pos 1
  obtain ⟨s, hs⟩ := h
  exact ⟨s, (Finset.mem_filter.1 hs).2⟩

/-- **A double cover is never injective.**  This is exactly the content the bare
field lacked. -/
theorem DoubleCover.not_injective (c : DoubleCover Spin Base) [Nonempty Base] :
    ¬ Function.Injective c.cover := by
  intro hinj
  obtain ⟨b⟩ := ‹Nonempty Base›
  have hcard := c.fibre_card b
  have hle : (Finset.univ.filter (fun s : Spin => c.cover s = b)).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro x hx y hy
    exact hinj ((Finset.mem_filter.1 hx).2.trans (Finset.mem_filter.1 hy).2.symm)
  omega

/-- **Hence the countermodel is refuted.**  No injective map can be given the
repaired structure. -/
theorem injective_cover_not_double (f : Spin → Base) [Nonempty Base]
    (hf : Function.Injective f) : ¬ ∃ c : DoubleCover Spin Base, c.cover = f := by
  rintro ⟨c, rfl⟩
  exact c.not_injective hf

/-- In particular the trivial one-point bundle of
`AgdaMirror.SpinEmergence.trivialSpinEmergence` is not a double cover. -/
theorem trivial_spin_not_double : IsEmpty (DoubleCover PUnit PUnit) := by
  constructor
  intro c
  have := c.fibre_card PUnit.unit
  simp at this

instance : Nonempty AgdaMirror.FiniteQuaternionStrictCover.V4Rotation :=
  ⟨AgdaMirror.FiniteQuaternionStrictCover.V4Rotation.identityRotation⟩

/-- **The repair is inhabited**: the quaternion cover `Q8 → V4Rotation` of
`Synthesis.SpinCoverBridge` supplies the structure. -/
def q8DoubleCover : DoubleCover AgdaMirror.FiniteQuaternionStrictCover.Q8
    AgdaMirror.FiniteQuaternionStrictCover.V4Rotation where
  cover := AgdaMirror.FiniteQuaternionStrictCover.rho
  fibre_card := Synthesis.SpinCoverBridge.card_rho_fiber

/-- So the spin repair passes the audit: the structure implies non-injectivity,
and it is witnessed. -/
def spinRepairAudited :
    Audited (fun _ : DoubleCover AgdaMirror.FiniteQuaternionStrictCover.Q8
                AgdaMirror.FiniteQuaternionStrictCover.V4Rotation => True)
      (fun c => ¬ Function.Injective c.cover) where
  sound := fun c _ => c.not_injective
  witness := q8DoubleCover
  witness_satisfies := trivial
  witness_intended := q8DoubleCover.not_injective

/-! ## Unitary: the scalars and the inner product must separate -/

/-- The condition the unitary interface silently assumed: the scalar carrier has
two distinct values, and the inner product tells two distinct vectors apart. -/
structure Separating {A : ComplexAxioms} {S : Type} (IPS : InnerProductSpace A S) : Prop where
  /-- The scalar carrier is not a single point. -/
  scalars_separate : ∃ c d : A.C, c ≠ d
  /-- Distinct vectors are distinguished by the inner product against some vector. -/
  vectors_separate : ∀ x y : S, x ≠ y → ∃ z, IPS.inner x z ≠ IPS.inner y z

/-- **The supplied trivial inner product is not separating** — which is exactly
why every invertible operator satisfied the record. -/
theorem trivialIPS_not_separating (S : Type) : ¬ Separating (trivialIPS S) := by
  rintro ⟨⟨c, d, hcd⟩, -⟩
  exact hcd (Subsingleton.elim (α := PUnit) c d)

/-- The real line with its product as inner product. -/
def realComplex : ComplexAxioms where
  C := ℝ
  eqC := fun x y => x = y

/-- `⟪x, y⟫ = x * y` on `ℝ`. -/
def realIPS : InnerProductSpace realComplex ℝ where
  inner := fun x y => x * y

/-- It is separating. -/
theorem realIPS_separating : Separating realIPS := by
  refine ⟨⟨(0 : ℝ), (1 : ℝ), by norm_num⟩, ?_⟩
  intro x y hxy
  exact ⟨(1 : ℝ), by simpa [realIPS] using hxy⟩

/-- Over the separating real inner product the preservation field has content:
a unitary map preserves squares. -/
theorem unitary_preserves_square {U : ℝ → ℝ} (h : Unitary realIPS U) (x : ℝ) :
    U x * U x = x * x := h.preserves x x

/-- **Hence the repaired interface constrains the operator.**  Over `ℝ` a unitary
map is the identity or the negation — pointwise. -/
theorem unitary_real_is_pm_id {U : ℝ → ℝ} (h : Unitary realIPS U) (x : ℝ) :
    U x = x ∨ U x = -x := by
  have hx : U x * U x = x * x := unitary_preserves_square h x
  have : (U x - x) * (U x + x) = 0 := by nlinarith [hx]
  rcases mul_eq_zero.1 this with h₁ | h₂
  · left; linarith [sub_eq_zero.1 h₁]
  · right; linarith

/-- And the countermodel direction: doubling is invertible but not unitary over
the separating inner product, whereas over the trivial one it was
(`Synthesis.PhysicsInterfaces.unitary_interface_trivially_satisfied`). -/
theorem scaling_not_unitary : ¬ Nonempty (Unitary realIPS (fun x : ℝ => 2 * x)) := by
  rintro ⟨h⟩
  have := unitary_preserves_square h 1
  norm_num at this

/-- The unitary repair passes the audit on the real instance: every unitary map
there is `±id` pointwise, and the identity is one. -/
def unitaryRepairAudited :
    Audited (fun U : ℝ → ℝ => Nonempty (Unitary realIPS U))
      (fun U => ∀ x, U x = x ∨ U x = -x) where
  sound := by rintro U ⟨h⟩ x; exact unitary_real_is_pm_id h x
  witness := id
  witness_satisfies :=
    ⟨{ invertible := { inv := id, left := fun _ => rfl, right := fun _ => rfl }
       preserves := fun _ _ => rfl }⟩
  witness_intended := fun _ => Or.inl rfl

end Synthesis.ContractRepair
