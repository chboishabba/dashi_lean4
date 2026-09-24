import Synthesis.Vec15Fibre
import AgdaMirror.GaugeGroupContract
import AgdaMirror.SpinEmergence
import AgdaMirror.QuantumUnitary
import AgdaMirror.PhysicsConformance

/-!
# Synthesis layer 2'''''': what the physics-facing interfaces actually contain

The repository carries four records whose *names* suggest physical content:
`AgdaMirror.GaugeGroupContract`, `AgdaMirror.SpinEmergence`,
`AgdaMirror.QuantumUnitary` and `AgdaMirror.PhysicsConformance`.  The dependency
map lists them as an open obligation ("replace the finite enumerations by actual
groups/operators").  This file settles, by proof, *how much* they currently
constrain — which is the honest prerequisite for that obligation.

Negative results (each an explicit witness, so each is a theorem, not a stance):

* `gauge_contract_permits_non_SM` — the gauge "uniqueness claim" record is
  satisfiable by an emergence that picks a non-Standard-Model group on a given
  state, because the record quantifies only over states its own `admissible`
  predicate accepts, and that predicate is unconstrained.  So inhabiting the
  record proves nothing about gauge groups;
* `gauge_contract_both_values` — both values of the `Gauge` tag are reachable
  inside satisfied claims, so the tag carries no distinguished element;
* `spin_interface_no_double_cover` — the "spin is a double cover" field is a bare
  map `SpinGroup → SO 3 1`; there is a bundle in which it is injective, so the
  interface does not express a double cover;
* `unitary_interface_trivially_satisfied` — with the supplied trivial scalar
  field (whose equality relation is `True`), *every* invertible operator is
  "unitary", so the preservation field is vacuous there.

Positive results — the one interface that does have transportable content is the
conformance predicate, and it lands in the Monster mask fibre:

* `conformsOn_iff_eq` — over the supplied one-point state carrier, conformance on
  any non-empty table is exactly equality of the two scanners;
* `conformsOn_scan_iff_mask_eq` — for scanned lenses, conformance is exactly
  equality of the two compatibility masks over the prime base;
* `conformsOn_scan_iff_dSSP_zero` — equivalently, distance zero in the supplied
  Monster mask ultrametric.

Nothing here asserts or refutes any physical statement; the theorems are about
the records as written.
-/

namespace Synthesis.PhysicsInterfaces

open AgdaMirror.MonsterOntos (SSP)
open AgdaMirror.GaugeGroupContract
open AgdaMirror.SpinEmergence
open AgdaMirror.QuantumUnitary
open AgdaMirror.PhysicsSignature
open AgdaMirror.PhysicsConformance
open Synthesis.MonsterFibre
open Synthesis.Vec15Fibre

/-! ## The gauge contract constrains nothing -/

/-- A satisfied uniqueness claim whose emergence picks a non-Standard-Model
group on the given state: the claim's `admissible` predicate is part of the
record, so it can be empty. -/
def nonSMClaim (State : Type) : UniquenessClaim State where
  E := ⟨fun _ => Gauge.Other⟩
  admissible := fun _ => false
  unique_SM := by intro s hs; exact absurd hs (by simp)

/-- **The gauge contract does not force the Standard Model.**  For every state
carrier and every state there is a record of type `UniquenessClaim` — all of
whose fields hold — whose emergence picks `Other` on that state. -/
theorem gauge_contract_permits_non_SM (State : Type) (s : State) :
    ∃ C : UniquenessClaim State, C.E.pickGauge s = Gauge.Other :=
  ⟨nonSMClaim State, rfl⟩

/-- Both values of the gauge tag occur inside satisfied claims, so inhabiting
the contract distinguishes neither. -/
theorem gauge_contract_both_values (State : Type) (s : State) :
    (∃ C : UniquenessClaim State, C.E.pickGauge s = Gauge.SM) ∧
    (∃ C : UniquenessClaim State, C.E.pickGauge s = Gauge.Other) :=
  ⟨⟨constSMClaim State, rfl⟩, ⟨nonSMClaim State, rfl⟩⟩

/-- The Standard-Model witness is genuinely different from the `Other` witness:
the tag itself is a two-element type. -/
theorem gauge_tag_two_valued : Gauge.SM ≠ Gauge.Other := by decide

/-! ## The spin interface does not express a double cover -/

/-- **The `SpinIsDoubleCover` field is a bare map.**  There is a bundle of the
supplied type in which it is injective, hence not two-to-one over any point; so
inhabiting `SpinEmergenceAxioms` says nothing about covers. -/
theorem spin_interface_no_double_cover :
    ¬ ∀ A : SpinEmergenceAxioms.{0}, ∀ x : A.SO 3 1,
        ∃ a b : A.SpinGroup, a ≠ b ∧
          A.SpinIsDoubleCover a = x ∧ A.SpinIsDoubleCover b = x := by
  intro h
  obtain ⟨a, b, hab, -, -⟩ := h trivialSpinEmergence PUnit.unit
  exact hab rfl

/-- Positively: the interface is inhabited by *arbitrary* data — it is a plain
tuple with no laws, so it imposes no condition on its carriers. -/
def spinAxiomsOfData (Q : Type) (q : Q) (Cl : Q → Type) (Sp : Type)
    (SOf : Nat → Nat → Type) (f : Sp → SOf 3 1) : SpinEmergenceAxioms where
  QuadraticForm := Q
  Signature31 := q
  CliffordAlgebra := Cl
  SpinGroup := Sp
  SO := SOf
  SpinIsDoubleCover := f

/-! ## The unitary interface is vacuous over the supplied scalar field -/

/-- **Every invertible operator is "unitary" for the supplied trivial scalar
field**, because its equality relation is `True`: the preservation field carries
no information until the scalars are replaced by actual complex numbers. -/
def unitary_interface_trivially_satisfied {S : Type} (U : S → S)
    (hU : AgdaMirror.OperatorTypes.Invertible U) : Unitary (trivialIPS S) U where
  invertible := hU
  preserves := fun _ _ => trivial

/-- In particular a non-identity operator can be "unitary" there: the interface
does not pin the operator down. -/
theorem unitary_interface_admits_nontrivial :
    ∃ U : Bool → Bool, Nonempty (Unitary (trivialIPS Bool) U) ∧
      AgdaMirror.OperatorTypes.Nontrivial U := by
  refine ⟨not, ⟨unitary_interface_trivially_satisfied not ⟨not, ?_, ?_⟩⟩, ?_⟩
  · intro x; cases x <;> rfl
  · intro x; cases x <;> rfl
  · intro h
    exact absurd (h true) (by decide)

/-! ## Conformance is mask equality in the Monster fibre -/

/-- Over the supplied one-point state carrier, conformance on a non-empty table
is exactly equality of the two scanners. -/
theorem conformsOn_iff_eq (f g : State → Sig15) {xs : List State} (hxs : xs ≠ []) :
    ConformsOn f g xs ↔ f = g := by
  constructor
  · intro h
    obtain ⟨s, ss, rfl⟩ : ∃ s ss, xs = s :: ss := by
      cases xs with
      | nil => exact absurd rfl hxs
      | cons s ss => exact ⟨s, ss, rfl⟩
    cases s
    funext t
    cases t
    exact h.1
  · rintro rfl
    exact conformsOn_self f xs

/-- For scanned lenses, conformance is exactly equality of the two compatibility
masks over the supersingular prime base. -/
theorem conformsOn_scan_iff_mask_eq (L₁ L₂ : Lens) {xs : List State} (hxs : xs ≠ []) :
    ConformsOn (scan L₁) (scan L₂) xs ↔
      sig15Equiv (scan L₁ State.st) = sig15Equiv (scan L₂ State.st) := by
  rw [conformsOn_iff_eq _ _ hxs]
  constructor
  · intro h; rw [h]
  · intro h
    funext s
    cases s
    exact sig15Equiv.injective h

/-- Equivalently: conformance is distance zero in the supplied Monster mask
ultrametric. -/
theorem conformsOn_scan_iff_dSSP_zero (L₁ L₂ : Lens) {xs : List State} (hxs : xs ≠ []) :
    ConformsOn (scan L₁) (scan L₂) xs ↔
      dSSP (sig15Equiv (scan L₁ State.st)) (sig15Equiv (scan L₂ State.st)) = 0 := by
  rw [conformsOn_scan_iff_mask_eq _ _ hxs, dSSP_eq_zero_iff]

/-- Conformance of scanned lenses is pointwise agreement of their compatibility
predicates on the fifteen primes. -/
theorem conformsOn_scan_iff_compat (L₁ L₂ : Lens) {xs : List State} (hxs : xs ≠ []) :
    ConformsOn (scan L₁) (scan L₂) xs ↔
      ∀ p : SSP, L₁.Compat p State.st = L₂.Compat p State.st := by
  rw [conformsOn_scan_iff_mask_eq _ _ hxs, sig15Equiv_scan, sig15Equiv_scan]
  constructor
  · intro h p; exact congrFun h p
  · intro h; funext p; exact h p

/-- The empty table is no constraint at all: any two scanners conform on it. -/
theorem conformsOn_nil_vacuous (f g : State → Sig15) : ConformsOn f g [] := trivial

end Synthesis.PhysicsInterfaces
