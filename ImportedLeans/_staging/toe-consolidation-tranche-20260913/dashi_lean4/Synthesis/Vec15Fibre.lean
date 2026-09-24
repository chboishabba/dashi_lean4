import Synthesis.MonsterFibre
import AgdaMirror.GodelLattice
import AgdaMirror.PhysicsSignature

/-!
# Synthesis layer 2''': the 15-slot record carriers are fibres over the base

Two further carriers in the repository are *written as flat 15-field records*
rather than as functions on the prime base:

* `AgdaMirror.GodelLattice.Vec15 A` — the "canonical coordinate", with slots
  named `e2 … e71`, a prime-indexed update `updateVec15 : SSP → …`, and the
  `map`/`zipWith`/`sum` aggregation API;
* `AgdaMirror.PhysicsSignature.Sig15` — the 15-bit signature produced by scanning
  a per-prime compatibility lens.

Proved here: both are the *same fibre* over the supersingular prime base that
`Synthesis.MonsterFibre` works with, and the record-level API is the pointwise
API transported along that identification.

* `vec15Equiv : Vec15 A ≃ (SSP → A)`, natural in `A`
  (`vec15Equiv_map`, `vec15Equiv_zipWith`, `vec15Equiv_replicate`);
* `vec15Equiv_update` — the prime-indexed slot update is `Function.update`;
* `vec15Equiv_sum` — the record sum is the sum over the base;
* `sig15Equiv : Sig15 ≃ MaskSSP` with `sig15Equiv_scan`: a scanned physics
  signature is exactly the mask `fun p => L.Compat p s`;
* consequently signatures inherit the Monster mask geometry:
  `sig15_dist_pos` (distinct signatures are at positive distance) and
  `sig15_projection_contractive`.

Boundary: `Sig15` is a 15-bit record and `Lens.Compat` is an uninterpreted
boolean predicate.  Calling it a "physics signature" is the source material's
naming; no physical content is asserted or used here.
-/

namespace Synthesis.Vec15Fibre

open AgdaMirror.MonsterOntos (SSP)
open AgdaMirror.GodelLattice (Vec15)
open AgdaMirror.PhysicsSignature (Sig15)
open Synthesis.MonsterFibre

/-! ## `Vec15` is the fibre over the base -/

/-- Read the slot selected by a prime. -/
def vec15At {A : Type*} (v : Vec15 A) : SSP → A
  | .p2 => v.e2 | .p3 => v.e3 | .p5 => v.e5 | .p7 => v.e7 | .p11 => v.e11
  | .p13 => v.e13 | .p17 => v.e17 | .p19 => v.e19 | .p23 => v.e23
  | .p29 => v.e29 | .p31 => v.e31 | .p41 => v.e41 | .p47 => v.e47
  | .p59 => v.e59 | .p71 => v.e71

/-- Assemble a record from a section. -/
def vec15Of {A : Type*} (f : SSP → A) : Vec15 A :=
  ⟨f .p2, f .p3, f .p5, f .p7, f .p11, f .p13, f .p17, f .p19, f .p23,
   f .p29, f .p31, f .p41, f .p47, f .p59, f .p71⟩

/-- **The 15-slot record carrier is the fibre over the prime base.** -/
def vec15Equiv {A : Type*} : Vec15 A ≃ (SSP → A) where
  toFun := vec15At
  invFun := vec15Of
  left_inv := by intro v; cases v; rfl
  right_inv := by intro f; funext p; cases p <;> rfl

@[simp] theorem vec15Equiv_apply {A : Type*} (v : Vec15 A) (p : SSP) :
    vec15Equiv v p = vec15At v p := rfl

theorem vec15Equiv_replicate {A : Type*} (x : A) :
    vec15Equiv (AgdaMirror.GodelLattice.replicate x) = fun _ => x := by
  funext p; cases p <;> rfl

theorem vec15Equiv_map {A B : Type*} (f : A → B) (v : Vec15 A) :
    vec15Equiv (AgdaMirror.GodelLattice.map f v) = fun p => f (vec15Equiv v p) := by
  funext p; cases p <;> rfl

theorem vec15Equiv_zipWith {A B C : Type*} (f : A → B → C) (u : Vec15 A) (v : Vec15 B) :
    vec15Equiv (AgdaMirror.GodelLattice.zipWith f u v) =
      fun p => f (vec15Equiv u p) (vec15Equiv v p) := by
  funext p; cases p <;> rfl

/-- The prime-indexed slot update is pointwise `Function.update`. -/
theorem vec15Equiv_update {A : Type*} (p : SSP) (f : A → A) (v : Vec15 A) :
    vec15Equiv (AgdaMirror.GodelLattice.updateVec15 p f v) =
      fun q => if p = q then f (vec15Equiv v q) else vec15Equiv v q := by
  funext q
  cases q <;>
    simp [AgdaMirror.GodelLattice.updateVec15, AgdaMirror.GodelLattice.updateField, vec15At]

/-- Enumeration of a sum over the prime base. -/
theorem sum_over_base {M : Type*} [AddCommMonoid M] (f : SSP → M) :
    ∑ p : SSP, f p = f .p2 + f .p3 + f .p5 + f .p7 + f .p11 + f .p13 + f .p17 + f .p19
      + f .p23 + f .p29 + f .p31 + f .p41 + f .p47 + f .p59 + f .p71 := by
  rw [← Equiv.sum_comp sspEquivFin15.symm f]
  simp [Fin.sum_univ_succ, sspEquivFin15, finToSsp, add_assoc]

/-- The record sum is the sum over the base. -/
theorem vec15Equiv_sum (v : Vec15 Nat) :
    AgdaMirror.GodelLattice.sum v = ∑ p : SSP, vec15Equiv v p := by
  rw [sum_over_base]
  simp [AgdaMirror.GodelLattice.sum, vec15At]

/-! ## `Sig15` is the mask fibre -/

/-- Read the bit selected by a prime. -/
def sigAt (s : Sig15) : SSP → Bool
  | .p2 => s.b2 | .p3 => s.b3 | .p5 => s.b5 | .p7 => s.b7 | .p11 => s.b11
  | .p13 => s.b13 | .p17 => s.b17 | .p19 => s.b19 | .p23 => s.b23
  | .p29 => s.b29 | .p31 => s.b31 | .p41 => s.b41 | .p47 => s.b47
  | .p59 => s.b59 | .p71 => s.b71

/-- Assemble a signature from a mask. -/
def sigOf (m : MaskSSP) : Sig15 :=
  ⟨m .p2, m .p3, m .p5, m .p7, m .p11, m .p13, m .p17, m .p19, m .p23,
   m .p29, m .p31, m .p41, m .p47, m .p59, m .p71⟩

/-- **A 15-bit signature is a point of the Monster mask fibre.** -/
def sig15Equiv : Sig15 ≃ MaskSSP where
  toFun := sigAt
  invFun := sigOf
  left_inv := by intro s; cases s; rfl
  right_inv := by intro m; funext p; cases p <;> rfl

/-- Scanning a lens produces exactly the mask of per-prime compatibility. -/
theorem sig15Equiv_scan (L : AgdaMirror.PhysicsSignature.Lens)
    (s : AgdaMirror.PhysicsSignature.State) :
    sig15Equiv (AgdaMirror.PhysicsSignature.scan L s) = fun p => L.Compat p s := by
  funext p; cases p <;> rfl

/-- Distinct signatures are at positive distance in the Monster mask geometry. -/
theorem sig15_dist_pos {x y : Sig15} (h : x ≠ y) : 0 < dSSP (sig15Equiv x) (sig15Equiv y) := by
  rcases Nat.eq_zero_or_pos (dSSP (sig15Equiv x) (sig15Equiv y)) with h0 | hpos
  · exact absurd (sig15Equiv.injective ((dSSP_eq_zero_iff _ _).mp h0)) h
  · exact hpos

/-- The constant Monster projection strictly contracts distances between
distinct signatures. -/
theorem sig15_projection_contractive (target : MaskSSP) {x y : Sig15} (h : x ≠ y) :
    dSSP (projectSSP target (sig15Equiv x)) (projectSSP target (sig15Equiv y)) <
      dSSP (sig15Equiv x) (sig15Equiv y) :=
  projectSSP_contractive target fun he => h (sig15Equiv.injective he)

end Synthesis.Vec15Fibre
