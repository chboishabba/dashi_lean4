import Mathlib
import AgdaMirror.Base369
import AgdaMirror.DASHIAlgebra
import AgdaMirror.TritBridge
import AgdaMirror.HalfTrit
import AgdaMirror.HalfTritIndexed

/-!
# Synthesis layer 0: the shared ternary tone primitive

This file isolates the *one* primitive that every domain in the supplied
material actually shares: a three-element cyclic "tone" carrier with a
distinguished order-3 rotation.

Provenance of the inputs (all taken from the repository, none re-defined here):

* `AgdaMirror.Base369.TriTruth`, `rotateTri`, `triXor` — the ternary universe.
* `AgdaMirror.DASHIAlgebra.Trit`, `Trit.inv` — the balanced-ternary digit.
* `AgdaMirror.TritBridge.toTriTruth` / `fromTriTruth` — the supplied bridge maps
  (their round-trip laws `toFrom` / `fromTo` are the supplied proofs).
* `AgdaMirror.HalfTritMod.HalfTrit`, `embedTrit`, `invHalfTrit` — the five-position
  half-trit refinement and its (necessarily non-injective) forgetful map.
* `AgdaMirror.HalfTritIndexedMod` — the `Fin 5` index of the half-trit fibre.

New content proved here:

* the supplied bridge maps are packaged as an honest `Equiv` (`tritToneEquiv`),
  and it is an isomorphism of the induced ternary XOR structures;
* the tone carrier is identified with `ZMod 3` (`toneZMod`), so "ternary
  operator" statements downstream are statements about `ℤ/3`;
* the half-trit fibre is identified with `Fin 5` (`halfTritEquivFin5`), and the
  tone of a half-trit factors through that index;
* the exact fibre sizes of the half-trit → tone collapse (`2, 1, 2`), which is
  the precise quantitative form of the supplied non-injectivity statement;
* `rotateTri` has no fixed point — the fact that later rules out any
  rotation-equivariant tone for a four-position dialectic.

Nothing here is a physical claim: `TriTruth` is a three-element set.
-/

namespace Synthesis.ToneCore

open AgdaMirror.Base369
open AgdaMirror.DASHIAlgebra (Trit)
open AgdaMirror.TritBridge
open AgdaMirror.HalfTritMod (HalfTrit embedTrit invHalfTrit)
open AgdaMirror.HalfTritIndexedMod (HalfTritIndexed embedIndexed indexedToFin finToIndexed)

/-! ## Finiteness of the supplied carriers -/

instance : Fintype Trit :=
  ⟨{.neg, .zer, .pos}, fun x => by cases x <;> decide⟩
instance : Fintype TriTruth :=
  ⟨{.low, .mid, .high}, fun x => by cases x <;> decide⟩
instance : Fintype HalfTrit :=
  ⟨{.negOne, .negHalf, .zero, .posHalf, .posOne}, fun x => by cases x <;> decide⟩
instance : Fintype HalfTritIndexed :=
  ⟨{.indexedNegOne, .indexedNegHalf, .indexedZero, .indexedPosHalf, .indexedPosOne},
    fun x => by cases x <;> decide⟩

/-! ## The `Trit ≃ TriTruth` bridge, packaged -/

/-- The supplied bridge maps assembled into an equivalence.  Both round-trip
proofs are the ones supplied in `AgdaMirror.TritBridge`. -/
def tritToneEquiv : Trit ≃ TriTruth where
  toFun := toTriTruth
  invFun := fromTriTruth
  left_inv := fromTo
  right_inv := toFrom

@[simp] theorem tritToneEquiv_apply (t : Trit) : tritToneEquiv t = toTriTruth t := rfl

/-- The bridge carries the induced digit XOR to the ternary XOR: it is an
isomorphism of ternary operator structures, not merely of carriers. -/
theorem tritToneEquiv_xor (a b : Trit) :
    tritToneEquiv (tritXor a b) = triXor (tritToneEquiv a) (tritToneEquiv b) :=
  triXor_equivariant a b

/-- ... and it carries the digit rotation to the tone rotation. -/
theorem tritToneEquiv_rot (t : Trit) :
    tritToneEquiv (rotTrit t) = rotateTri (tritToneEquiv t) :=
  rotTrit_equivariant_to t

/-! ## The tone carrier is `ZMod 3` -/

/-- Tone as an element of `ℤ/3`. -/
def toneToZMod : TriTruth → ZMod 3
  | .low => 0
  | .mid => 1
  | .high => 2

/-- `ℤ/3` back to a tone. -/
def zmodToTone (z : ZMod 3) : TriTruth :=
  if z = 0 then .low else if z = 1 then .mid else .high

/-- The tone carrier *is* `ℤ/3`. -/
def toneZMod : TriTruth ≃ ZMod 3 where
  toFun := toneToZMod
  invFun := zmodToTone
  left_inv := by decide
  right_inv := by decide

/-- The ternary XOR of `Base369` is addition in `ℤ/3`. -/
theorem toneZMod_xor (a b : TriTruth) :
    toneZMod (triXor a b) = toneZMod a + toneZMod b := by
  cases a <;> cases b <;> decide

/-- The rotation of `Base369` is `+1` in `ℤ/3`. -/
theorem toneZMod_rot (t : TriTruth) : toneZMod (rotateTri t) = toneZMod t + 1 := by
  cases t <;> decide

/-- The rotation has no fixed point.  This is the obstruction used in
`Synthesis.DialecticTone`. -/
theorem rotateTri_no_fixpoint (t : TriTruth) : rotateTri t ≠ t := by cases t <;> decide

/-- Consequently the rotation has order exactly 3 (it is not the identity, and
its cube is). -/
theorem rotateTri_order_three :
    (∀ t, rotateTri (rotateTri (rotateTri t)) = t) ∧ ∃ t, rotateTri t ≠ t :=
  ⟨rotateTri_cubed, ⟨.low, by decide⟩⟩

/-! ## Tone reflection versus tone rotation -/

/-- Tone reflection: the image of digit negation under the bridge. -/
def triReflect : TriTruth → TriTruth
  | .low => .high
  | .mid => .mid
  | .high => .low

/-- The bridge carries digit negation to tone reflection. -/
theorem tritToneEquiv_inv (t : Trit) :
    tritToneEquiv (Trit.inv t) = triReflect (tritToneEquiv t) := by cases t <;> rfl

theorem triReflect_invol (t : TriTruth) : triReflect (triReflect t) = t := by
  cases t <;> rfl

/-- Reflection is not a rotation power: the supplied `Trit`-level obstruction
transported to the tone carrier. -/
theorem triReflect_ne_rot :
    triReflect ≠ rotateTri ∧ triReflect ≠ (rotateTri ∘ rotateTri) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact absurd (congrFun h TriTruth.low) (by decide)
  · exact absurd (congrFun h TriTruth.mid) (by decide)

/-! ## The half-trit fibre and its five-element index -/

/-- The tone of a half-trit: the supplied forgetful map followed by the bridge. -/
def halfTone (x : HalfTrit) : TriTruth := toTriTruth (embedTrit x)

/-- The half-trit carrier is exactly its `Fin 5` coordinate index: the supplied
`embedIndexed` and `indexedToFin` compose to an equivalence. -/
def halfTritEquivFin5 : HalfTrit ≃ Fin 5 where
  toFun x := indexedToFin (embedIndexed x)
  invFun i :=
    match finToIndexed i with
    | .indexedNegOne => .negOne
    | .indexedNegHalf => .negHalf
    | .indexedZero => .zero
    | .indexedPosHalf => .posHalf
    | .indexedPosOne => .posOne
  left_inv := by decide
  right_inv := by decide

/-- The tone of a half-trit factors through its `Fin 5` index. -/
def indexTone : Fin 5 → TriTruth
  | 0 => .low
  | 1 => .low
  | 2 => .mid
  | 3 => .high
  | 4 => .high

theorem halfTone_factors (x : HalfTrit) : halfTone x = indexTone (halfTritEquivFin5 x) := by
  cases x <;> rfl

/-- The collapse is surjective onto the tone carrier. -/
theorem halfTone_surjective : Function.Surjective halfTone := by
  intro t; cases t
  · exact ⟨.negOne, rfl⟩
  · exact ⟨.zero, rfl⟩
  · exact ⟨.posOne, rfl⟩

/-- Exact fibre sizes of the half-trit → tone collapse: the signed positions
come in pairs, the zero position is alone.  This is the quantitative form of the
supplied `embedTrit_not_injective`. -/
theorem halfTone_fibre_card (t : TriTruth) :
    (Finset.univ.filter (fun x : HalfTrit => halfTone x = t)).card =
      if t = .mid then 1 else 2 := by
  cases t <;> decide

/-- The collapse is genuinely lossy: distinct half-trits share a tone. -/
theorem halfTone_not_injective : ¬ Function.Injective halfTone := by
  intro h
  exact absurd (h (show halfTone .negOne = halfTone .negHalf from rfl)) (by decide)

/-- The half-trit sign flip descends to the tone reflection. -/
theorem halfTone_inv (x : HalfTrit) : halfTone (invHalfTrit x) = triReflect (halfTone x) := by
  cases x <;> rfl

end Synthesis.ToneCore
