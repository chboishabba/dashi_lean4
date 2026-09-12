import Synthesis.Hyperfabric
import TriadicKernelAlgebra

/-!
# Synthesis layer 3': the hyperfabric is a triadic codec kernel

`TriadicKernelAlgebra` (recovered from the DASHI form-constant work, and
self-contained: it imports only Mathlib) develops a balanced-ternary codec
algebra whose depth-`d` *kernel* is `K_d = Fin d → ZMod 3`, with `|K_d| = 3 ^ d`
and an inversion action `u ↦ -u` whose orbit count is `(3 ^ d + 1) / 2`.

`Synthesis.Hyperfabric` builds, from an entirely different part of the
repository, the section space `Fabric = SSP → Trit` of the ternary fibre over
the 15-element supersingular prime base.

These are the same object at depth 15.  Proved here:

* `fabricKernelEquiv : Fabric ≃ (Fin 15 → ZMod 3)`, the identification, taken in
  the *balanced-ternary* reading `neg ↦ -1, zer ↦ 0, pos ↦ 1`;
* `fabricKernelEquiv_neg` — it carries the pointwise digit negation `Trit.inv`
  to the codec's inversion action `u ↦ -u`;
* `card_fabric_eq_pow` — the section count is the supplied `card_kernel 15`;
* `fabricOrbits_eq` / `fabricOrbits_value` — the number of inversion orbits of
  Monster hyperfabrics is the supplied `orbitCount 15 = (3 ^ 15 + 1)/2 = 7174454`;
* an honest mismatch, `fabricKernelEquiv_xor_affine` and
  `xor_neutral_is_minus_one`: the supplied ternary XOR of `AgdaMirror.TritBridge`
  is *not* balanced-ternary addition — its neutral element is the digit `neg`,
  i.e. `-1`, so in balanced coordinates XOR is the affine operation
  `u + v + 1`.  The two ternary operations in the repository therefore agree only
  up to a translation, and this is proved rather than glossed.

Boundary: this bridges two *formalisms* in this repository.  The document's
reading of the codec (perception, form constants) is provenance, not theorem,
and nothing about it is asserted here.  Note also what is deliberately *not*
bridged: the codec's "5 trits per byte" statement concerns `Fin 5 → ZMod 3` and
has no structural relation to the five-position half-trit fibre of
`Synthesis.ToneCore` — the shared numeral 5 is a coincidence, not a map.
-/

namespace Synthesis.CodecBridge

open AgdaMirror.DASHIAlgebra (Trit)
open AgdaMirror.MonsterOntos (SSP)
open Synthesis.ToneCore
open Synthesis.MonsterFibre
open Synthesis.Hyperfabric

/-! ## The balanced-ternary reading of a digit -/

/-- The balanced-ternary value of a digit: `neg ↦ -1`, `zer ↦ 0`, `pos ↦ 1`. -/
def tritValue : Trit → ZMod 3
  | .neg => -1
  | .zer => 0
  | .pos => 1

/-- Back from a value to a digit. -/
def valueTrit (z : ZMod 3) : Trit :=
  if z = 0 then .zer else if z = 1 then .pos else .neg

/-- The digit type is `ℤ/3` in its balanced-ternary reading. -/
def tritBalanced : Trit ≃ ZMod 3 where
  toFun := tritValue
  invFun := valueTrit
  left_inv := by decide
  right_inv := by decide

/-- In this reading, digit negation is negation. -/
theorem tritBalanced_inv (t : Trit) : tritBalanced (Trit.inv t) = - tritBalanced t := by
  cases t <;> decide

/-- The supplied ternary XOR is *not* balanced addition: it is addition
translated by one. -/
theorem tritBalanced_xor (a b : Trit) :
    tritBalanced (AgdaMirror.TritBridge.tritXor a b) = tritBalanced a + tritBalanced b + 1 := by
  cases a <;> cases b <;> decide

/-- Concretely, the XOR-neutral digit is `-1`, not `0`. -/
theorem xor_neutral_is_minus_one : tritBalanced .neg = -1 := rfl

/-! ## The hyperfabric as a depth-15 kernel -/

/-- Pointwise digit negation of a hyperfabric. -/
def fabricInv (F : Fabric) : Fabric := fun p => Trit.inv (F p)

/-- **The Monster hyperfabric is the depth-15 triadic kernel.** -/
def fabricKernelEquiv : Fabric ≃ (Fin 15 → ZMod 3) :=
  Equiv.arrowCongr sspEquivFin15 tritBalanced

@[simp] theorem fabricKernelEquiv_apply (F : Fabric) (i : Fin 15) :
    fabricKernelEquiv F i = tritBalanced (F (sspEquivFin15.symm i)) := rfl

/-- The identification carries pointwise digit negation to kernel inversion. -/
theorem fabricKernelEquiv_neg (F : Fabric) :
    fabricKernelEquiv (fabricInv F) = - fabricKernelEquiv F := by
  funext i
  simpa [fabricInv] using tritBalanced_inv (F (sspEquivFin15.symm i))

/-- ... and carries the supplied ternary XOR to the affine kernel operation. -/
theorem fabricKernelEquiv_xor_affine (x y : Fabric) :
    fabricKernelEquiv (fabricXor x y) =
      fabricKernelEquiv x + fabricKernelEquiv y + 1 := by
  funext i
  simpa [fabricXor] using tritBalanced_xor (x (sspEquivFin15.symm i)) (y (sspEquivFin15.symm i))

theorem card_fabric_eq_kernel : Fintype.card Fabric = Fintype.card (Fin 15 → ZMod 3) :=
  Fintype.card_congr fabricKernelEquiv

theorem card_fabric_eq_pow : Fintype.card Fabric = 3 ^ 15 :=
  card_fabric_eq_kernel.trans (TriadicKernelAlgebra.card_kernel 15)

/-! ## Inversion orbits -/

/-- Transport of an unordered-pair orbit count along an equivalence intertwining
the two involutions. -/
theorem pair_image_card_transport {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (e : A ≃ B) (f : A → A) (g : B → B)
    (h : ∀ a, e (f a) = g (e a)) :
    (Finset.univ.image (fun a : A => ({a, f a} : Finset A))).card
      = (Finset.univ.image (fun b : B => ({b, g b} : Finset B))).card := by
  have hinj : Function.Injective (fun S : Finset A => S.image e) :=
    Finset.image_injective e.injective
  calc (Finset.univ.image (fun a : A => ({a, f a} : Finset A))).card
      = ((Finset.univ.image (fun a : A => ({a, f a} : Finset A))).image
          (fun S => S.image e)).card := (Finset.card_image_of_injective _ hinj).symm
    _ = (Finset.univ.image (fun a : A => ({e a, g (e a)} : Finset B))).card := by
        rw [Finset.image_image]
        congr 1
        refine Finset.image_congr ?_
        intro a _
        simp [Finset.image_insert, h a]
    _ = ((Finset.univ.image e).image (fun b : B => ({b, g b} : Finset B))).card := by
        rw [Finset.image_image]; rfl
    _ = (Finset.univ.image (fun b : B => ({b, g b} : Finset B))).card := by
        rw [Finset.image_univ_of_surjective e.surjective]

/-- Inversion orbits of Monster hyperfabrics, in the supplied
unordered-pair form. -/
def fabricOrbits : Nat :=
  (Finset.univ.image (fun F : Fabric => ({F, fabricInv F} : Finset Fabric))).card

/-- **The inversion quotient of the hyperfabric is the supplied codec orbit
count.** -/
theorem fabricOrbits_eq : fabricOrbits = TriadicKernelAlgebra.orbitCount 15 :=
  pair_image_card_transport fabricKernelEquiv fabricInv (fun u => -u) fabricKernelEquiv_neg

/-- Its value: `(3 ^ 15 + 1) / 2 = 7174454`. -/
theorem fabricOrbits_value : fabricOrbits = 7174454 := by
  rw [fabricOrbits_eq, TriadicKernelAlgebra.orbitCount_formula]
  norm_num

end Synthesis.CodecBridge
