import Cuisine.UmamiTransport
import Synthesis.CodecBridge

/-!
# Cuisine ⟶ codec: the umami monoid in balanced-ternary kernel coordinates

`Synthesis.CodecBridge` identifies the Monster hyperfabric with the depth-15
triadic codec kernel `K₁₅ = Fin 15 → ZMod 3` of `TriadicKernelAlgebra`, in the
*balanced* reading of a digit, and records the honest mismatch that the
repository's ternary XOR is not balanced addition but the affine operation
`u + v + 1`.

`Cuisine.UmamiTransport` maps cuisine umami intensities onto the hyperfabric.
This file composes the two, and asks what the codec's own structure — its
inversion action and its orbit count — becomes on the cuisine side.

Proved here (all sorry-free):

* `umamiCodec` — the composite `ℕ → K₁₅`, and `umamiCodec_surjective`: every
  codec word of depth fifteen is the coordinate vector of a cuisine blend;
* `umamiCodec_compose` — combining blends is the *affine* codec operation
  `x + y + 1`, exactly the mismatch recorded in `Synthesis.CodecBridge`.  This
  is the precise sense in which the cuisine monoid is the codec kernel: an
  isomorphism onto the affine, not the linear, structure;
* `umamiCodec_selfBlend` — **seasoning a blend with itself is the codec
  inversion action, translated**: `x ↦ -x + 1`;
* `fabricXor_self_ne_fabricInv` — the honest negative: it is *never* literally
  the codec inversion `x ↦ -x`; the two involutions differ at every point;
* `blendDoubleOrbits_eq` / `blendDoubleOrbits_value` — nevertheless the
  quotient count agrees: hyperfabric shadows of cuisine blends up to
  self-seasoning number `TriadicKernelAlgebra.orbitCount 15 = 7174454`, the
  supplied codec inversion-orbit count;
* `selfBlend_involutive_on_shadows` — self-seasoning is an involution on
  shadows, so the orbit count above counts what it appears to count;
* `fabricShift_conjugates`, `blendDoubleOrbits_eq_fabricOrbits` — *why* the two
  counts agree: the two involutions are conjugate by translation of codec
  coordinates, so the coincidence is structural and not arithmetic.

Boundary.  `TriadicKernelAlgebra` is a finite balanced-ternary algebra; nothing
here concerns perception, form constants, or any physical codec.  The cuisine
side is the arithmetic law `1 + (a ⊕ b) = (1+a)(1+b)`, nothing else.
-/

namespace Cuisine.CodecTransport

open AgdaMirror.DASHIAlgebra (Trit)
open AgdaMirror.MonsterOntos (SSP)
open Synthesis.MonsterFibre
open Synthesis.Hyperfabric
open Synthesis.CodecBridge
open Cuisine.UmamiTransport

/-- The codec coordinates of a cuisine intensity: the balanced-ternary word of
its hyperfabric shadow. -/
noncomputable def umamiCodec (u : ℕ) : Fin 15 → ZMod 3 :=
  fabricKernelEquiv (umamiFabric u)

/-- Every depth-15 codec word is the coordinate vector of a cuisine blend. -/
theorem umamiCodec_surjective : Function.Surjective umamiCodec := by
  intro w
  obtain ⟨u, hu⟩ := umamiFabric_surjective (fabricKernelEquiv.symm w)
  exact ⟨u, by rw [umamiCodec, hu, Equiv.apply_symm_apply]⟩

/-- **Combining blends is the affine codec operation.**  The translation by one
is the mismatch of `Synthesis.CodecBridge.fabricKernelEquiv_xor_affine`: the
repository's ternary XOR has neutral digit `-1`, not `0`. -/
theorem umamiCodec_compose (a b : ℕ) :
    umamiCodec (umamiCompose a b) = umamiCodec a + umamiCodec b + 1 := by
  rw [umamiCodec, umamiFabric_compose, fabricKernelEquiv_xor_affine]
  rfl

/-- Seasoning a blend with itself: `1 + (u ⊕ u) = (1+u)²`. -/
def selfBlend (u : ℕ) : ℕ := umamiCompose u u

theorem selfBlend_succ (u : ℕ) : selfBlend u + 1 = (u + 1) ^ 2 := by
  simp only [selfBlend, umamiCompose]; ring

/-- **Self-seasoning is the codec inversion action, translated by one.** -/
theorem umamiCodec_selfBlend (u : ℕ) :
    umamiCodec (selfBlend u) = - umamiCodec u + 1 := by
  rw [selfBlend, umamiCodec_compose]
  funext i
  have : (umamiCodec u i) + (umamiCodec u i) = - umamiCodec u i := by
    have h3 : (3 : ZMod 3) = 0 := by decide
    have : (umamiCodec u i) + (umamiCodec u i) + (umamiCodec u i) = 0 := by
      have : (3 : ZMod 3) * umamiCodec u i = 0 := by rw [h3]; ring
      linear_combination this
    linear_combination this
  simp only [Pi.add_apply, Pi.one_apply, Pi.neg_apply]
  rw [this]

/-! ## The two involutions, and their common orbit count -/

/-- Self-seasoning, on shadows: `F ↦ F ⊕ F`. -/
def fabricDouble (F : Fabric) : Fabric := fabricXor F F

/-- Self-seasoning of a blend is self-seasoning of its shadow. -/
theorem umamiFabric_selfBlend (u : ℕ) :
    umamiFabric (selfBlend u) = fabricDouble (umamiFabric u) := by
  rw [selfBlend, umamiFabric_compose, fabricDouble]

/-- In codec coordinates, self-seasoning is the translated inversion. -/
theorem fabricKernelEquiv_fabricDouble (F : Fabric) :
    fabricKernelEquiv (fabricDouble F) = - fabricKernelEquiv F + 1 := by
  funext i
  rw [fabricDouble, fabricKernelEquiv_xor_affine]
  have h : (fabricKernelEquiv F i) + (fabricKernelEquiv F i) + (fabricKernelEquiv F i) = 0 := by
    have h3 : (3 : ZMod 3) * fabricKernelEquiv F i = 0 := by
      have : (3 : ZMod 3) = 0 := by decide
      rw [this]; ring
    linear_combination h3
  simp only [Pi.add_apply, Pi.one_apply, Pi.neg_apply]
  linear_combination h

/-- **Honest negative.**  Self-seasoning is *never* the codec inversion
`Synthesis.CodecBridge.fabricInv`: the two involutions differ at every
hyperfabric section, because the XOR-neutral digit is `-1`. -/
theorem fabricXor_self_ne_fabricInv (F : Fabric) : fabricDouble F ≠ fabricInv F := by
  intro h
  have := congrArg fabricKernelEquiv h
  rw [fabricKernelEquiv_fabricDouble, fabricKernelEquiv_neg] at this
  have h0 := congrFun this ⟨0, by norm_num⟩
  simp only [Pi.add_apply, Pi.one_apply, Pi.neg_apply] at h0
  have : (1 : ZMod 3) = 0 := by linear_combination h0
  exact absurd this (by decide)

/-- Self-seasoning is an involution on shadows. -/
theorem fabricDouble_involutive (F : Fabric) : fabricDouble (fabricDouble F) = F := by
  apply fabricKernelEquiv.injective
  rw [fabricKernelEquiv_fabricDouble, fabricKernelEquiv_fabricDouble]
  funext i
  have h : ∀ x : ZMod 3, -(-x + 1) + 1 = x := by decide
  simpa only [Pi.add_apply, Pi.one_apply, Pi.neg_apply] using h (fabricKernelEquiv F i)

/-- The corresponding statement one level down: self-seasoning a blend twice
returns its shadow. -/
theorem selfBlend_involutive_on_shadows (u : ℕ) :
    umamiFabric (selfBlend (selfBlend u)) = umamiFabric u := by
  rw [umamiFabric_selfBlend, umamiFabric_selfBlend, fabricDouble_involutive]

/-- The equivalence intertwining self-seasoning with the codec inversion: the
codec coordinates translated by one. -/
noncomputable def shiftedKernelEquiv : Fabric ≃ (Fin 15 → ZMod 3) :=
  fabricKernelEquiv.trans (Equiv.addRight (1 : Fin 15 → ZMod 3))

theorem shiftedKernelEquiv_double (F : Fabric) :
    shiftedKernelEquiv (fabricDouble F) = - shiftedKernelEquiv F := by
  simp only [shiftedKernelEquiv, Equiv.trans_apply, Equiv.coe_addRight,
    fabricKernelEquiv_fabricDouble]
  funext i
  have h : ∀ x : ZMod 3, -x + 1 + 1 = -(x + 1) := by decide
  simpa only [Pi.add_apply, Pi.one_apply, Pi.neg_apply] using h (fabricKernelEquiv F i)

/-- Shadows of cuisine blends up to self-seasoning, in the supplied
unordered-pair form. -/
noncomputable def blendDoubleOrbits : ℕ := by
  classical
  exact (Finset.univ.image (fun F : Fabric => ({F, fabricDouble F} : Finset Fabric))).card

/-- **The self-seasoning quotient of the hyperfabric is the supplied codec
orbit count** — even though self-seasoning is not the codec inversion. -/
theorem blendDoubleOrbits_eq : blendDoubleOrbits = TriadicKernelAlgebra.orbitCount 15 := by
  classical
  exact pair_image_card_transport shiftedKernelEquiv fabricDouble (fun u => -u)
    shiftedKernelEquiv_double

/-- Its value: `(3 ^ 15 + 1) / 2 = 7174454`. -/
theorem blendDoubleOrbits_value : blendDoubleOrbits = 7174454 := by
  rw [blendDoubleOrbits_eq, TriadicKernelAlgebra.orbitCount_formula]
  norm_num

/-! ## Why the two orbit counts agree -/

/-- The translation of codec coordinates by the neutral digit, as a self-map of
the hyperfabric. -/
noncomputable def fabricShift : Fabric ≃ Fabric :=
  fabricKernelEquiv.trans ((Equiv.addRight (1 : Fin 15 → ZMod 3)).trans fabricKernelEquiv.symm)

/-- **The explanation of the coincidence.**  Self-seasoning and the codec
inversion are not equal, but they are *conjugate*: translating codec coordinates
by the neutral digit carries one to the other.  Equal orbit counts follow. -/
theorem fabricShift_conjugates (F : Fabric) :
    fabricShift (fabricDouble F) = fabricInv (fabricShift F) := by
  apply fabricKernelEquiv.injective
  rw [fabricKernelEquiv_neg]
  simp only [fabricShift, Equiv.trans_apply, Equiv.coe_addRight, Equiv.apply_symm_apply]
  rw [fabricKernelEquiv_fabricDouble]
  funext i
  have h : ∀ x : ZMod 3, -x + 1 + 1 = -(x + 1) := by decide
  simpa only [Pi.add_apply, Pi.one_apply, Pi.neg_apply] using h (fabricKernelEquiv F i)

/-- Consequently the self-seasoning quotient and the codec inversion quotient of
the hyperfabric have the same size, for a structural reason. -/
theorem blendDoubleOrbits_eq_fabricOrbits : blendDoubleOrbits = fabricOrbits := by
  classical
  exact pair_image_card_transport fabricShift fabricDouble fabricInv fabricShift_conjugates

/-- Non-vacuity: every hyperfabric section, hence every orbit counted above, is
the shadow of an actual cuisine intensity. -/
theorem exists_blend_shadow (F : Fabric) :
    ∃ u : ℕ, umamiFabric u = F ∧ umamiFabric (selfBlend u) = fabricDouble F := by
  obtain ⟨u, hu⟩ := umamiFabric_surjective F
  exact ⟨u, hu, by rw [umamiFabric_selfBlend, hu]⟩

end Cuisine.CodecTransport
