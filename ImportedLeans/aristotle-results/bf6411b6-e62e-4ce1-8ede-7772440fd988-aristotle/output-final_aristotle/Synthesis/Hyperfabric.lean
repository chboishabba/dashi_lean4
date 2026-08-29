import Synthesis.ToneCore
import Synthesis.DialecticTone
import Synthesis.MonsterFibre

/-!
# Synthesis layer 3: hyperfabric = ternary fibres over the Monster base

The three layers below supply, respectively, a ternary tone primitive
(`Synthesis.ToneCore`), dialectical carriers over it (`Synthesis.DialecticTone`)
and a 15-element Monster prime base carrying a mask fibre with a genuine
ultrametric (`Synthesis.MonsterFibre`).

This file performs the only composition the material actually supports: taking
*sections of the trit fibre over the Monster base*.  A `Fabric` is a section
`SSP → Trit`; a `HalfFabric` is a section of the finer half-trit fibre.

Proved here:

* the fabric is a commutative monoid under pointwise ternary XOR, and is
  isomorphic (as an additive group) to `SSP → ZMod 3` (`fabricZMod_add`);
  in particular it has `3 ^ 15` sections, and the half-trit fibre has `5 ^ 15`;
* the half-trit → trit collapse on sections is surjective and genuinely not
  injective, so the half-step refinement is not recoverable from a fabric;
* the sixfold dialectic acts on the fabric by tone rotation, and the action is
  equivariant for the dialectical successor (`fabricAct_next6`), with period 3
  in the tone and period 6 in the stage;
* the support map `Fabric → MaskSSP` lands in the mask fibre of layer 2, so the
  fabric inherits the supplied Monster geometry, and the constant Monster
  projection strictly contracts distances between fabrics of distinct support;
* an honest obstruction: the support map is *not* a homomorphism from ternary
  XOR to boolean OR (`support_not_hom`), so the ternary layer does not descend
  to the mask layer as an algebra map — only as a map of sets.

Boundary: "hyperfabric" here means exactly "sections of a finite fibre over a
finite base".  No continuum, no field theory, no dynamics beyond the finite
group actions proved below.
-/

namespace Synthesis.Hyperfabric

open AgdaMirror.Base369
open AgdaMirror.DASHIAlgebra (Trit Stage6 next6)
open AgdaMirror.TritBridge (toTriTruth fromTriTruth tritXor rotTrit)
open AgdaMirror.HalfTritMod (HalfTrit embedTrit invHalfTrit)
open AgdaMirror.MonsterOntos (SSP)
open Synthesis.ToneCore
open Synthesis.DialecticTone
open Synthesis.MonsterFibre

/-! ## Sections -/

/-- A hyperfabric: a section of the balanced-ternary fibre over the Monster
prime base. -/
abbrev Fabric := SSP → Trit

/-- A half-trit refined section. -/
abbrev HalfFabric := SSP → HalfTrit

/-- The forgetful collapse of a refined section. -/
def collapse (H : HalfFabric) : Fabric := fun p => embedTrit (H p)

/-- The tone of a section. -/
def fabricTone (F : Fabric) : SSP → TriTruth := fun p => toTriTruth (F p)

/-- Tone is a bijection of section spaces (it is pointwise the tone equivalence
of layer 0). -/
def fabricToneEquiv : Fabric ≃ (SSP → TriTruth) :=
  Equiv.arrowCongr (Equiv.refl SSP) tritToneEquiv

@[simp] theorem fabricToneEquiv_apply (F : Fabric) : fabricToneEquiv F = fabricTone F := rfl

/-! ## The ternary algebra of sections -/

/-- Pointwise ternary XOR of sections. -/
def fabricXor (x y : Fabric) : Fabric := fun p => tritXor (x p) (y p)

/-- The neutral section. -/
def fabricZero : Fabric := fun _ => .neg

theorem tritXor_comm (a b : Trit) : tritXor a b = tritXor b a := by
  cases a <;> cases b <;> rfl

theorem fabricXor_comm (x y : Fabric) : fabricXor x y = fabricXor y x := by
  funext p; exact tritXor_comm _ _

theorem fabricXor_assoc (x y z : Fabric) :
    fabricXor x (fabricXor y z) = fabricXor (fabricXor x y) z := by
  funext p; exact AgdaMirror.TritBridge.tritXor_assoc _ _ _

theorem fabricXor_zero_left (x : Fabric) : fabricXor fabricZero x = x := by
  funext p; exact AgdaMirror.TritBridge.tritXor_idL _

theorem fabricXor_zero_right (x : Fabric) : fabricXor x fabricZero = x := by
  rw [fabricXor_comm]; exact fabricXor_zero_left x

/-- Every section has order dividing 3. -/
theorem fabricXor_three (x : Fabric) : fabricXor x (fabricXor x x) = fabricZero := by
  funext p; revert p; intro p; cases h : x p <;> simp [fabricXor, fabricZero, tritXor, h] <;> rfl

/-- Sections as `ℤ/3`-valued functions. -/
def fabricZMod : Fabric ≃ (SSP → ZMod 3) :=
  Equiv.arrowCongr (Equiv.refl SSP) (tritToneEquiv.trans toneZMod)

/-- **The section algebra is `(ℤ/3)^15`.**  Pointwise ternary XOR is pointwise
addition in `ℤ/3`. -/
theorem fabricZMod_add (x y : Fabric) :
    fabricZMod (fabricXor x y) = fabricZMod x + fabricZMod y := by
  funext p
  have := toneZMod_xor (toTriTruth (x p)) (toTriTruth (y p))
  simpa [fabricZMod, fabricXor, Equiv.arrowCongr,
    AgdaMirror.TritBridge.triXor_equivariant] using this

theorem fabricZMod_zero : fabricZMod fabricZero = 0 := by
  funext p; rfl

/-! ## Counting -/

theorem card_fabric : Fintype.card Fabric = 3 ^ 15 := by
  rw [Fintype.card_fun]
  rfl

theorem card_halfFabric : Fintype.card HalfFabric = 5 ^ 15 := by
  rw [Fintype.card_fun]
  rfl

/-- The refinement is genuinely bigger than the collapse target. -/
theorem card_halfFabric_gt : Fintype.card Fabric < Fintype.card HalfFabric := by
  rw [card_fabric, card_halfFabric]
  norm_num

/-! ## The collapse of refined sections -/

theorem collapse_surjective : Function.Surjective collapse := by
  intro F
  refine ⟨fun p => (match F p with
    | .neg => HalfTrit.negOne
    | .zer => HalfTrit.zero
    | .pos => HalfTrit.posOne), ?_⟩
  funext p
  cases h : F p <;> simp [collapse, h, embedTrit]

/-- The collapse is not injective: the half-step refinement is genuinely lost,
already on a single fibre. -/
theorem collapse_not_injective : ¬ Function.Injective collapse := by
  intro h
  have hcol : collapse (fun _ => HalfTrit.negOne) = collapse (fun _ => HalfTrit.negHalf) := by
    funext p; rfl
  have := h hcol
  have : (HalfTrit.negOne) = HalfTrit.negHalf := congrFun this .p2
  exact absurd this (by decide)

/-- The sign flip on refined sections descends to the tone reflection. -/
theorem collapse_flip (H : HalfFabric) (p : SSP) :
    toTriTruth (collapse (fun q => invHalfTrit (H q)) p) =
      triReflect (toTriTruth (collapse H p)) := by
  simpa [collapse] using halfTone_inv (H p)

/-- The fibre of the digit-level forgetful embedding: two half-steps over each
signed digit, one over the zero digit. -/
theorem card_embedTrit_fibre (t : Trit) :
    Fintype.card {x : HalfTrit // embedTrit x = t} = if t = .zer then 1 else 2 := by
  cases t <;> simp [Fintype.card_subtype] <;> decide

/-- **Exact fibre count of the section collapse.**  The refinements of a given
ternary section are counted by its non-zero fibres: there are `2 ^ k` of them,
where `k` is the number of base points carrying a non-zero digit.  This is the
quantitative form of the loss recorded by `collapse_not_injective`. -/
theorem card_collapse_fibre (F : Fabric) :
    Fintype.card {H : HalfFabric // collapse H = F} =
      2 ^ (Finset.univ.filter (fun p : SSP => F p ≠ .zer)).card := by
  have e1 : {H : HalfFabric // collapse H = F} ≃
      {H : HalfFabric // ∀ p, embedTrit (H p) = F p} :=
    Equiv.subtypeEquivRight (fun _ => funext_iff)
  have e2 : {H : HalfFabric // ∀ p, embedTrit (H p) = F p} ≃
      ((p : SSP) → {x : HalfTrit // embedTrit x = F p}) :=
    Equiv.subtypePiEquivPi (β := fun _ => HalfTrit) (p := fun p x => embedTrit x = F p)
  rw [Fintype.card_congr (e1.trans e2), Fintype.card_pi]
  simp only [card_embedTrit_fibre]
  rw [Finset.prod_ite]
  simp [Finset.prod_const]

/-- The collapse is injective exactly over the zero section, where the fibre is a
singleton, and maximally lossy over the nowhere-zero sections, where it has
`2 ^ 15` elements. -/
theorem card_collapse_fibre_extremes :
    Fintype.card {H : HalfFabric // collapse H = fun _ => Trit.zer} = 1 ∧
      Fintype.card {H : HalfFabric // collapse H = fun _ => Trit.pos} = 2 ^ 15 := by
  constructor
  · rw [card_collapse_fibre]; simp
  · rw [card_collapse_fibre]
    simp [Finset.filter_true_of_mem, card_ssp]

/-- **The dialectic cannot act on the base itself.**  Any action of the sixfold
dialectical cycle on the Monster prime base by reindexing that respects the mask
geometry is trivial at every stage.  So the only genuine link between the
dialectical carriers and the base is the one this spine uses: an action on the
*sections*, fibrewise through the tone — never a motion of the base. -/
theorem no_nontrivial_geometric_base_action (act : Stage6 → SSP ≃ SSP)
    (hiso : ∀ (s : Stage6) (x y : MaskSSP),
      dSSP (fun p => x (act s p)) (fun p => y (act s p)) = dSSP x y) :
    ∀ s, act s = Equiv.refl SSP :=
  fun s => isometric_reindex_eq_refl (act s) (hiso s)

/-! ## The sixfold dialectic acts on the fabric -/

/-- Rotate a digit `n` times. -/
def rotIter : Nat → Trit → Trit
  | 0, t => t
  | n + 1, t => rotTrit (rotIter n t)

theorem rotIter_three (t : Trit) : rotIter 3 t = t := by cases t <;> rfl

/-- The tone index of a sixfold dialectic stage. -/
def stageIndex (s : Stage6) : Nat := triIndex (stage6Tone s)

/-- The action of a dialectical stage on a fabric: rotate every fibre by the
stage's tone index. -/
def fabricAct (s : Stage6) (F : Fabric) : Fabric := fun p => rotIter (stageIndex s) (F p)

/-- Pointwise rotation of a fabric. -/
def fabricRot (F : Fabric) : Fabric := fun p => rotTrit (F p)

/-- Key digit-level step: advancing the tone index rotates once more. -/
theorem rotIter_index_rot (t u : Trit) :
    rotIter (triIndex (rotateTri (toTriTruth t))) u = rotTrit (rotIter (triIndex (toTriTruth t)) u) := by
  cases t <;> cases u <;> rfl

/-- **Dialectic ⇒ fabric equivariance.**  One dialectical successor step acts as
exactly one tone rotation of every fibre. -/
theorem fabricAct_next6 (s : Stage6) (F : Fabric) :
    fabricAct (next6 s) F = fabricRot (fabricAct s F) := by
  funext p
  have hs : stage6Tone (next6 s) = rotateTri (stage6Tone s) := stage6Tone_next s
  cases s <;> cases h : F p <;>
    simp [fabricAct, fabricRot, stageIndex, hs, h] <;> rfl

/-- The action has period 3 (not 6): the dialectic drives the fabric through the
ternary rotation, and the sixfold cycle covers it twice. -/
theorem fabricAct_period_three (s : Stage6) (F : Fabric) :
    fabricAct (next6 (next6 (next6 s))) F = fabricAct s F := by
  funext p; cases s <;> cases h : F p <;> simp [fabricAct, stageIndex, h] <;> rfl

/-- The dialectical rotation acts on the section algebra as a *translation*, not
as an automorphism: rotating a XOR of sections is the XOR with one rotated
argument. -/
theorem fabricRot_xor (x y : Fabric) :
    fabricRot (fabricXor x y) = fabricXor (fabricRot x) y := by
  funext p
  cases h : x p <;> cases h' : y p <;> simp [fabricRot, fabricXor, h, h'] <;> rfl

/-- ... and it is genuinely not additive. -/
theorem fabricRot_not_additive :
    ¬ ∀ x y : Fabric, fabricRot (fabricXor x y) = fabricXor (fabricRot x) (fabricRot y) := by
  intro h
  have := congrFun (h fabricZero fabricZero) SSP.p2
  exact absurd this (by decide)

/-! ## The fabric over the Monster geometry -/

/-- Support of a digit: `true` away from the XOR-neutral position. -/
def support (t : Trit) : Bool := decide (t ≠ Trit.neg)

/-- The support mask of a fabric: an element of the layer-2 mask fibre. -/
def supportMask (F : Fabric) : MaskSSP := fun p => support (F p)

/-- **Honest obstruction.**  Support is not a homomorphism from ternary XOR to
boolean OR, so the ternary section algebra does not descend to the mask
semilattice as an algebra map. -/
theorem support_not_hom :
    ¬ ∀ a b : Trit, support (tritXor a b) = (support a || support b) := by
  intro h
  exact absurd (h .zer .pos) (by decide)

/-- **Fabric geometry.**  The constant Monster projection strictly contracts the
supplied ultrametric distance between the support masks of two fabrics with
distinct supports. -/
theorem fabric_projection_contractive (target : MaskSSP) {x y : Fabric}
    (hxy : supportMask x ≠ supportMask y) :
    dSSP (projectSSP target (supportMask x)) (projectSSP target (supportMask y)) <
      dSSP (supportMask x) (supportMask y) :=
  projectSSP_contractive target hxy

/-- The support mask does not see the half-step refinement: two refined sections
with the same collapse have the same mask, and distinct refined sections can
share a mask. -/
theorem supportMask_blind_to_refinement :
    (∀ H H' : HalfFabric, collapse H = collapse H' →
        supportMask (collapse H) = supportMask (collapse H')) ∧
      ∃ H H' : HalfFabric, H ≠ H' ∧ supportMask (collapse H) = supportMask (collapse H') := by
  refine ⟨fun H H' h => by rw [h], ?_⟩
  refine ⟨fun _ => HalfTrit.negOne, fun _ => HalfTrit.negHalf, ?_, rfl⟩
  intro h
  exact absurd (congrFun h SSP.p2) (by decide)

end Synthesis.Hyperfabric
