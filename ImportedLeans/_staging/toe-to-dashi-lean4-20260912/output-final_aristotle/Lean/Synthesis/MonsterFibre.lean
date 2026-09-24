import Mathlib
import AgdaMirror.MonsterOntos
import AgdaMirror.DASHIAlgebra
import AgdaMirror.MonsterProjection15
import AgdaMirror.Ultrametric

/-!
# Synthesis layer 2: the Monster prime base and its mask fibre

The repository supplies three *different* length-15 mask carriers, one in each
of three modules, with no stated relation between them:

* `AgdaMirror.MonsterOntos.SSP` — the 15 supersingular primes dividing `|M|`,
  with the injective embedding `toNat`;
* `AgdaMirror.DASHIAlgebra.Mask15 = Fin 15 → Bool` — the mask *algebra* carrier
  (pointwise AND, identity `fullMask`, supplied semilattice laws);
* `AgdaMirror.MonsterProjection15.Mask15 = {m : List Bool // m.length = 15}` —
  the mask *geometry* carrier, which carries the supplied genuine ultrametric
  `UMask15` and the supplied contractivity theorem `proj_contractive`.

This file proves that these are one and the same object, indexed by the Monster
prime base, and transports the geometry onto the base-indexed carrier:

* `sspEquivFin15 : SSP ≃ Fin 15` (built from the supplied injectivity of `toNat`
  in spirit; here from an explicit numbering) and `toNat_prime`;
* `maskFibreEquiv : (SSP → Bool) ≃ MonsterProjection15.Mask15`, factoring
  through the algebra carrier `Fin 15 → Bool`;
* `Ultrametric.comap`, a general transport of a discrete ultrametric along a map,
  and the resulting `USSP : Ultrametric (SSP → Bool)`;
* `dSSP_eq_zero_iff` (the transported identity of indiscernibles — genuinely a
  biconditional, because the transport map is injective);
* `projectSSP_contractive`, the supplied contractivity theorem transported to
  the base-indexed carrier;
* the mask semilattice on the base-indexed carrier, with the reindexing
  equivalence proved to be a homomorphism onto the supplied `maskAnd` algebra.

Boundary: "Monster" here names the supplied 15-element index set of
supersingular primes and the mask carriers built on it.  Nothing about the
Monster *group*, its representations, or moonshine is claimed or used.
-/

namespace Synthesis.MonsterFibre

open AgdaMirror (Ultrametric)
open AgdaMirror.MonsterOntos (SSP)
open AgdaMirror.MonsterProjection15 (d15 dMask lcpLen eq_of_dMask_zero dMask_id_zero)

/-! ## The Monster prime base -/

instance : Fintype SSP :=
  ⟨{.p2, .p3, .p5, .p7, .p11, .p13, .p17, .p19, .p23, .p29, .p31, .p41, .p47, .p59, .p71},
    fun x => by cases x <;> decide⟩

/-- Numbering of the supersingular primes. -/
def sspToFin : SSP → Fin 15
  | .p2 => 0 | .p3 => 1 | .p5 => 2 | .p7 => 3 | .p11 => 4
  | .p13 => 5 | .p17 => 6 | .p19 => 7 | .p23 => 8 | .p29 => 9
  | .p31 => 10 | .p41 => 11 | .p47 => 12 | .p59 => 13 | .p71 => 14

/-- Inverse numbering. -/
def finToSsp : Fin 15 → SSP
  | 0 => .p2 | 1 => .p3 | 2 => .p5 | 3 => .p7 | 4 => .p11
  | 5 => .p13 | 6 => .p17 | 7 => .p19 | 8 => .p23 | 9 => .p29
  | 10 => .p31 | 11 => .p41 | 12 => .p47 | 13 => .p59 | 14 => .p71

/-- **The Monster prime base is a 15-element index.** -/
def sspEquivFin15 : SSP ≃ Fin 15 where
  toFun := sspToFin
  invFun := finToSsp
  left_inv := by decide
  right_inv := by decide

@[simp] theorem card_ssp : Fintype.card SSP = 15 := rfl

/-- Every element of the base is a prime. -/
theorem toNat_prime (p : SSP) : Nat.Prime (AgdaMirror.MonsterOntos.toNat p) := by
  cases p <;> norm_num [AgdaMirror.MonsterOntos.toNat]

/-- The base enumerates exactly the fifteen supersingular primes. -/
theorem toNat_image :
    (Finset.univ.image AgdaMirror.MonsterOntos.toNat) =
      ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71} : Finset Nat) := by decide

/-! ## The mask fibre over the base -/

/-- A Monster mask: a boolean fibre over the prime base. -/
abbrev MaskSSP := SSP → Bool

/-- Reindexing the fibre along the numbering gives the supplied mask *algebra*
carrier. -/
def maskReindex : MaskSSP ≃ (Fin 15 → Bool) :=
  Equiv.arrowCongr sspEquivFin15 (Equiv.refl Bool)

/-- The supplied mask *geometry* carrier is the same as the algebra carrier. -/
def maskListEquiv : (Fin 15 → Bool) ≃ AgdaMirror.MonsterProjection15.Mask15 where
  toFun f := ⟨List.ofFn f, by simp⟩
  invFun l := fun i => l.val[(i : Nat)]'(by rw [l.property]; exact i.isLt)
  left_inv := by
    intro f; funext i
    simp only [List.getElem_ofFn, Fin.eta]
  right_inv := by
    intro l
    apply Subtype.ext
    apply List.ext_getElem (by simp [l.property])
    intro n h1 h2
    simp only [List.getElem_ofFn]

/-- **Mask carriers agree.**  The boolean fibre over the Monster prime base, the
supplied mask algebra carrier, and the supplied mask geometry carrier are all
the same object. -/
def maskFibreEquiv : MaskSSP ≃ AgdaMirror.MonsterProjection15.Mask15 :=
  maskReindex.trans maskListEquiv

/-! ## Transport of the supplied ultrametric geometry -/

/-- Transport of a discrete ultrametric along an arbitrary map. -/
def Ultrametric.comap {A B : Type} (f : A → B) (U : Ultrametric B) : Ultrametric A where
  d x y := U.d (f x) (f y)
  id_zero x := U.id_zero (f x)
  symmetric x y := U.symmetric (f x) (f y)
  ultratriangle x y z := U.ultratriangle (f x) (f y) (f z)

/-- The mask distance on the base-indexed fibre. -/
def dSSP (x y : MaskSSP) : Nat := d15 (maskFibreEquiv x) (maskFibreEquiv y)

/-- **The Monster mask fibre carries the supplied genuine ultrametric.** -/
def USSP : Ultrametric MaskSSP :=
  Ultrametric.comap maskFibreEquiv AgdaMirror.MonsterProjection15.UMask15

@[simp] theorem USSP_d (x y : MaskSSP) : USSP.d x y = dSSP x y := rfl

/-- Identity of indiscernibles, now as a biconditional: the transport is
injective, so vanishing distance really means equality of fibres. -/
theorem dSSP_eq_zero_iff (x y : MaskSSP) : dSSP x y = 0 ↔ x = y := by
  constructor
  · intro h
    have hlen : (maskFibreEquiv x).val.length = (maskFibreEquiv y).val.length :=
      (maskFibreEquiv x).property.trans (maskFibreEquiv y).property.symm
    have : (maskFibreEquiv x : AgdaMirror.MonsterProjection15.Mask15) = maskFibreEquiv y :=
      Subtype.ext (eq_of_dMask_zero hlen h)
    exact maskFibreEquiv.injective this
  · rintro rfl
    exact dMask_id_zero _

/-! ## The supplied contractive projection, transported -/

/-- Constant projection of the mask fibre onto a target fibre. -/
def projectSSP (target : MaskSSP) : MaskSSP → MaskSSP := fun _ => target

/-- **Transported contractivity.**  On the base-indexed mask fibre, the constant
projection strictly decreases the ultrametric distance between distinct fibres.
This is the supplied `proj_contractive` moved onto the shared carrier. -/
theorem projectSSP_contractive (target : MaskSSP) {x y : MaskSSP} (hxy : x ≠ y) :
    dSSP (projectSSP target x) (projectSSP target y) < dSSP x y := by
  have h0 : dSSP (projectSSP target x) (projectSSP target y) = 0 := by
    simp [dSSP, projectSSP, d15, dMask_id_zero]
  rw [h0]
  rcases Nat.eq_zero_or_pos (dSSP x y) with h | h
  · exact absurd ((dSSP_eq_zero_iff x y).mp h) hxy
  · exact h

/-- The projection has a unique fixed point, namely its target. -/
theorem projectSSP_unique_fixed (target x : MaskSSP) (hx : projectSSP target x = x) :
    x = target := hx.symm

/-! ## The mask algebra on the base-indexed fibre -/

/-- Pointwise AND of Monster masks. -/
def maskAndSSP (x y : MaskSSP) : MaskSSP := fun p => x p && y p

/-- The all-primes-kept mask. -/
def fullMaskSSP : MaskSSP := fun _ => true

theorem maskAndSSP_comm (x y : MaskSSP) : maskAndSSP x y = maskAndSSP y x := by
  funext p; simp [maskAndSSP, Bool.and_comm]

theorem maskAndSSP_assoc (x y z : MaskSSP) :
    maskAndSSP (maskAndSSP x y) z = maskAndSSP x (maskAndSSP y z) := by
  funext p; simp [maskAndSSP, Bool.and_assoc]

theorem maskAndSSP_idem (x : MaskSSP) : maskAndSSP x x = x := by
  funext p; simp [maskAndSSP]

theorem maskAndSSP_full (x : MaskSSP) : maskAndSSP x fullMaskSSP = x := by
  funext p; simp [maskAndSSP, fullMaskSSP]

/-- **The reindexing is an algebra homomorphism** onto the supplied mask
algebra: the base-indexed mask semilattice *is* `AgdaMirror.DASHIAlgebra`'s. -/
theorem maskReindex_hom (x y : MaskSSP) :
    maskReindex (maskAndSSP x y) =
      AgdaMirror.DASHIAlgebra.maskAnd (maskReindex x) (maskReindex y) := by
  funext i
  simp [maskReindex, maskAndSSP, AgdaMirror.DASHIAlgebra.maskAnd,
    AgdaMirror.DASHIAlgebra.boolAnd, Equiv.arrowCongr]

theorem maskReindex_full :
    maskReindex fullMaskSSP = AgdaMirror.DASHIAlgebra.fullMask := by
  funext i; rfl

/-- The mask fibre has exactly `2^15` elements. -/
theorem card_maskSSP : Fintype.card MaskSSP = 2 ^ 15 := by
  simp [MaskSSP]

/-! ## Distance to the collapse mask -/

/-- The collapse mask: every factor removed. -/
def emptyMaskSSP : MaskSSP := fun _ => false

/-- Monotonicity of the common prefix against the all-zero word: adding `true`s
only shortens the leading run of zeros. -/
theorem lcpLen_zeros_mono : ∀ (n : Nat) (f g : Fin n → Bool), (∀ i, f i = true → g i = true) →
    AgdaMirror.MonsterProjection15.lcpLen (List.ofFn g) (List.replicate n false) ≤
      AgdaMirror.MonsterProjection15.lcpLen (List.ofFn f) (List.replicate n false) := by
  intro n
  induction n with
  | zero => intro f g _; simp
  | succ n ih =>
    intro f g h
    rw [List.ofFn_succ, List.ofFn_succ, List.replicate_succ]
    cases hg : g 0 with
    | true => simp [AgdaMirror.MonsterProjection15.lcpLen]
    | false =>
      have hf : f 0 = false := by
        by_contra hc
        simp only [Bool.not_eq_false] at hc
        rw [h 0 hc] at hg; exact Bool.noConfusion hg
      simp only [hf, AgdaMirror.MonsterProjection15.lcpLen]
      exact Nat.succ_le_succ (ih (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ))

/-- The distance to the collapse mask is `15` minus the leading run of removed
factors. -/
theorem dSSP_empty (x : MaskSSP) :
    dSSP x emptyMaskSSP =
      15 - AgdaMirror.MonsterProjection15.lcpLen
        (List.ofFn (fun i => x (finToSsp i))) (List.replicate 15 false) := by
  have h1 : (maskFibreEquiv emptyMaskSSP).val = List.replicate 15 false := by
    show List.ofFn (fun _ : Fin 15 => false) = List.replicate 15 false
    simp
  have h2 : (maskFibreEquiv x).val = List.ofFn (fun i => x (finToSsp i)) := rfl
  simp only [dSSP, d15, dMask, h1, h2, List.length_ofFn]

/-- **Submasks are no further from the collapse mask.**  Removing factors never
increases the distance to the empty mask. -/
theorem dSSP_empty_mono {x y : MaskSSP} (h : ∀ p, x p = true → y p = true) :
    dSSP x emptyMaskSSP ≤ dSSP y emptyMaskSSP := by
  rw [dSSP_empty, dSSP_empty]
  have := lcpLen_zeros_mono 15 (fun i => x (finToSsp i)) (fun i => y (finToSsp i))
    (fun i => h (finToSsp i))
  omega

/-! ## Rigidity of the mask geometry under reindexing of the base -/

/-- The mask supported at a single base point. -/
def indMask (j : SSP) : MaskSSP := fun p => decide (p = j)

/-- The distance from the empty mask to a point mask reads off the position of
that point in the base ordering. -/
theorem dSSP_const_ind (j : SSP) :
    dSSP (fun _ => false) (indMask j) = 15 - (sspToFin j : Nat) := by
  revert j; decide

/-- Reindexing a point mask moves its point by the inverse permutation. -/
theorem indMask_comp (σ : SSP ≃ SSP) (j : SSP) :
    (fun p => indMask j (σ p)) = indMask (σ.symm j) := by
  funext p
  simp only [indMask, decide_eq_decide]
  constructor
  · intro h; rw [← h, σ.symm_apply_apply]
  · intro h; rw [h, σ.apply_symm_apply]

/-- **Rigidity.**  The mask geometry is a first-difference geometry, hence it
remembers the ordering of the base: the only permutation of the base whose
reindexing preserves `dSSP` is the identity.  (The empty mask and the point
masks already separate the positions.) -/
theorem isometric_reindex_eq_refl (σ : SSP ≃ SSP)
    (h : ∀ x y : MaskSSP, dSSP (fun p => x (σ p)) (fun p => y (σ p)) = dSSP x y) :
    σ = Equiv.refl SSP := by
  have key : ∀ j : SSP, σ.symm j = j := by
    intro j
    have h1 := h (fun _ => false) (indMask j)
    rw [indMask_comp σ j] at h1
    rw [dSSP_const_ind, dSSP_const_ind] at h1
    have hj : (sspToFin j : Nat) < 15 := (sspToFin j).isLt
    have hs : (sspToFin (σ.symm j) : Nat) < 15 := (sspToFin (σ.symm j)).isLt
    have : sspToFin (σ.symm j) = sspToFin j := Fin.ext (by omega)
    exact sspEquivFin15.injective this
  apply Equiv.ext
  intro p
  simpa using (congrArg σ (key (σ p))).symm

end Synthesis.MonsterFibre
