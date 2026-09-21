import Synthesis.MillenniumBSDActualE2GaloisFixed
import Synthesis.MillenniumBSDCMTwoTorsionGaloisModule
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Actual algebraic-closure E[2] is additively (Z/2)^2

The two basis labels map to the literal points `(0,0)` and `(1,0)`.
Their sum is forced to be the remaining nonzero two-torsion point `(-1,0)`
by the already-proved four-point classification; no new elliptic addition
formula is needed.
-/

namespace Synthesis.Millennium.BSD

def actualZeroTorsionSubgroupPoint : cmAlgClosureTwoTorsionSubgroup :=
  ⟨.affine 0 0 (by norm_num),
    (cmAlgClosure_twoTorsion_classification _).2 (Or.inr (Or.inl rfl))⟩

def actualOneTorsionSubgroupPoint : cmAlgClosureTwoTorsionSubgroup :=
  ⟨.affine 1 0 (by norm_num),
    (cmAlgClosure_twoTorsion_classification _).2
      (Or.inr (Or.inr (Or.inl rfl)))⟩

def actualMinusOneTorsionSubgroupPoint : cmAlgClosureTwoTorsionSubgroup :=
  ⟨.affine (-1) 0 (by norm_num),
    (cmAlgClosure_twoTorsion_classification _).2
      (Or.inr (Or.inr (Or.inr rfl)))⟩

@[simp] theorem actualZeroTorsion_ne_zero :
    actualZeroTorsionSubgroupPoint ≠ 0 := by
  intro h
  have hv := congrArg Subtype.val h
  rw [cmAlgClosure_zero_eq_infinity] at hv
  cases hv

@[simp] theorem actualOneTorsion_ne_zero :
    actualOneTorsionSubgroupPoint ≠ 0 := by
  intro h
  have hv := congrArg Subtype.val h
  rw [cmAlgClosure_zero_eq_infinity] at hv
  cases hv

theorem actualZeroTorsion_ne_actualOne :
    actualZeroTorsionSubgroupPoint ≠ actualOneTorsionSubgroupPoint := by
  intro h
  have hv := congrArg Subtype.val h
  injection hv with hx _
  norm_num at hx

theorem actualZeroTorsion_add_actualOne :
    actualZeroTorsionSubgroupPoint + actualOneTorsionSubgroupPoint =
      actualMinusOneTorsionSubgroupPoint := by
  let S := actualZeroTorsionSubgroupPoint + actualOneTorsionSubgroupPoint
  have hclass := (cmAlgClosure_twoTorsion_classification S.1).1 S.2
  rcases hclass with hzero | hz | ho | hm
  · have hs0 : S = 0 := Subtype.ext hzero
    have hneg : actualZeroTorsionSubgroupPoint = -actualOneTorsionSubgroupPoint := by
      exact add_eq_zero_iff_eq_neg.mp hs0
    have honeSelfNeg : -actualOneTorsionSubgroupPoint = actualOneTorsionSubgroupPoint := by
      apply neg_eq_iff_add_eq_zero.mpr
      change actualOneTorsionSubgroupPoint + actualOneTorsionSubgroupPoint = 0
      simpa [two_nsmul] using actualOneTorsionSubgroupPoint.2
    exact (actualZeroTorsion_ne_actualOne (hneg.trans honeSelfNeg))
  · have hs : S = actualZeroTorsionSubgroupPoint := Subtype.ext hz
    have : actualOneTorsionSubgroupPoint = 0 := by
      exact add_left_cancel (by simpa [S] using hs)
    exact actualOneTorsion_ne_zero this
  · have hs : S = actualOneTorsionSubgroupPoint := Subtype.ext ho
    have : actualZeroTorsionSubgroupPoint = 0 := by
      exact add_right_cancel (by simpa [S] using hs)
    exact actualZeroTorsion_ne_zero this
  · exact Subtype.ext hm

noncomputable def zmodTwoToActualZeroTorsion :
    ZMod 2 →+ cmAlgClosureTwoTorsionSubgroup :=
  ZMod.lift 2
    ⟨zmultiplesHom cmAlgClosureTwoTorsionSubgroup actualZeroTorsionSubgroupPoint, by
      change (2 : ℤ) • actualZeroTorsionSubgroupPoint = 0
      ext
      simpa using actualZeroTorsionSubgroupPoint.2⟩

noncomputable def zmodTwoToActualOneTorsion :
    ZMod 2 →+ cmAlgClosureTwoTorsionSubgroup :=
  ZMod.lift 2
    ⟨zmultiplesHom cmAlgClosureTwoTorsionSubgroup actualOneTorsionSubgroupPoint, by
      change (2 : ℤ) • actualOneTorsionSubgroupPoint = 0
      ext
      simpa using actualOneTorsionSubgroupPoint.2⟩

@[simp] theorem zmodTwoToActualZeroTorsion_one :
    zmodTwoToActualZeroTorsion 1 = actualZeroTorsionSubgroupPoint := by
  change ZMod.lift 2 _ (1 : ZMod 2) = _
  simpa using ZMod.lift_coe 2
    (⟨zmultiplesHom cmAlgClosureTwoTorsionSubgroup actualZeroTorsionSubgroupPoint, by
      change (2 : ℤ) • actualZeroTorsionSubgroupPoint = 0
      ext; simpa using actualZeroTorsionSubgroupPoint.2⟩) 1

@[simp] theorem zmodTwoToActualOneTorsion_one :
    zmodTwoToActualOneTorsion 1 = actualOneTorsionSubgroupPoint := by
  change ZMod.lift 2 _ (1 : ZMod 2) = _
  simpa using ZMod.lift_coe 2
    (⟨zmultiplesHom cmAlgClosureTwoTorsionSubgroup actualOneTorsionSubgroupPoint, by
      change (2 : ℤ) • actualOneTorsionSubgroupPoint = 0
      ext; simpa using actualOneTorsionSubgroupPoint.2⟩) 1

noncomputable def cmTwoTorsionToActual :
    CMTwoTorsionCarrier →+ cmAlgClosureTwoTorsionSubgroup where
  toFun := fun x => zmodTwoToActualZeroTorsion x.1 + zmodTwoToActualOneTorsion x.2
  map_zero' := by simp
  map_add' := by intro x y; simp; abel

@[simp] theorem cmTwoTorsionToActual_00 : cmTwoTorsionToActual (0,0) = 0 := by
  simp [cmTwoTorsionToActual]
@[simp] theorem cmTwoTorsionToActual_10 :
    cmTwoTorsionToActual (1,0) = actualZeroTorsionSubgroupPoint := by
  simp [cmTwoTorsionToActual]
@[simp] theorem cmTwoTorsionToActual_01 :
    cmTwoTorsionToActual (0,1) = actualOneTorsionSubgroupPoint := by
  simp [cmTwoTorsionToActual]
@[simp] theorem cmTwoTorsionToActual_11 :
    cmTwoTorsionToActual (1,1) = actualMinusOneTorsionSubgroupPoint := by
  simp [cmTwoTorsionToActual, actualZeroTorsion_add_actualOne]

theorem cmTwoTorsionToActual_injective : Function.Injective cmTwoTorsionToActual := by
  intro x y h
  rcases x with ⟨a,b⟩
  rcases y with ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp at h ⊢

theorem cmTwoTorsionToActual_surjective : Function.Surjective cmTwoTorsionToActual := by
  intro P
  rcases P with ⟨P,hP⟩
  rcases (cmAlgClosure_twoTorsion_classification P).1 hP with h0 | hz | h1 | hm
  · subst P; exact ⟨(0,0), by simp⟩
  · subst P; exact ⟨(1,0), by simp [actualZeroTorsionSubgroupPoint]⟩
  · subst P; exact ⟨(0,1), by simp [actualOneTorsionSubgroupPoint]⟩
  · subst P; exact ⟨(1,1), by simp [actualMinusOneTorsionSubgroupPoint]⟩

noncomputable def cmAlgClosureTwoTorsionEquiv :
    CMTwoTorsionCarrier ≃+ cmAlgClosureTwoTorsionSubgroup :=
  AddEquiv.ofBijective cmTwoTorsionToActual
    ⟨cmTwoTorsionToActual_injective, cmTwoTorsionToActual_surjective⟩

theorem cmAlgClosureTwoTorsionEquiv_maps_labels :
    (cmAlgClosureTwoTorsionEquiv cmTorsionInfinityLabel = 0) ∧
    (cmAlgClosureTwoTorsionEquiv cmTorsionZeroLabel = actualZeroTorsionSubgroupPoint) ∧
    (cmAlgClosureTwoTorsionEquiv cmTorsionOneLabel = actualOneTorsionSubgroupPoint) ∧
    (cmAlgClosureTwoTorsionEquiv cmTorsionMinusOneLabel = actualMinusOneTorsionSubgroupPoint) := by
  simp [cmAlgClosureTwoTorsionEquiv, cmTorsionInfinityLabel, cmTorsionZeroLabel,
    cmTorsionOneLabel, cmTorsionMinusOneLabel]

end Synthesis.Millennium.BSD
