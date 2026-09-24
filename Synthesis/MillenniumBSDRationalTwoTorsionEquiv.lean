import Synthesis.MillenniumBSDRationalTwoTorsionExact
import Synthesis.MillenniumBSDCMTwoTorsionGaloisModule
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Additive same-object theorem for rational E[2]

The literal rational subgroup killed by two is additively equivalent to
`(ZMod 2)^2`.  The two basis vectors are sent to `(0,0)` and `(1,0)`;
their sum is `(-1,0)` by the already-proved torsion triangle.
-/

namespace Synthesis.Millennium.BSD

def rationalZeroTorsionSubgroupPoint : rationalTwoTorsionSubgroup :=
  ⟨rationalZeroTorsionPoint, rationalZeroTorsion_two_nsmul_zero⟩

def rationalOneTorsionSubgroupPoint : rationalTwoTorsionSubgroup :=
  ⟨rationalOneTorsionPoint, rationalOneTorsion_two_nsmul_zero⟩

def rationalMinusOneTorsionSubgroupPoint : rationalTwoTorsionSubgroup :=
  ⟨rationalMinusOneTorsionPoint, rationalMinusOneTorsion_two_nsmul_zero⟩

noncomputable def zmodTwoToZeroTorsion :
    ZMod 2 →+ rationalTwoTorsionSubgroup :=
  ZMod.lift 2
    ⟨zmultiplesHom rationalTwoTorsionSubgroup
      rationalZeroTorsionSubgroupPoint, by
        change (2 : ℤ) • rationalZeroTorsionSubgroupPoint = 0
        ext
        simpa using rationalZeroTorsion_two_nsmul_zero⟩

noncomputable def zmodTwoToOneTorsion :
    ZMod 2 →+ rationalTwoTorsionSubgroup :=
  ZMod.lift 2
    ⟨zmultiplesHom rationalTwoTorsionSubgroup
      rationalOneTorsionSubgroupPoint, by
        change (2 : ℤ) • rationalOneTorsionSubgroupPoint = 0
        ext
        simpa using rationalOneTorsion_two_nsmul_zero⟩

@[simp] theorem zmodTwoToZeroTorsion_one :
    zmodTwoToZeroTorsion 1 = rationalZeroTorsionSubgroupPoint := by
  change ZMod.lift 2 _ (1 : ZMod 2) = _
  simpa using ZMod.lift_coe 2
    (⟨zmultiplesHom rationalTwoTorsionSubgroup
      rationalZeroTorsionSubgroupPoint, by
        change (2 : ℤ) • rationalZeroTorsionSubgroupPoint = 0
        ext
        simpa using rationalZeroTorsion_two_nsmul_zero⟩) 1

@[simp] theorem zmodTwoToOneTorsion_one :
    zmodTwoToOneTorsion 1 = rationalOneTorsionSubgroupPoint := by
  change ZMod.lift 2 _ (1 : ZMod 2) = _
  simpa using ZMod.lift_coe 2
    (⟨zmultiplesHom rationalTwoTorsionSubgroup
      rationalOneTorsionSubgroupPoint, by
        change (2 : ℤ) • rationalOneTorsionSubgroupPoint = 0
        ext
        simpa using rationalOneTorsion_two_nsmul_zero⟩) 1

noncomputable def cmTwoTorsionToRational :
    CMTwoTorsionCarrier →+ rationalTwoTorsionSubgroup where
  toFun := fun x => zmodTwoToZeroTorsion x.1 + zmodTwoToOneTorsion x.2
  map_zero' := by simp
  map_add' := by
    intro x y
    simp
    abel

@[simp] theorem cmTwoTorsionToRational_00 :
    cmTwoTorsionToRational (0,0) = 0 := by simp [cmTwoTorsionToRational]

@[simp] theorem cmTwoTorsionToRational_10 :
    cmTwoTorsionToRational (1,0) = rationalZeroTorsionSubgroupPoint := by
  simp [cmTwoTorsionToRational]

@[simp] theorem cmTwoTorsionToRational_01 :
    cmTwoTorsionToRational (0,1) = rationalOneTorsionSubgroupPoint := by
  simp [cmTwoTorsionToRational]

@[simp] theorem cmTwoTorsionToRational_11 :
    cmTwoTorsionToRational (1,1) = rationalMinusOneTorsionSubgroupPoint := by
  apply Subtype.ext
  simp [cmTwoTorsionToRational]
  exact rational_zero_add_one_torsion

theorem cmTwoTorsionToRational_injective :
    Function.Injective cmTwoTorsionToRational := by
  intro x y h
  rcases x with ⟨a,b⟩
  rcases y with ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp at h ⊢

theorem cmTwoTorsionToRational_surjective :
    Function.Surjective cmTwoTorsionToRational := by
  intro P
  rcases P with ⟨P,hP⟩
  have hclass := (rationalTwoTorsion_classification P).mp hP
  rcases hclass with h0 | hz | h1 | hm1
  · subst P
    exact ⟨(0,0), by simp⟩
  · subst P
    exact ⟨(1,0), by simp [rationalZeroTorsionSubgroupPoint]⟩
  · subst P
    exact ⟨(0,1), by simp [rationalOneTorsionSubgroupPoint]⟩
  · subst P
    exact ⟨(1,1), by simp [rationalMinusOneTorsionSubgroupPoint]⟩

noncomputable def cmTwoTorsionEquivRationalTwoTorsion :
    CMTwoTorsionCarrier ≃+ rationalTwoTorsionSubgroup :=
  AddEquiv.ofBijective cmTwoTorsionToRational
    ⟨cmTwoTorsionToRational_injective, cmTwoTorsionToRational_surjective⟩

theorem cmTwoTorsionEquivRational_maps_labels :
    (cmTwoTorsionEquivRationalTwoTorsion cmTorsionInfinityLabel = 0) ∧
    (cmTwoTorsionEquivRationalTwoTorsion cmTorsionZeroLabel =
      rationalZeroTorsionSubgroupPoint) ∧
    (cmTwoTorsionEquivRationalTwoTorsion cmTorsionOneLabel =
      rationalOneTorsionSubgroupPoint) ∧
    (cmTwoTorsionEquivRationalTwoTorsion cmTorsionMinusOneLabel =
      rationalMinusOneTorsionSubgroupPoint) := by
  simp [cmTwoTorsionEquivRationalTwoTorsion,
    cmTorsionInfinityLabel, cmTorsionZeroLabel,
    cmTorsionOneLabel, cmTorsionMinusOneLabel]

end Synthesis.Millennium.BSD
