import Synthesis.MillenniumBSDLocalKummerHomomorphism
import Synthesis.MillenniumBSDSquareClassGroups
import Mathlib.Tactic

/-!
# The explicit all-place 2-Selmer intersection is an actual subgroup

The finite-place conditions are now subgroup conditions because each
LocalKummerImage p has been proved to be the image of the actual local Kummer
homomorphism.

At infinity the condition is equality of the two sign bits.  Multiplying two
pairs with equal coordinate signs preserves equality of signs; inversion is
trivial because every square class has exponent two.

Hence the previously-defined ExplicitTwoSelmerIntersection is promoted from a
set to a literal subgroup of (Q*/Q*²)².
-/

namespace Synthesis.Millennium.BSD

theorem signBit_eq_iff_same_sign
    {a b : ℚ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    signBit a = signBit b
      ↔
    ((0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0)) := by
  unfold signBit
  by_cases ha : a < 0 <;> by_cases hb : b < 0 <;>
    simp [ha, hb] at *
  · exact Or.inr ⟨ha, hb⟩
  · exfalso
    exact hb (lt_of_le_of_ne
      (le_of_not_gt hb)
      (Ne.symm hb0))
  · exfalso
    exact ha (lt_of_le_of_ne
      (le_of_not_gt ha)
      (Ne.symm ha0))
  · exact Or.inl
      ⟨lt_of_le_of_ne (le_of_not_gt ha) (Ne.symm ha0),
       lt_of_le_of_ne (le_of_not_gt hb) (Ne.symm hb0)⟩

theorem signBit_mul_preserves_pair_equality
    {a₁ a₂ b₁ b₂ : ℚ}
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0)
    (ha : signBit a₁ = signBit a₂)
    (hb : signBit b₁ = signBit b₂) :
    signBit (a₁ * b₁) = signBit (a₂ * b₂) := by
  rw [signBit_eq_iff_same_sign ha₁ ha₂] at ha
  rw [signBit_eq_iff_same_sign hb₁ hb₂] at hb
  rw [signBit_eq_iff_same_sign
    (mul_ne_zero ha₁ hb₁)
    (mul_ne_zero ha₂ hb₂)]
  rcases ha with hapos | haneg <;>
    rcases hb with hbpos | hbneg
  · exact Or.inl
      ⟨mul_pos hapos.1 hbpos.1,
       mul_pos hapos.2 hbpos.2⟩
  · exact Or.inr
      ⟨mul_neg_of_pos_of_neg hapos.1 hbneg.1,
       mul_neg_of_pos_of_neg hapos.2 hbneg.2⟩
  · exact Or.inr
      ⟨mul_neg_of_neg_of_pos haneg.1 hbpos.1,
       mul_neg_of_neg_of_pos haneg.2 hbpos.2⟩
  · exact Or.inl
      ⟨mul_pos_of_neg_of_neg haneg.1 hbneg.1,
       mul_pos_of_neg_of_neg haneg.2 hbneg.2⟩

theorem realKummerCondition_mul
    {a b : RatSquareClass × RatSquareClass}
    (ha :
      realKummerLocalization a ∈ RealKummerImage)
    (hb :
      realKummerLocalization b ∈ RealKummerImage) :
    realKummerLocalization (a * b) ∈ RealKummerImage := by
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  refine Quotient.inductionOn a₁ ?_
  intro ar₁
  refine Quotient.inductionOn a₂ ?_
  intro ar₂
  refine Quotient.inductionOn b₁ ?_
  intro br₁
  refine Quotient.inductionOn b₂ ?_
  intro br₂
  change
    signBit ((ar₁ : ℚ) * (br₁ : ℚ))
      =
    signBit ((ar₂ : ℚ) * (br₂ : ℚ))
  change signBit (ar₁ : ℚ) = signBit (ar₂ : ℚ) at ha
  change signBit (br₁ : ℚ) = signBit (br₂ : ℚ) at hb
  exact signBit_mul_preserves_pair_equality
    ar₁.property ar₂.property br₁.property br₂.property
    ha hb

theorem ratSquareClassPair_inv_eq_self
    (a : RatSquareClass × RatSquareClass) :
    a⁻¹ = a := by
  apply Prod.ext <;>
    exact ratSquareClass_inv_eq_self _

def explicitTwoSelmerSubgroup :
    Subgroup (RatSquareClass × RatSquareClass) where
  carrier := ExplicitTwoSelmerIntersection
  one_mem' := by
    have h :=
      torsionKummer_mem_explicitSelmer
        RationalTwoTorsionPoint.infinity
    simpa [torsionKummer, nzRatOne, oneNZ] using h
  mul_mem' := by
    intro a b ha hb
    rcases ha with ⟨haReal, haFinite⟩
    rcases hb with ⟨hbReal, hbFinite⟩
    refine ⟨realKummerCondition_mul haReal hbReal, ?_⟩
    intro p
    letI : Fact p.1.Prime := ⟨p.2⟩
    have hloc :
        localizeKummerPair p.1 (a * b)
          =
        localizeKummerPair p.1 a
          * localizeKummerPair p.1 b := by
      exact (localizeKummerPairHom p.1).map_mul a b
    rw [hloc]
    exact
      (localKummerImageSubgroup p.1).mul_mem
        (haFinite p) (hbFinite p)
  inv_mem' := by
    intro a ha
    have hinv := ratSquareClassPair_inv_eq_self a
    rwa [hinv]

theorem mem_explicitTwoSelmerSubgroup_iff
    (a : RatSquareClass × RatSquareClass) :
    a ∈ explicitTwoSelmerSubgroup
      ↔
    a ∈ ExplicitTwoSelmerIntersection :=
  Iff.rfl

theorem ordinaryKummer_mem_explicitTwoSelmerSubgroup
    (P : OrdinaryKummerPoint) :
    ordinaryKummer P ∈ explicitTwoSelmerSubgroup :=
  ordinaryKummer_mem_explicitSelmer P

theorem torsionKummer_mem_explicitTwoSelmerSubgroup
    (P : RationalTwoTorsionPoint) :
    torsionKummer P ∈ explicitTwoSelmerSubgroup :=
  torsionKummer_mem_explicitSelmer P

end Synthesis.Millennium.BSD
