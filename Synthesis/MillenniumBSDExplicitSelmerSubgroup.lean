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

theorem signBit_mul
    {a b : ℚ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    signBit (a * b) = Bool.xor (signBit a) (signBit b) := by
  by_cases ha : a < 0
  · by_cases hb : b < 0
    · have hab : 0 < a * b :=
        mul_pos_of_neg_of_neg ha hb
      simp [signBit, ha, hb, not_lt_of_ge hab.le]
    · have hbpos : 0 < b :=
        lt_of_le_of_ne (le_of_not_gt hb) (Ne.symm hb0)
      have hab : a * b < 0 :=
        mul_neg_of_neg_of_pos ha hbpos
      simp [signBit, ha, hb, hab]
  · have hapos : 0 < a :=
      lt_of_le_of_ne (le_of_not_gt ha) (Ne.symm ha0)
    by_cases hb : b < 0
    · have hab : a * b < 0 :=
        mul_neg_of_pos_of_neg hapos hb
      simp [signBit, ha, hb, hab]
    · have hbpos : 0 < b :=
        lt_of_le_of_ne (le_of_not_gt hb) (Ne.symm hb0)
      have hab : 0 < a * b :=
        mul_pos hapos hbpos
      simp [signBit, ha, hb, not_lt_of_ge hab.le]

theorem squareClassSignBit_mul
    (a b : RatSquareClass) :
    squareClassSignBit (a * b)
      =
    Bool.xor (squareClassSignBit a) (squareClassSignBit b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro ar br
  change signBit ((ar : ℚ) * (br : ℚ))
      =
    Bool.xor (signBit (ar : ℚ)) (signBit (br : ℚ))
  exact signBit_mul ar.property br.property

theorem realKummerCondition_mul
    {a b : RatSquareClass × RatSquareClass}
    (ha :
      realKummerLocalization a ∈ RealKummerImage)
    (hb :
      realKummerLocalization b ∈ RealKummerImage) :
    realKummerLocalization (a * b) ∈ RealKummerImage := by
  change squareClassSignBit (a.1 * b.1)
      = squareClassSignBit (a.2 * b.2)
  change squareClassSignBit a.1 = squareClassSignBit a.2 at ha
  change squareClassSignBit b.1 = squareClassSignBit b.2 at hb
  rw [squareClassSignBit_mul, squareClassSignBit_mul, ha, hb]

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
