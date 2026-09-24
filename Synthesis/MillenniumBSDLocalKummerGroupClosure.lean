import Synthesis.MillenniumBSDSquareClassGroups
import Mathlib.Tactic

/-!
# Group-theoretic local conditions for the explicit 2-Selmer intersection

The square-class quotients are now actual elementary abelian 2-groups.
This file pushes that structure into the local conditions:

* the real equal-sign condition is a subgroup;
* every finite local Kummer image contains the identity;
* every finite local Kummer image is closed under inversion automatically,
  because every square class is self-inverse;
* therefore the only missing subgroup law for a local Kummer image is
  multiplication closure.

That multiplication theorem is precisely the statement that the Kummer map
respects elliptic addition modulo 2, i.e. the real descent theorem required
before E(Q)/2E(Q) -> Sel² can be an honest group homomorphism.
-/

namespace Synthesis.Millennium.BSD

theorem signBit_mul_nonzero
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    signBit (a * b) = Bool.xor (signBit a) (signBit b) := by
  by_cases hna : a < 0
  · by_cases hnb : b < 0
    · have hab : 0 < a * b := mul_pos_of_neg_of_neg hna hnb
      simp [signBit, hna, hnb, not_lt_of_ge hab.le]
    · have hbpos : 0 < b := lt_of_le_of_ne (le_of_not_gt hnb) (Ne.symm hb)
      have hab : a * b < 0 := mul_neg_of_neg_of_pos hna hbpos
      simp [signBit, hna, hnb, hab]
  · have hapos : 0 < a := lt_of_le_of_ne (le_of_not_gt hna) (Ne.symm ha)
    by_cases hnb : b < 0
    · have hab : a * b < 0 := mul_neg_of_pos_of_neg hapos hnb
      simp [signBit, hna, hnb, hab]
    · have hbpos : 0 < b := lt_of_le_of_ne (le_of_not_gt hnb) (Ne.symm hb)
      have hab : 0 < a * b := mul_pos hapos hbpos
      simp [signBit, hna, hnb, not_lt_of_ge hab.le]

theorem squareClassSignBit_mul
    (a b : RatSquareClass) :
    squareClassSignBit (a * b) =
      Bool.xor (squareClassSignBit a) (squareClassSignBit b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  exact signBit_mul_nonzero (x : ℚ) (y : ℚ) x.property y.property

theorem realCondition_one :
    realKummerLocalization (1 : RatSquareClass × RatSquareClass) ∈
      RealKummerImage := by
  change squareClassSignBit (1 : RatSquareClass) =
    squareClassSignBit (1 : RatSquareClass)
  rfl

theorem realCondition_mul
    {a b : RatSquareClass × RatSquareClass}
    (ha : realKummerLocalization a ∈ RealKummerImage)
    (hb : realKummerLocalization b ∈ RealKummerImage) :
    realKummerLocalization (a * b) ∈ RealKummerImage := by
  change squareClassSignBit (a.1 * b.1) =
    squareClassSignBit (a.2 * b.2)
  rw [squareClassSignBit_mul, squareClassSignBit_mul]
  change squareClassSignBit a.1 = squareClassSignBit a.2 at ha
  change squareClassSignBit b.1 = squareClassSignBit b.2 at hb
  rw [ha, hb]

theorem realCondition_inv
    {a : RatSquareClass × RatSquareClass}
    (ha : realKummerLocalization a ∈ RealKummerImage) :
    realKummerLocalization a⁻¹ ∈ RealKummerImage := by
  change squareClassSignBit a.1⁻¹ = squareClassSignBit a.2⁻¹
  rw [ratSquareClass_inv_eq_self, ratSquareClass_inv_eq_self]
  exact ha

def RealKummerSubgroup :
    Subgroup (RatSquareClass × RatSquareClass) where
  carrier := {a | realKummerLocalization a ∈ RealKummerImage}
  one_mem' := realCondition_one
  mul_mem' := fun ha hb => realCondition_mul ha hb
  inv_mem' := fun ha => realCondition_inv ha

theorem localInfinityKummer_eq_one
    (p : ℕ) [Fact p.Prime] :
    localInfinityKummer p =
      (1 : PadicSquareClass p × PadicSquareClass p) := by
  rfl

theorem localKummerImage_one
    (p : ℕ) [Fact p.Prime] :
    (1 : PadicSquareClass p × PadicSquareClass p) ∈
      LocalKummerImage p := by
  rw [← localInfinityKummer_eq_one p]
  exact localInfinity_mem_KummerImage p

theorem padicPair_inv_eq_self
    (p : ℕ) [Fact p.Prime]
    (c : PadicSquareClass p × PadicSquareClass p) :
    c⁻¹ = c := by
  apply Prod.ext <;>
    simp [padicSquareClass_inv_eq_self]

theorem localKummerImage_inv
    {p : ℕ} [Fact p.Prime]
    {c : PadicSquareClass p × PadicSquareClass p}
    (hc : c ∈ LocalKummerImage p) :
    c⁻¹ ∈ LocalKummerImage p := by
  rwa [padicPair_inv_eq_self p c]

def LocalKummerMulClosed
    (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ ⦃a b : PadicSquareClass p × PadicSquareClass p⦄,
    a ∈ LocalKummerImage p →
    b ∈ LocalKummerImage p →
    a * b ∈ LocalKummerImage p

def localKummerSubgroupOfMulClosed
    (p : ℕ) [Fact p.Prime]
    (hmul : LocalKummerMulClosed p) :
    Subgroup (PadicSquareClass p × PadicSquareClass p) where
  carrier := LocalKummerImage p
  one_mem' := localKummerImage_one p
  mul_mem' := hmul
  inv_mem' := fun hc => localKummerImage_inv hc

theorem explicitSelmer_real_condition_is_subgroup :
    {c : RatSquareClass × RatSquareClass |
      realKummerLocalization c ∈ RealKummerImage}
      = RealKummerSubgroup := by
  rfl

end Synthesis.Millennium.BSD
