import Synthesis.MillenniumBSDRationalQuadraticKummerHom
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Tactic

/-!
# Injectivity of the scalar quadratic Kummer map

If the continuous quadratic character of a square class is trivial, its chosen
square root is fixed by every element of the absolute Galois group.  Infinite
Galois theory identifies the fixed field with Q, so that root is rational and
the representative is a rational square.

Thus the square-class-to-character map is injective.  The only remaining
scalar Kummer theorem is surjectivity onto continuous quadratic characters.
-/

namespace Synthesis.Millennium.BSD

open Field MulAction Set

theorem rationalKummerRoot_mem_rational_of_character_trivial
    (a : NonzeroRat)
    (hchar : rationalQuadraticKummerCharacter a = 1) :
    rationalKummerRoot a ∈
      Set.range (algebraMap ℚ (AlgebraicClosure ℚ)) := by
  rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
  intro σ
  have hσ := DFunLike.congr_fun hchar σ
  apply (rationalKummerBit_eq_zero_iff a σ).mp
  have hadd := congrArg Multiplicative.toAdd hσ
  simpa [rationalQuadraticKummerCharacter_apply] using hadd

theorem squareClass_eq_one_of_character_trivial
    (a : NonzeroRat)
    (hchar : rationalQuadraticKummerCharacter a = 1) :
    squareClassOf a = (1 : RatSquareClass) := by
  rcases rationalKummerRoot_mem_rational_of_character_trivial a hchar with
    ⟨q,hq⟩
  have hq0 : q ≠ 0 := by
    intro h0
    subst q
    have : rationalKummerRoot a = 0 := by simpa using hq.symm
    exact rationalKummerRoot_ne_zero a this
  let qNZ : NonzeroRat := ⟨q,hq0⟩
  apply Quotient.sound
  refine ⟨nzRatOne, qNZ, ?_⟩
  change (a : ℚ) * (1 : ℚ) ^ 2 = (1 : ℚ) * q ^ 2
  simp only [mul_one, one_mul, one_pow]
  have hs := rationalKummerRoot_spec a
  rw [← hq] at hs
  apply (algebraMap ℚ (AlgebraicClosure ℚ)).injective
  simpa [map_pow] using hs.symm

theorem ratSquareClassKummerHom_ker_trivial
    (c : RatSquareClass)
    (hc : ratSquareClassKummerHom c = 1) :
    c = 1 := by
  refine Quotient.inductionOn c ?_
  intro a
  change ratSquareClassKummerCharacter (squareClassOf a) = 1 at hc
  change squareClassOf a = 1
  exact squareClass_eq_one_of_character_trivial a hc

theorem ratSquareClassKummerHom_injective :
    Function.Injective ratSquareClassKummerHom := by
  intro a b hab
  have hker : ratSquareClassKummerHom (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  have hclass := ratSquareClassKummerHom_ker_trivial (a * b⁻¹) hker
  exact div_eq_one.mp (by simpa [div_eq_mul_inv] using hclass)

theorem rationalSquareClassKummerHom_injective :
    Function.Injective rationalSquareClassKummerHom := by
  intro a b hab
  apply mathlibSquareClassToRat_rightInverse.injective
  apply ratSquareClassKummerHom_injective
  simpa [rationalSquareClassKummerHom] using hab

/-- BA4 is now reduced to the surjectivity half of continuous quadratic Kummer theory. -/
def RationalQuadraticKummerSurjectivity : Prop :=
  Function.Surjective rationalSquareClassKummerHom

theorem rationalQuadraticKummerBijection_of_surjective
    (hsurj : RationalQuadraticKummerSurjectivity) :
    RationalQuadraticKummerCharacterBijection := by
  exact ⟨rationalSquareClassKummerHom_injective, hsurj⟩

end Synthesis.Millennium.BSD
