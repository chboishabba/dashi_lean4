import Synthesis.MillenniumBSDQuadraticCharacterFiniteFieldReduction
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

/-!
# A nontrivial continuous quadratic character cuts out a quadratic field

The fixed field of a continuous quadratic character is already known finite
and Galois.  Its Galois group is the quotient by the character kernel, hence
isomorphic to the character range, a subgroup of the two-element sign group.
Thus the field degree is at most two.  A nontrivial character rules out degree
one, so the degree is exactly two.
-/

namespace Synthesis.Millennium.BSD

open Field MulAction Set

noncomputable def quadraticCharacterGalEquivRange
    (χ : RationalQuadraticCharacter) :
    Gal(quadraticCharacterFixedField χ / ℚ) ≃*
      MonoidHom.mrange χ.toMonoidHom := by
  let H : ClosedSubgroup RationalAbsoluteGalois :=
    quadraticCharacterClosedKernel χ
  letI : H.Normal := by
    change (quadraticCharacterKernel χ).Normal
    exact quadraticCharacterKernel_normal χ
  exact
    (InfiniteGalois.normalAutEquivQuotient H).symm.trans
      (QuotientGroup.quotientKerEquivRange χ.toMonoidHom)

theorem quadraticCharacterFixedField_finrank_le_two
    (χ : RationalQuadraticCharacter) :
    Module.finrank ℚ (quadraticCharacterFixedField χ) ≤ 2 := by
  letI : FiniteDimensional ℚ (quadraticCharacterFixedField χ) :=
    quadraticCharacterFixedField_finiteDimensional χ
  letI : IsGalois ℚ (quadraticCharacterFixedField χ) :=
    quadraticCharacterFixedField_isGalois χ
  calc
    Module.finrank ℚ (quadraticCharacterFixedField χ)
        = Nat.card Gal(quadraticCharacterFixedField χ / ℚ) := by
          symm
          exact IsGalois.card_aut_eq_finrank _ _
    _ = Nat.card (MonoidHom.mrange χ.toMonoidHom) := by
          exact Nat.card_congr (quadraticCharacterGalEquivRange χ).toEquiv
    _ ≤ Nat.card RationalQuadraticSign :=
          Nat.card_le_card_of_injective
            (fun x : MonoidHom.mrange χ.toMonoidHom => x.1)
            Subtype.val_injective
    _ = 2 := by
          rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem quadraticCharacterFixedField_ne_bot
    {χ : RationalQuadraticCharacter} (hχ : χ ≠ 1) :
    quadraticCharacterFixedField χ ≠ ⊥ := by
  intro hbot
  apply hχ
  apply ContinuousMonoidHom.ext
  intro σ
  have hker : σ ∈ quadraticCharacterKernel χ := by
    rw [← quadraticCharacterFixedField_fixingSubgroup χ, hbot]
    simp
  exact hker

theorem quadraticCharacterFixedField_finrank_ne_one
    {χ : RationalQuadraticCharacter} (hχ : χ ≠ 1) :
    Module.finrank ℚ (quadraticCharacterFixedField χ) ≠ 1 := by
  intro hone
  have hbot : quadraticCharacterFixedField χ = ⊥ :=
    (IntermediateField.finrank_eq_one_iff).mp hone
  exact quadraticCharacterFixedField_ne_bot hχ hbot

theorem quadraticCharacterFixedField_finrank_eq_two
    {χ : RationalQuadraticCharacter} (hχ : χ ≠ 1) :
    Module.finrank ℚ (quadraticCharacterFixedField χ) = 2 := by
  have hle := quadraticCharacterFixedField_finrank_le_two χ
  have hpos : 0 < Module.finrank ℚ (quadraticCharacterFixedField χ) :=
    Module.finrank_pos
  have hne := quadraticCharacterFixedField_finrank_ne_one hχ
  omega

/--
The scalar Kummer surjectivity residual is now purely the degree-two
square-root classification inside the algebraic closure.
-/
def QuadraticFixedFieldGeneratedBySquareRoot : Prop :=
  ∀ χ : RationalQuadraticCharacter, χ ≠ 1 →
    ∃ a : NonzeroRat,
      quadraticCharacterKernel χ =
        quadraticCharacterKernel (rationalQuadraticKummerCharacter a)

theorem fixedFieldSquareRootClassification_of_degreeTwo
    (h : ∀ χ : RationalQuadraticCharacter, χ ≠ 1 →
      ∃ a : NonzeroRat,
        quadraticCharacterKernel χ =
          quadraticCharacterKernel (rationalQuadraticKummerCharacter a)) :
    QuadraticCharacterFixedFieldSquareRootClassification := h

end Synthesis.Millennium.BSD
