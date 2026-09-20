import Synthesis.MillenniumBSDCMQuarticQuadraticBridge
import Synthesis.MillenniumBSDFrobeniusPointCount
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Tactic

/-!
# Split CM cubic character sum as two Jacobi sums

Let χ be the exact order-four character at a split prime and η = χ².
Since η is the complexified quadratic character, the cubic character sum for
E : y² = x³ - x may be rewritten

  S = Σ_x η(x³-x)
    = Σ_x χ(x²) η(1-x²).

Grouping by y=x² gives a fibre cardinality 1+η(y).  Expanding and using
χ³=χ⁻¹ yields

  S = J(χ,η) + J(χ⁻¹,η).
-/

namespace Synthesis.Millennium.BSD

open scoped BigOperators

noncomputable def splitQuadraticShadow
    (p : ℕ) [Fact p.Prime] (hmod : p % 4 = 1) :
    MulChar (ZMod p) ℂ :=
  splitQuarticCharacter p hmod ^ 2

theorem splitQuadraticShadow_eq_complexQuadraticChar
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    splitQuadraticShadow p hmod = complexQuadraticChar p :=
  splitQuarticCharacter_sq_eq_complexQuadraticChar hmod

theorem splitQuarticCharacter_cube_eq_inv
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    splitQuarticCharacter p hmod ^ 3 =
      (splitQuarticCharacter p hmod)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← pow_succ]
  have hpow := pow_orderOf_eq_one (splitQuarticCharacter p hmod)
  rw [splitQuarticCharacter_orderOf hmod] at hpow
  simpa using hpow

theorem splitQuadraticShadow_neg_one
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    splitQuadraticShadow p hmod (-1) = 1 := by
  rw [splitQuadraticShadow_eq_complexQuadraticChar hmod]
  unfold complexQuadraticChar
  rw [MulChar.ringHomComp_apply]
  have hsquare : IsSquare (-1 : ZMod p) :=
    ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
  have hne : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  rw [quadraticChar_one_iff_isSquare hne.mpr]
  · simp
  · exact hsquare

theorem splitQuadraticShadow_cmCubic
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1)
    (x : ZMod p) :
    splitQuadraticShadow p hmod (cmCubic x)
      = splitQuadraticShadow p hmod x *
          splitQuadraticShadow p hmod (1 - x ^ 2) := by
  have hcubic : cmCubic x = - (x * (1 - x^2)) := by
    simp [cmCubic]
    ring
  rw [hcubic, map_neg, splitQuadraticShadow_neg_one hmod,
    map_mul, one_mul]

theorem splitQuadraticShadow_apply_eq_quartic_square_input
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1)
    (x : ZMod p) :
    splitQuadraticShadow p hmod x =
      splitQuarticCharacter p hmod (x ^ 2) := by
  unfold splitQuadraticShadow
  simp [pow_two, map_mul]

theorem split_cubic_summand_square_form
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1)
    (x : ZMod p) :
    (quadraticChar (ZMod p) (cmCubic x) : ℂ)
      = splitQuarticCharacter p hmod (x ^ 2) *
          splitQuadraticShadow p hmod (1 - x ^ 2) := by
  rw [← splitQuarticCharacter_sq_apply hmod]
  change splitQuadraticShadow p hmod (cmCubic x) = _
  rw [splitQuadraticShadow_cmCubic hmod,
    splitQuadraticShadow_apply_eq_quartic_square_input hmod]

theorem sum_square_pullback
    {p : ℕ} [Fact hp : p.Prime] (f : ZMod p → ℂ) :
    (∑ x : ZMod p, f (x ^ 2)) =
      ∑ y : ZMod p,
        (({x : ZMod p | x ^ 2 = y}.toFinset.card : ℕ) : ℂ) * f y := by
  classical
  rw [← Fintype.sum_fiberwise' (fun x : ZMod p => x ^ 2) f]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_const]
  simp

theorem split_square_fiber_card_complex
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1)
    (y : ZMod p) :
    (({x : ZMod p | x ^ 2 = y}.toFinset.card : ℕ) : ℂ)
      = splitQuadraticShadow p hmod y + 1 := by
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hmod
  have hcard := quadraticChar_card_sqrts
    ((ringChar_zmod_n p).substr hp2) y
  exact_mod_cast hcard.trans <| by
    rw [← splitQuarticCharacter_sq_apply hmod]
    rfl

theorem split_fiber_expansion
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1)
    (y : ZMod p) :
    (splitQuadraticShadow p hmod y + 1) *
        (splitQuarticCharacter p hmod y *
          splitQuadraticShadow p hmod (1-y))
      = splitQuarticCharacter p hmod y *
          splitQuadraticShadow p hmod (1-y)
        + (splitQuarticCharacter p hmod)⁻¹ y *
          splitQuadraticShadow p hmod (1-y) := by
  have hcub := congrFun
    (show (splitQuarticCharacter p hmod ^ 3 : MulChar (ZMod p) ℂ) =
        (splitQuarticCharacter p hmod)⁻¹ from
      splitQuarticCharacter_cube_eq_inv hmod) y
  change
    ((splitQuarticCharacter p hmod ^ 2) y + 1) *
        (splitQuarticCharacter p hmod y *
          (splitQuarticCharacter p hmod ^ 2) (1-y))
      = _
  simp only [MulChar.pow_apply_coe] at hcub ⊢
  rw [← hcub]
  ring

noncomputable def splitJacobiPlus
    (p : ℕ) [Fact p.Prime] (hmod : p % 4 = 1) : ℂ :=
  jacobiSum (splitQuarticCharacter p hmod)
    (splitQuadraticShadow p hmod)

noncomputable def splitJacobiMinus
    (p : ℕ) [Fact p.Prime] (hmod : p % 4 = 1) : ℂ :=
  jacobiSum (splitQuarticCharacter p hmod)⁻¹
    (splitQuadraticShadow p hmod)

theorem split_cmCharacterSum_eq_two_jacobi
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    (cmCharacterSum p : ℂ) =
      splitJacobiPlus p hmod + splitJacobiMinus p hmod := by
  classical
  unfold cmCharacterSum cmCharacterTerm
  rw [Int.cast_sum]
  calc
    (∑ x : ZMod p, (quadraticChar (ZMod p) (cmCubic x) : ℂ))
        = ∑ x : ZMod p,
            splitQuarticCharacter p hmod (x^2) *
              splitQuadraticShadow p hmod (1-x^2) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact split_cubic_summand_square_form hmod x
    _ = ∑ y : ZMod p,
          (({x : ZMod p | x^2 = y}.toFinset.card : ℕ) : ℂ) *
            (splitQuarticCharacter p hmod y *
              splitQuadraticShadow p hmod (1-y)) := by
            exact sum_square_pullback
              (fun y : ZMod p =>
                splitQuarticCharacter p hmod y *
                  splitQuadraticShadow p hmod (1-y))
    _ = ∑ y : ZMod p,
          (splitQuadraticShadow p hmod y + 1) *
            (splitQuarticCharacter p hmod y *
              splitQuadraticShadow p hmod (1-y)) := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [split_square_fiber_card_complex hmod]
    _ = ∑ y : ZMod p,
          (splitQuarticCharacter p hmod y *
              splitQuadraticShadow p hmod (1-y)
            + (splitQuarticCharacter p hmod)⁻¹ y *
              splitQuadraticShadow p hmod (1-y)) := by
            apply Finset.sum_congr rfl
            intro y hy
            exact split_fiber_expansion hmod y
    _ = splitJacobiPlus p hmod + splitJacobiMinus p hmod := by
            rw [Finset.sum_add_distrib]
            rfl

end Synthesis.Millennium.BSD
