import Synthesis.MillenniumBSDCMQuarticJacobi
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Tactic

/-!
# The square of the split quartic character is the quadratic character

On a finite field, the unit group is cyclic.  Hence there is at most one
nontrivial quadratic multiplicative character with values in C: on a cyclic
generator its value must be -1.  This identifies the square of any exact
order-four character with the complexification of the canonical quadratic
character.
-/

namespace Synthesis.Millennium.BSD

theorem nontrivialQuadraticCharacter_unique
    {F : Type*} [Field F] [Fintype F]
    {χ ψ : MulChar F ℂ}
    (hχq : χ.IsQuadratic) (hψq : ψ.IsQuadratic)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) :
    χ = ψ := by
  classical
  let g : Fˣ := Classical.choose (inferInstance : IsCyclic Fˣ).exists_generator
  have hg : ∀ x : Fˣ, x ∈ Subgroup.zpowers g :=
    Classical.choose_spec (inferInstance : IsCyclic Fˣ).exists_generator
  rw [MulChar.eq_iff hg χ ψ]
  have hχg0 : χ (g : F) ≠ 0 := by
    exact (IsUnit.map χ g.isUnit).ne_zero
  have hψg0 : ψ (g : F) ≠ 0 := by
    exact (IsUnit.map ψ g.isUnit).ne_zero
  have hχg1 : χ (g : F) ≠ 1 := by
    intro h
    apply hχ
    rw [MulChar.eq_iff hg χ 1]
    simpa using h
  have hψg1 : ψ (g : F) ≠ 1 := by
    intro h
    apply hψ
    rw [MulChar.eq_iff hg ψ 1]
    simpa using h
  rcases hχq (g : F) with h0 | h1 | hm1
  · exact (hχg0 h0).elim
  · exact (hχg1 h1).elim
  rcases hψq (g : F) with h0 | h1 | hm1'
  · exact (hψg0 h0).elim
  · exact (hψg1 h1).elim
  exact hm1.trans hm1'.symm

noncomputable def complexQuadraticChar
    (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

theorem complexQuadraticChar_isQuadratic
    (p : ℕ) [Fact p.Prime] :
    (complexQuadraticChar p).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)

theorem complexQuadraticChar_ne_one
    {p : ℕ} [Fact hp : p.Prime] (hp2 : p ≠ 2) :
    complexQuadraticChar p ≠ 1 := by
  unfold complexQuadraticChar
  exact (MulChar.ringHomComp_ne_one_iff (Int.castRingHom ℂ).injective).mpr
    (quadraticChar_ne_one (F := ZMod p) (by simpa [ringChar_zmod_n] using hp2))

theorem splitQuarticCharacter_sq_isQuadratic
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    (splitQuarticCharacter p hmod ^ 2).IsQuadratic := by
  rw [MulChar.isQuadratic_iff_sq_eq_one]
  rw [← pow_mul]
  have horder := splitQuarticCharacter_orderOf hmod
  have hpow := pow_orderOf_eq_one (splitQuarticCharacter p hmod)
  rw [horder] at hpow
  simpa using hpow

theorem splitQuarticCharacter_sq_eq_complexQuadraticChar
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    splitQuarticCharacter p hmod ^ 2 = complexQuadraticChar p := by
  have hp2 : p ≠ 2 := by
    intro hpEq
    subst p
    norm_num at hmod
  exact nontrivialQuadraticCharacter_unique
    (splitQuarticCharacter_sq_isQuadratic hmod)
    (complexQuadraticChar_isQuadratic p)
    (splitQuarticCharacter_sq_ne_one hmod)
    (complexQuadraticChar_ne_one hp2)

theorem splitQuarticCharacter_sq_apply
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1)
    (x : ZMod p) :
    (splitQuarticCharacter p hmod ^ 2) x =
      (quadraticChar (ZMod p) x : ℂ) := by
  rw [splitQuarticCharacter_sq_eq_complexQuadraticChar hmod]
  rfl

end Synthesis.Millennium.BSD
