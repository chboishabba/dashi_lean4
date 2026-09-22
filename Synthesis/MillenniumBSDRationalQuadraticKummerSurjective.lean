import Synthesis.MillenniumBSDQuadraticCharacterSquareRootGenerator
import Mathlib.Tactic

/-!
# Scalar quadratic Kummer surjectivity

For a nontrivial continuous quadratic character χ, the previous file
constructs a generator r of its fixed field with r² = D ∈ Qˣ.

Because r generates the fixed field, an absolute-Galois automorphism lies in
`ker χ` iff it fixes r.  The canonical Kummer root of D has the same square
as r, so root-choice invariance says it has exactly the same stabilizer.
Thus χ and the Kummer character of D have the same kernel; the existing
C₂-valued kernel comparison then gives equality of characters.

This closes the scalar square-class ↔ continuous quadratic-character
bijection without general Hilbert 90.
-/

namespace Synthesis.Millennium.BSD

open Field MulAction Set

private theorem rationalKummerBitOfRoot_eq_zero_iff
    (r : AlgebraicClosure ℚ) (σ : RationalAbsoluteGalois) :
    rationalKummerBitOfRoot r σ = 0 ↔ σ r = r := by
  by_cases h : σ r = r <;> simp [rationalKummerBitOfRoot,h]

theorem mem_quadraticCharacterKernel_iff_fixes_generator
    {χ : RationalQuadraticCharacter} (hχ : χ ≠ 1)
    (σ : RationalAbsoluteGalois) :
    σ ∈ quadraticCharacterKernel χ ↔
      σ (quadraticCharacterAmbientRoot χ hχ) =
        quadraticCharacterAmbientRoot χ hχ := by
  let G := quadraticCharacterSquareRootGenerator χ hχ
  let L := quadraticCharacterFixedField χ
  let rL : L := G.value
  change σ ∈ quadraticCharacterKernel χ ↔ σ (rL : AlgebraicClosure ℚ) = rL
  constructor
  · intro hσ
    have hfix : σ ∈ L.fixingSubgroup := by
      rw [quadraticCharacterFixedField_fixingSubgroup χ]
      exact hσ
    exact (IntermediateField.mem_fixingSubgroup_iff σ L).mp hfix rL rL.property
  · intro hr
    rw [← quadraticCharacterFixedField_fixingSubgroup χ]
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    let xL : L := ⟨x,hx⟩
    have hxAdjoin : xL ∈ Algebra.adjoin ℚ ({rL} : Set L) := by
      rw [G.adjoin_eq_top]
      trivial
    have hfixAll : σ (xL : AlgebraicClosure ℚ) = xL := by
      induction hxAdjoin using Algebra.adjoin_induction with
      | mem y hy =>
          have hy' : y = rL := by simpa using hy
          subst y
          exact hr
      | algebraMap q => simp
      | add x y hx hy ihx ihy =>
          simpa [map_add] using congrArg₂ (· + ·) ihx ihy
      | mul x y hx hy ihx ihy =>
          simpa [map_mul] using congrArg₂ (· * ·) ihx ihy
    simpa [xL] using hfixAll

theorem mem_kummerKernel_iff_fixes_generatorRadicandRoot
    {χ : RationalQuadraticCharacter} (hχ : χ ≠ 1)
    (σ : RationalAbsoluteGalois) :
    σ ∈ quadraticCharacterKernel
      (rationalQuadraticKummerCharacter
        ⟨(quadraticCharacterSquareRootGenerator χ hχ).radicand,
          (quadraticCharacterSquareRootGenerator χ hχ).radicand_ne_zero⟩) ↔
      σ (quadraticCharacterAmbientRoot χ hχ) =
        quadraticCharacterAmbientRoot χ hχ := by
  let G := quadraticCharacterSquareRootGenerator χ hχ
  let a : NonzeroRat := ⟨G.radicand,G.radicand_ne_zero⟩
  let r := quadraticCharacterAmbientRoot χ hχ
  have hsquares : rationalKummerRoot a * rationalKummerRoot a = r * r := by
    rw [rationalKummerRoot_spec a]
    exact (quadraticCharacterAmbientRoot_sq χ hχ).symm
  change rationalQuadraticKummerCharacter a σ = 1 ↔ σ r = r
  have hbit :
      rationalKummerBit a σ = rationalKummerBitOfRoot r σ := by
    rw [rationalKummerBit_eq_ofRoot]
    exact rationalKummerBitOfRoot_independent hsquares σ
  constructor
  · intro hχσ
    have hadd := congrArg Multiplicative.toAdd hχσ
    have hz : rationalKummerBit a σ = 0 := by
      simpa [rationalQuadraticKummerCharacter_apply] using hadd
    exact (rationalKummerBitOfRoot_eq_zero_iff r σ).mp (hbit ▸ hz)
  · intro hr
    apply Multiplicative.toAdd_injective
    change rationalKummerBit a σ = 0
    rw [hbit]
    exact (rationalKummerBitOfRoot_eq_zero_iff r σ).mpr hr

theorem quadraticCharacter_kernel_eq_kummer_of_nontrivial
    {χ : RationalQuadraticCharacter} (hχ : χ ≠ 1) :
    ∃ a : NonzeroRat,
      quadraticCharacterKernel χ =
        quadraticCharacterKernel (rationalQuadraticKummerCharacter a) := by
  let G := quadraticCharacterSquareRootGenerator χ hχ
  let a : NonzeroRat := ⟨G.radicand,G.radicand_ne_zero⟩
  refine ⟨a,?_⟩
  ext σ
  rw [mem_quadraticCharacterKernel_iff_fixes_generator hχ σ]
  exact (mem_kummerKernel_iff_fixes_generatorRadicandRoot hχ σ).symm

theorem quadraticCharacterFixedFieldSquareRootClassification_paid :
    QuadraticCharacterFixedFieldSquareRootClassification := by
  intro χ hχ
  exact quadraticCharacter_kernel_eq_kummer_of_nontrivial hχ

theorem rationalQuadraticKummerSurjectivity_paid :
    RationalQuadraticKummerSurjectivity := by
  exact rationalQuadraticKummerSurjective_of_fixedFieldClassification
    quadraticCharacterFixedFieldSquareRootClassification_paid

theorem rationalQuadraticKummerCharacterBijection_paid :
    RationalQuadraticKummerCharacterBijection := by
  exact rationalQuadraticKummerBijection_of_surjective
    rationalQuadraticKummerSurjectivity_paid

end Synthesis.Millennium.BSD
