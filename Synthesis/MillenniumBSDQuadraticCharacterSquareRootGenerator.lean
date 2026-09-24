import Synthesis.MillenniumBSDQuadraticCharacterDegreeTwo
import Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension
import Mathlib.Tactic

/-!
# A nontrivial quadratic-character fixed field has a square-root generator

For a nontrivial continuous quadratic character χ, its fixed field Lχ has
degree two over Q.  Mathlib identifies every rank-two extension with a
`QuadraticAlgebra Q a b`.  Completing the square gives the generator

  r = 2ω - b,      r² = b² + 4a.

Since 2 is invertible in Q, `r` generates the same algebra as `ω`.
This is exactly the square-root generator needed for scalar Kummer
surjectivity; no general Hilbert-90 argument is required.
-/

namespace Synthesis.Millennium.BSD

open Field MulAction Set
open QuadraticAlgebra

private theorem completedSquare_sq
    (a b : ℚ) :
    ((2 : QuadraticAlgebra ℚ a b) * ω - algebraMap ℚ _ b) ^ 2 =
      algebraMap ℚ _ (b ^ 2 + 4 * a) := by
  rw [sq]
  rw [mul_sub, sub_mul, omega_mul_omega_eq_algebraMap]
  push_cast
  ring

private theorem completedSquare_ne_zero
    (a b : ℚ) :
    (2 : QuadraticAlgebra ℚ a b) * ω - algebraMap ℚ _ b ≠ 0 := by
  intro h
  have him := congrArg QuadraticAlgebra.im h
  norm_num at him

private theorem omega_mem_adjoin_completedSquare
    (a b : ℚ) :
    ω ∈ Algebra.adjoin ℚ
      ({(2 : QuadraticAlgebra ℚ a b) * ω - algebraMap ℚ _ b} :
        Set (QuadraticAlgebra ℚ a b)) := by
  let r : QuadraticAlgebra ℚ a b :=
    (2 : QuadraticAlgebra ℚ a b) * ω - algebraMap ℚ _ b
  have hr : r ∈ Algebra.adjoin ℚ ({r} : Set (QuadraticAlgebra ℚ a b)) :=
    Algebra.self_mem_adjoin_singleton ℚ r
  have hb : algebraMap ℚ (QuadraticAlgebra ℚ a b) b ∈
      Algebra.adjoin ℚ ({r} : Set (QuadraticAlgebra ℚ a b)) :=
    (Algebra.adjoin ℚ ({r} : Set (QuadraticAlgebra ℚ a b))).algebraMap_mem b
  have hsum : r + algebraMap ℚ (QuadraticAlgebra ℚ a b) b ∈
      Algebra.adjoin ℚ ({r} : Set (QuadraticAlgebra ℚ a b)) :=
    (Algebra.adjoin ℚ ({r} : Set (QuadraticAlgebra ℚ a b))).add_mem hr hb
  have hhalf : algebraMap ℚ (QuadraticAlgebra ℚ a b) (1/2 : ℚ) ∈
      Algebra.adjoin ℚ ({r} : Set (QuadraticAlgebra ℚ a b)) :=
    (Algebra.adjoin ℚ ({r} : Set (QuadraticAlgebra ℚ a b))).algebraMap_mem _
  have hmul := (Algebra.adjoin ℚ ({r} : Set (QuadraticAlgebra ℚ a b))).mul_mem
    hhalf hsum
  have heq :
      algebraMap ℚ (QuadraticAlgebra ℚ a b) (1/2 : ℚ) *
        (r + algebraMap ℚ (QuadraticAlgebra ℚ a b) b) = ω := by
    dsimp [r]
    push_cast
    ring
  simpa [heq] using hmul

private theorem adjoin_completedSquare_eq_top
    (a b : ℚ) :
    Algebra.adjoin ℚ
      ({(2 : QuadraticAlgebra ℚ a b) * ω - algebraMap ℚ _ b} :
        Set (QuadraticAlgebra ℚ a b)) = ⊤ := by
  apply top_unique
  rw [← QuadraticAlgebra.adjoin_omega_eq_top (R := ℚ) (a := a) (b := b)]
  exact Algebra.adjoin_le.mpr (by
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact omega_mem_adjoin_completedSquare a b)

structure QuadraticFixedFieldSquareRootGenerator
    (χ : RationalQuadraticCharacter) where
  value : quadraticCharacterFixedField χ
  radicand : ℚ
  radicand_ne_zero : radicand ≠ 0
  square_spec : value * value =
    algebraMap ℚ (quadraticCharacterFixedField χ) radicand
  adjoin_eq_top :
    Algebra.adjoin ℚ ({value} : Set (quadraticCharacterFixedField χ)) = ⊤

noncomputable def quadraticCharacterSquareRootGenerator
    (χ : RationalQuadraticCharacter) (hχ : χ ≠ 1) :
    QuadraticFixedFieldSquareRootGenerator χ := by
  let L := quadraticCharacterFixedField χ
  letI : FiniteDimensional ℚ L :=
    quadraticCharacterFixedField_finiteDimensional χ
  letI : Algebra.IsQuadraticExtension ℚ L := {
    finrank_eq_two' := quadraticCharacterFixedField_finrank_eq_two hχ
  }
  rcases Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra
      (R := ℚ) (A := L) with ⟨a,b,⟨e⟩⟩
  let rq : QuadraticAlgebra ℚ a b :=
    (2 : QuadraticAlgebra ℚ a b) * ω - algebraMap ℚ _ b
  let rL : L := e.symm rq
  let D : ℚ := b^2 + 4*a
  have hrqSq : rq ^ 2 = algebraMap ℚ _ D := by
    exact completedSquare_sq a b
  have hrLSq : rL * rL = algebraMap ℚ L D := by
    apply e.injective
    simp [rL,rq,D, hrqSq]
  have hrq0 : rq ≠ 0 := completedSquare_ne_zero a b
  have hD0 : D ≠ 0 := by
    intro hD
    have : rq ^ 2 = 0 := by simpa [hD] using hrqSq
    have : rq = 0 := pow_eq_zero this
    exact hrq0 this
  have hadjoin : Algebra.adjoin ℚ ({rL} : Set L) = ⊤ := by
    apply e.symm.toAlgHom.injective
    ext x
    simp only [AlgEquiv.toAlgHom_eq_coe]
    have htransport :
        Algebra.map e (Algebra.adjoin ℚ ({rL} : Set L)) =
          Algebra.adjoin ℚ ({rq} : Set (QuadraticAlgebra ℚ a b)) := by
      rw [Algebra.map_adjoin]
      congr 1
      ext y
      simp [rL,rq]
    rw [← htransport, adjoin_completedSquare_eq_top a b]
    simp
  exact {
    value := rL
    radicand := D
    radicand_ne_zero := hD0
    square_spec := hrLSq
    adjoin_eq_top := hadjoin
  }

/-- Embedded square-root generator in the ambient algebraic closure. -/
noncomputable def quadraticCharacterAmbientRoot
    (χ : RationalQuadraticCharacter) (hχ : χ ≠ 1) :
    AlgebraicClosure ℚ :=
  (quadraticCharacterSquareRootGenerator χ hχ).value

theorem quadraticCharacterAmbientRoot_sq
    (χ : RationalQuadraticCharacter) (hχ : χ ≠ 1) :
    quadraticCharacterAmbientRoot χ hχ * quadraticCharacterAmbientRoot χ hχ =
      algebraMap ℚ (AlgebraicClosure ℚ)
        (quadraticCharacterSquareRootGenerator χ hχ).radicand := by
  exact_mod_cast (quadraticCharacterSquareRootGenerator χ hχ).square_spec

end Synthesis.Millennium.BSD
