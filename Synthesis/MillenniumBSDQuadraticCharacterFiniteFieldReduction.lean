import Synthesis.MillenniumBSDRationalQuadraticKummerInjective
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Tactic

/-!
# Continuous quadratic characters cut out finite Galois subextensions

For a continuous quadratic character of the absolute Galois group, the
kernel is the inverse image of the open singleton `{1}` in the discrete
two-element target.  Hence it is open; as a kernel it is normal.  Infinite
Galois correspondence then identifies its fixed field as a finite Galois
intermediate extension of `Qbar/Q`.

This lowers scalar Kummer surjectivity to the finite quadratic-extension
classification, without formalizing general Hilbert 90 or generic H¹.
-/

namespace Synthesis.Millennium.BSD

open Field MulAction Set

abbrev RationalQuadraticCharacter :=
  RationalAbsoluteGalois →ₜ* RationalQuadraticSign

def quadraticCharacterKernel
    (χ : RationalQuadraticCharacter) : Subgroup RationalAbsoluteGalois :=
  χ.toMonoidHom.ker

theorem quadraticCharacterKernel_isOpen
    (χ : RationalQuadraticCharacter) :
    IsOpen (quadraticCharacterKernel χ : Set RationalAbsoluteGalois) := by
  have hopen : IsOpen ({1} : Set RationalQuadraticSign) :=
    isOpen_singleton
  have hpre := hopen.preimage χ.continuous_toFun
  simpa [quadraticCharacterKernel, MonoidHom.mem_ker] using hpre

theorem quadraticCharacterKernel_normal
    (χ : RationalQuadraticCharacter) :
    (quadraticCharacterKernel χ).Normal := by
  exact MonoidHom.normal_ker χ.toMonoidHom

theorem quadraticCharacterKernel_isClosed
    (χ : RationalQuadraticCharacter) :
    IsClosed (quadraticCharacterKernel χ : Set RationalAbsoluteGalois) := by
  exact Subgroup.isClosed_of_isOpen _ (quadraticCharacterKernel_isOpen χ)

noncomputable def quadraticCharacterFixedField
    (χ : RationalQuadraticCharacter) :
    IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.fixedField (quadraticCharacterKernel χ)

noncomputable def quadraticCharacterClosedKernel
    (χ : RationalQuadraticCharacter) : ClosedSubgroup RationalAbsoluteGalois :=
  ⟨quadraticCharacterKernel χ, quadraticCharacterKernel_isClosed χ⟩

theorem quadraticCharacterFixedField_fixingSubgroup
    (χ : RationalQuadraticCharacter) :
    (quadraticCharacterFixedField χ).fixingSubgroup =
      quadraticCharacterKernel χ := by
  simpa [quadraticCharacterFixedField, quadraticCharacterClosedKernel] using
    (InfiniteGalois.fixingSubgroup_fixedField
      (quadraticCharacterClosedKernel χ))

theorem quadraticCharacterFixedField_finiteDimensional
    (χ : RationalQuadraticCharacter) :
    FiniteDimensional ℚ (quadraticCharacterFixedField χ) := by
  have hopen :
      IsOpen ((quadraticCharacterFixedField χ).fixingSubgroup.carrier) := by
    rw [quadraticCharacterFixedField_fixingSubgroup χ]
    exact quadraticCharacterKernel_isOpen χ
  exact (InfiniteGalois.isOpen_iff_finite
    (quadraticCharacterFixedField χ)).mp hopen

theorem quadraticCharacterFixedField_isGalois
    (χ : RationalQuadraticCharacter) :
    IsGalois ℚ (quadraticCharacterFixedField χ) := by
  have hnormal :
      (quadraticCharacterFixedField χ).fixingSubgroup.Normal := by
    rw [quadraticCharacterFixedField_fixingSubgroup χ]
    exact quadraticCharacterKernel_normal χ
  exact (InfiniteGalois.normal_iff_isGalois
    (quadraticCharacterFixedField χ)).mp hnormal

theorem quadraticCharacterFixedField_finite_and_galois
    (χ : RationalQuadraticCharacter) :
    FiniteDimensional ℚ (quadraticCharacterFixedField χ) ∧
      IsGalois ℚ (quadraticCharacterFixedField χ) :=
  ⟨quadraticCharacterFixedField_finiteDimensional χ,
    quadraticCharacterFixedField_isGalois χ⟩

/--
The exact remaining finite producer for scalar Kummer surjectivity: every
nontrivial finite Galois subextension cut out by a C₂-character is generated
by a square root of a nonzero rational.
-/
def QuadraticCharacterFixedFieldSquareRootClassification : Prop :=
  ∀ χ : RationalQuadraticCharacter, χ ≠ 1 →
    ∃ a : NonzeroRat,
      quadraticCharacterKernel χ =
        quadraticCharacterKernel (rationalQuadraticKummerCharacter a)

theorem rationalQuadraticKummerSurjective_of_fixedFieldClassification
    (hclass : QuadraticCharacterFixedFieldSquareRootClassification) :
    RationalQuadraticKummerSurjectivity := by
  intro χ
  by_cases hχ : χ = 1
  · refine ⟨1, ?_⟩
    rw [hχ, map_one]
  · rcases hclass χ hχ with ⟨a,hker⟩
    refine ⟨mathlibSquareClassOf a, ?_⟩
    have htarget := rationalSquareClassKummerHom_mk a
    rw [htarget]
    apply ContinuousMonoidHom.ext
    intro σ
    -- Two C₂-valued homomorphisms are determined by their kernels.
    by_cases hσ : σ ∈ quadraticCharacterKernel χ
    · have hσ' : σ ∈ quadraticCharacterKernel
          (rationalQuadraticKummerCharacter a) := by simpa [hker] using hσ
      simp [quadraticCharacterKernel, MonoidHom.mem_ker] at hσ hσ'
      simpa [hσ,hσ']
    · have hσ' : σ ∉ quadraticCharacterKernel
          (rationalQuadraticKummerCharacter a) := by
        simpa [hker] using hσ
      have hx : χ σ ≠ 1 := by
        simpa [quadraticCharacterKernel, MonoidHom.mem_ker] using hσ
      have hy : rationalQuadraticKummerCharacter a σ ≠ 1 := by
        simpa [quadraticCharacterKernel, MonoidHom.mem_ker] using hσ'
      -- The multiplicative Z/2 target has only two elements.
      fin_cases χ σ <;> fin_cases rationalQuadraticKummerCharacter a σ <;>
        simp_all

end Synthesis.Millennium.BSD
