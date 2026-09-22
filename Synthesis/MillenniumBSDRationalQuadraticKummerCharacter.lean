import Synthesis.MillenniumBSDRatSquareClassMathlibWeld
import Synthesis.MillenniumBSDSelmerShaCohomologicalBoundary
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Tactic

/-!
# Continuous quadratic Kummer character for a fixed rational representative

For each nonzero rational `a`, choose a square root `r` of its image in
`AlgebraicClosure ℚ`. Every absolute-Galois automorphism sends `r` to `±r`.
We record the sign as an element of `ZMod 2`; composition of automorphisms
adds the signs, so after `Multiplicative` this is a monoid homomorphism.

The zero fibre is the stabilizer of `r`.  Krull topology makes stabilizers of
algebraic elements open; as an open subgroup it is clopen.  Hence the sign
map is locally constant and therefore continuous.

This file intentionally stops before quotient descent.  Remaining known math:
independence of the chosen root, invariance under multiplying `a` by a square,
and then injectivity/surjectivity (the continuous Kummer/Hilbert-90 theorem).
-/

namespace Synthesis.Millennium.BSD

open Field MulAction Set

abbrev RationalQuadraticSign := Multiplicative (ZMod 2)

noncomputable def rationalKummerRoot (a : NonzeroRat) : AlgebraicClosure ℚ :=
  Classical.choose
    (IsAlgClosed.exists_eq_mul_self
      (algebraMap ℚ (AlgebraicClosure ℚ) a.1))

theorem rationalKummerRoot_spec (a : NonzeroRat) :
    rationalKummerRoot a * rationalKummerRoot a =
      algebraMap ℚ (AlgebraicClosure ℚ) a.1 := by
  exact (Classical.choose_spec
    (IsAlgClosed.exists_eq_mul_self
      (algebraMap ℚ (AlgebraicClosure ℚ) a.1))).symm

theorem rationalKummerRoot_ne_zero (a : NonzeroRat) :
    rationalKummerRoot a ≠ 0 := by
  intro h
  have hs := rationalKummerRoot_spec a
  rw [h, zero_mul] at hs
  have : a.1 = 0 := by
    exact (FaithfulSMul.algebraMap_injective ℚ (AlgebraicClosure ℚ)) hs.symm
  exact a.2 this

theorem galois_kummerRoot_eq_or_neg
    (a : NonzeroRat) (σ : RationalAbsoluteGalois) :
    σ (rationalKummerRoot a) = rationalKummerRoot a ∨
      σ (rationalKummerRoot a) = - rationalKummerRoot a := by
  apply mul_self_eq_mul_self_iff.mp
  have hs := congrArg σ (rationalKummerRoot_spec a)
  simpa [map_mul] using hs.trans (rationalKummerRoot_spec a).symm

noncomputable def rationalKummerBit
    (a : NonzeroRat) (σ : RationalAbsoluteGalois) : ZMod 2 :=
  if σ (rationalKummerRoot a) = rationalKummerRoot a then 0 else 1

@[simp] theorem rationalKummerBit_eq_zero_iff
    (a : NonzeroRat) (σ : RationalAbsoluteGalois) :
    rationalKummerBit a σ = 0 ↔
      σ (rationalKummerRoot a) = rationalKummerRoot a := by
  by_cases h : σ (rationalKummerRoot a) = rationalKummerRoot a
  · simp [rationalKummerBit, h]
  · simp [rationalKummerBit, h]

@[simp] theorem rationalKummerBit_eq_one_iff
    (a : NonzeroRat) (σ : RationalAbsoluteGalois) :
    rationalKummerBit a σ = 1 ↔
      σ (rationalKummerRoot a) = - rationalKummerRoot a := by
  rcases galois_kummerRoot_eq_or_neg a σ with h | h
  · have hn : rationalKummerBit a σ = 0 := by
      simp [rationalKummerBit, h]
    rw [hn]
    constructor
    · norm_num
    · intro hr
      have hself : -rationalKummerRoot a = rationalKummerRoot a := by
        simpa [h] using hr.symm
      exact (rationalKummerRoot_ne_zero a)
        ((CharZero.neg_eq_self_iff).mp hself)
  · have hne : σ (rationalKummerRoot a) ≠ rationalKummerRoot a := by
      rw [h]
      intro hself
      exact (rationalKummerRoot_ne_zero a)
        ((CharZero.neg_eq_self_iff).mp hself)
    simp [rationalKummerBit, hne, h]

theorem rationalKummerBit_one
    (a : NonzeroRat) : rationalKummerBit a 1 = 0 := by
  simp [rationalKummerBit]

theorem rationalKummerBit_mul
    (a : NonzeroRat) (σ τ : RationalAbsoluteGalois) :
    rationalKummerBit a (σ * τ) =
      rationalKummerBit a σ + rationalKummerBit a τ := by
  rcases galois_kummerRoot_eq_or_neg a σ with hσ | hσ <;>
  rcases galois_kummerRoot_eq_or_neg a τ with hτ | hτ
  · have hστ : (σ * τ) (rationalKummerRoot a) = rationalKummerRoot a := by
      simp only [AlgEquiv.mul_apply, hτ, hσ]
    simp [rationalKummerBit, hσ, hτ, hστ]
  · have hστ : (σ * τ) (rationalKummerRoot a) = -rationalKummerRoot a := by
      simp only [AlgEquiv.mul_apply, hτ, map_neg, hσ]
    have hσn : σ (rationalKummerRoot a) = rationalKummerRoot a := hσ
    have hτn : τ (rationalKummerRoot a) ≠ rationalKummerRoot a := by
      rw [hτ]
      intro hs
      exact rationalKummerRoot_ne_zero a ((CharZero.neg_eq_self_iff).mp hs)
    have hστn : (σ * τ) (rationalKummerRoot a) ≠ rationalKummerRoot a := by
      rw [hστ]
      intro hs
      exact rationalKummerRoot_ne_zero a ((CharZero.neg_eq_self_iff).mp hs)
    simp [rationalKummerBit, hσn, hτn, hστn]
  · have hστ : (σ * τ) (rationalKummerRoot a) = -rationalKummerRoot a := by
      simp only [AlgEquiv.mul_apply, hτ, hσ]
    have hσn : σ (rationalKummerRoot a) ≠ rationalKummerRoot a := by
      rw [hσ]
      intro hs
      exact rationalKummerRoot_ne_zero a ((CharZero.neg_eq_self_iff).mp hs)
    have hτp : τ (rationalKummerRoot a) = rationalKummerRoot a := hτ
    have hστn : (σ * τ) (rationalKummerRoot a) ≠ rationalKummerRoot a := by
      rw [hστ]
      intro hs
      exact rationalKummerRoot_ne_zero a ((CharZero.neg_eq_self_iff).mp hs)
    simp [rationalKummerBit, hσn, hτp, hστn]
  · have hστ : (σ * τ) (rationalKummerRoot a) = rationalKummerRoot a := by
      simp only [AlgEquiv.mul_apply, hτ, map_neg, hσ, neg_neg]
    have hσn : σ (rationalKummerRoot a) ≠ rationalKummerRoot a := by
      rw [hσ]
      intro hs
      exact rationalKummerRoot_ne_zero a ((CharZero.neg_eq_self_iff).mp hs)
    have hτn : τ (rationalKummerRoot a) ≠ rationalKummerRoot a := by
      rw [hτ]
      intro hs
      exact rationalKummerRoot_ne_zero a ((CharZero.neg_eq_self_iff).mp hs)
    simp [rationalKummerBit, hσn, hτn, hστ]

theorem rationalKummerBit_isLocallyConstant (a : NonzeroRat) :
    IsLocallyConstant (rationalKummerBit a) := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro y
  fin_cases y
  · have hopen : IsOpen
        (MulAction.stabilizer RationalAbsoluteGalois
          (rationalKummerRoot a) : Set RationalAbsoluteGalois) :=
      stabilizer_isOpen_of_isIntegral
        ℚ (AlgebraicClosure ℚ) (rationalKummerRoot a)
    simpa [MulAction.mem_stabilizer_iff, rationalKummerBit_eq_zero_iff] using hopen
  · have hopen : IsOpen
        (MulAction.stabilizer RationalAbsoluteGalois
          (rationalKummerRoot a) : Set RationalAbsoluteGalois) :=
      stabilizer_isOpen_of_isIntegral
        ℚ (AlgebraicClosure ℚ) (rationalKummerRoot a)
    have hclosed : IsClosed
        (MulAction.stabilizer RationalAbsoluteGalois
          (rationalKummerRoot a) : Set RationalAbsoluteGalois) :=
      Subgroup.isClosed_of_isOpen hopen
    have hcomp : IsOpen
        ((MulAction.stabilizer RationalAbsoluteGalois
          (rationalKummerRoot a) : Set RationalAbsoluteGalois)ᶜ) :=
      hclosed.isOpen_compl
    convert hcomp using 1
    ext σ
    simp [MulAction.mem_stabilizer_iff, rationalKummerBit_eq_one_iff,
      galois_kummerRoot_eq_or_neg, rationalKummerRoot_ne_zero]

theorem rationalKummerBit_continuous (a : NonzeroRat) :
    Continuous (rationalKummerBit a) :=
  (rationalKummerBit_isLocallyConstant a).continuous

noncomputable def rationalQuadraticKummerCharacter
    (a : NonzeroRat) :
    RationalAbsoluteGalois →ₜ* RationalQuadraticSign where
  toFun σ := Multiplicative.ofAdd (rationalKummerBit a σ)
  map_one' := by
    apply Multiplicative.toAdd_injective
    simpa using rationalKummerBit_one a
  map_mul' σ τ := by
    apply Multiplicative.toAdd_injective
    simpa using rationalKummerBit_mul a σ τ
  continuous_toFun := by
    exact rationalKummerBit_continuous a

@[simp] theorem rationalQuadraticKummerCharacter_apply
    (a : NonzeroRat) (σ : RationalAbsoluteGalois) :
    Multiplicative.toAdd (rationalQuadraticKummerCharacter a σ) =
      rationalKummerBit a σ := rfl

/-- Exact next descent seam: descend the representative character to square classes. -/
def RationalQuadraticKummerCharacterDescent : Prop :=
  ∃ κ : MathlibRatSquareClass →
      (RationalAbsoluteGalois →ₜ* RationalQuadraticSign),
    ∀ a : NonzeroRat,
      κ (explicitToMathlibSquareClass a) =
        rationalQuadraticKummerCharacter a

end Synthesis.Millennium.BSD
