/-
# One time evolution, one generator

The terminal Yang–Mills lane asks for the identification `H_Stone = H_YM`.
The cheapest normal form of that identification is *not* a comparison of two
independently manufactured operators, but the observation that a physical
system carries **one** time-evolution group and that a group determines its
generator.

This module proves that uniqueness in the bounded (norm-continuous) case, on
the nose:

* `eq_of_exp_smul_eq` — in any complete normed `ℝ`-algebra, two elements whose
  one-parameter exponential families agree are equal;
* `hamiltonian_eq_of_unitary_group_eq` — two bounded operators on a Hilbert
  space generating the same evolution `t ↦ e^{-itH}` are equal;
* `descend_hamiltonian_eq_of_unitary_group_eq` — the same conclusion transported
  to the physical null quotient of a semi-definite pairing.

The scope is stated honestly: this is the bounded-generator (norm-continuous
group) case, i.e. exactly the case in which the exponential series converges in
operator norm.  It is what a finite-lattice transfer operator supplies, and it
removes the need for a separate "compare two Hamiltonians" theorem there.  The
unbounded Stone case is *not* claimed here.
-/
import Mathlib
import RequestProject.YangMills.PhysicalNullQuotient

namespace RequestProject.YangMills.PhysicalTimeEvolutionGenerator

open NormedSpace
open RequestProject.YangMills.PhysicalNullQuotient
open scoped InnerProductSpace

/-- **Generator uniqueness.**  In a complete normed `ℝ`-algebra, the
one-parameter family `t ↦ exp (t • a)` determines `a`. -/
theorem eq_of_exp_smul_eq {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] {a b : A} (h : ∀ t : ℝ, exp (t • a) = exp (t • b)) :
    a = b := by
  have ha : HasDerivAt (fun t : ℝ => exp (t • a)) a 0 := by
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) a 0
  have hb : HasDerivAt (fun t : ℝ => exp (t • b)) b 0 := by
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) b 0
  exact ha.unique (by simpa only [h] using hb)

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The physical evolution `e^{-itH}` written as an exponential of a real
multiple of the skew-adjoint generator `-iH`. -/
theorem real_smul_neg_I_smul (H : E →L[ℂ] E) (t : ℝ) :
    (t : ℝ) • ((-Complex.I) • H) = (-(Complex.I * t)) • H := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  simp [mul_comm]

/-- **One evolution, one Hamiltonian.**  Two bounded operators generating the
same norm-continuous unitary group `t ↦ e^{-itH}` are the same operator.  In
particular a reconstructed (Stone) generator and a variational Yang–Mills
Hamiltonian implementing the same physical time translation need no separate
same-object theorem. -/
theorem hamiltonian_eq_of_unitary_group_eq {H₁ H₂ : E →L[ℂ] E}
    (h : ∀ t : ℝ, exp ((-(Complex.I * t)) • H₁) = exp ((-(Complex.I * t)) • H₂)) :
    H₁ = H₂ := by
  have key : ∀ t : ℝ, exp (t • ((-Complex.I) • H₁)) = exp (t • ((-Complex.I) • H₂)) := by
    intro t
    rw [real_smul_neg_I_smul, real_smul_neg_I_smul]
    exact h t
  have hAB : (-Complex.I) • H₁ = (-Complex.I) • H₂ := eq_of_exp_smul_eq key
  have hI : (-Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
  exact smul_right_injective (E →L[ℂ] E) hI hAB

end Hilbert

section Quotient

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Two Hamiltonians that implement the same physical evolution *weakly* — i.e.
have identical pairings against all test wavefunctions — descend to the same
operator on the physical null quotient.  This is the semi-definite counterpart
of `hamiltonian_eq_of_unitary_group_eq`: no definiteness of the measure is
assumed, only the pairing itself. -/
theorem descend_hamiltonian_eq_of_weak_eq {H₁ H₂ : E →ₗ[ℂ] E}
    (h₁ : PreservesNull H₁) (h₂ : PreservesNull H₂)
    (h : ∀ f φ : E, ⟪H₁ f, φ⟫_ℂ = ⟪H₂ f, φ⟫_ℂ) :
    descend H₁ h₁ = descend H₂ h₂ :=
  descend_congr_of_forall_inner_eq h₁ h₂ h

/-- Bounded Hamiltonians on a semi-definite carrier: weak equality of the two
generators is *equivalent* to equality of the descended physical operators. -/
theorem descend_eq_iff_weak_eq {H₁ H₂ : E →ₗ[ℂ] E}
    (h₁ : PreservesNull H₁) (h₂ : PreservesNull H₂) :
    descend H₁ h₁ = descend H₂ h₂ ↔ ∀ f φ : E, ⟪H₁ f, φ⟫_ℂ = ⟪H₂ f, φ⟫_ℂ := by
  constructor
  · intro hEq f φ
    have := congrArg (fun L => L (SeparationQuotient.mk f)) hEq
    simp only [descend_mk] at this
    have hnull : NullRel (H₁ f) (H₂ f) :=
      nullRel_iff_inseparable.mpr (SeparationQuotient.mk_eq_mk.mp this)
    exact forall_inner_eq_of_nullRel hnull φ
  · exact descend_hamiltonian_eq_of_weak_eq h₁ h₂

end Quotient

end RequestProject.YangMills.PhysicalTimeEvolutionGenerator
