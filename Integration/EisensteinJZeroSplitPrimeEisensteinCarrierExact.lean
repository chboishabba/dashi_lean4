import Integration.EisensteinJZeroSplitJacobiCyclotomicExact
import Integration.EisensteinQuadraticAlgebraExact
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# Literal split-prime Jacobi -> EisensteinQA carrier weld

This file removes the remaining carrier ambiguity in the split local branch.
The complex sixth-cyclotomic order is connected to the repository's literal
`EisensteinQA := QuadraticAlgebra Int (-1) (-1)` by the explicit generator

    omega_C = zeta_6 - 1,

which satisfies `omega_C^2 + omega_C + 1 = 0`.

We prove the corresponding quadratic-algebra embedding is injective and its
range is exactly `Z[omega_C]`.  Since `Z[zeta_6] = Z[omega_C]`, the canonical
split Jacobi sum can therefore be pulled back to an ACTUAL `EisensteinQA`
element.  Conjugation compatibility then transports the already-proved
complex norm-p theorem to the literal quadratic-algebra norm.

Finally the two-term Jacobi trace compiler collapses to the quadratic trace of
that same element.  For the resulting `z = a+b*omega`:

    N(z) = a^2-a*b+b^2 = p,
    a_p  = -(2*a-b),

and hence the split local Euler polynomial is

    1 + (2*a-b) T + p T^2.

Attribution: Mathlib owns `QuadraticAlgebra.lift`, primitive-root and complex
conjugation infrastructure, and the Jacobi theorems consumed upstream.
DASHI/Lean owns this explicit carrier specialization/composition and the
same-prime weld.  No Hecke/Groessencharacter or global elliptic L-function is
inferred here.
-/

namespace Integration.EisensteinJZeroSplitPrimeEisensteinCarrierExact

open scoped BigOperators ComplexConjugate
open Dashi.EisensteinQuadraticAlgebraExact
open Integration.EisensteinJZeroFiniteFieldTraceExact
open Integration.EisensteinJZeroCubicJacobiExact
open Integration.EisensteinJZeroCanonicalCubicCharacterExact
open Integration.EisensteinJZeroSplitJacobiCyclotomicExact

------------------------------------------------------------------------
-- The explicit complex Eisenstein generator.
------------------------------------------------------------------------

/-- `zeta_6 - 1`, a primitive cubic root satisfying the Eisenstein relation. -/
noncomputable def omegaComplex : ℂ := sixthRoot - 1

private theorem sixthRoot_pow_three_eq_neg_one : sixthRoot ^ 3 = -1 := by
  have h6 := sixthRoot_isPrimitive
  have h3ne : sixthRoot ^ 3 ≠ 1 :=
    h6.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hsq : (sixthRoot ^ 3) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
    exact h6.pow_eq_one
  exact (sq_eq_one_iff.mp hsq).resolve_left h3ne

private theorem sixthRoot_quadratic :
    sixthRoot ^ 2 - sixthRoot + 1 = 0 := by
  have hzneg : sixthRoot ≠ -1 := by
    intro h
    have h2 : sixthRoot ^ 2 = 1 := by simp [h]
    exact (sixthRoot_isPrimitive.pow_ne_one_of_pos_of_lt
      (by norm_num) (by norm_num)) h2
  have hfac :
      (sixthRoot + 1) * (sixthRoot ^ 2 - sixthRoot + 1) = 0 := by
    calc
      (sixthRoot + 1) * (sixthRoot ^ 2 - sixthRoot + 1)
          = sixthRoot ^ 3 + 1 := by ring
      _ = 0 := by rw [sixthRoot_pow_three_eq_neg_one]; ring
  exact (mul_eq_zero.mp hfac).resolve_left (add_ne_zero.mpr hzneg)

/-- The concrete generator satisfies `omega^2 = -1-omega`. -/
theorem omegaComplex_square : omegaComplex ^ 2 = -1 - omegaComplex := by
  unfold omegaComplex
  have h := sixthRoot_quadratic
  ring_nf at h ⊢
  linear_combination h

private theorem sixthRoot_ne_zero : sixthRoot ≠ 0 := by
  exact sixthRoot_isPrimitive.ne_zero

private theorem sixthRoot_conj : Complex.conj sixthRoot = 1 - sixthRoot := by
  have hnorm : ‖sixthRoot‖ = 1 :=
    sixthRoot_isPrimitive.norm'_eq_one (by norm_num)
  have hinvconj : sixthRoot⁻¹ = Complex.conj sixthRoot :=
    Complex.inv_eq_conj hnorm
  have hmul : sixthRoot * (1 - sixthRoot) = 1 := by
    have hq := sixthRoot_quadratic
    calc
      sixthRoot * (1 - sixthRoot) = sixthRoot - sixthRoot ^ 2 := by ring
      _ = 1 := by linear_combination -hq
  have hinv : sixthRoot⁻¹ = 1 - sixthRoot :=
    (mul_eq_one_iff_inv_eq₀ sixthRoot_ne_zero).mp hmul
  rw [← hinvconj, hinv]

/-- Complex conjugation is exactly the Eisenstein quadratic involution on the
chosen generator. -/
theorem omegaComplex_conj :
    Complex.conj omegaComplex = -1 - omegaComplex := by
  unfold omegaComplex
  rw [map_sub, sixthRoot_conj, map_one]
  ring

------------------------------------------------------------------------
-- Explicit quadratic-algebra embedding and injectivity.
------------------------------------------------------------------------

private theorem omegaComplex_lift_relation :
    omegaComplex * omegaComplex =
      (-1 : Int) • (1 : ℂ) + (-1 : Int) • omegaComplex := by
  rw [← pow_two, omegaComplex_square]
  norm_num

/-- The literal repo Eisenstein carrier embedded into the complex cyclotomic
model by `omega -> zeta_6-1`. -/
noncomputable def eisensteinComplexEmbedding : EisensteinQA →ₐ[Int] ℂ :=
  QuadraticAlgebra.lift ⟨omegaComplex, omegaComplex_lift_relation⟩

private theorem eisenstein_int_norm_zero
    {s t : Int} (h : s * s - s * t + t * t = 0) :
    s = 0 ∧ t = 0 := by
  have ht2 : t * t = 0 := by
    nlinarith [sq_nonneg (2 * s - t), sq_nonneg t]
  have ht : t = 0 := mul_self_eq_zero.mp ht2
  subst t
  have hs2 : s * s = 0 := by simpa using h
  exact ⟨mul_self_eq_zero.mp hs2, rfl⟩

private theorem one_omegaComplex_linearIndependent :
    LinearIndependent Int ![(1 : ℂ), omegaComplex] := by
  rw [LinearIndependent.pair_iff]
  intro s t hlin
  have hlin' : (s : ℂ) + (t : ℂ) * omegaComplex = 0 := by
    simpa [Algebra.smul_def] using hlin
  have hnormC :
      ((s * s - s * t + t * t : Int) : ℂ) = 0 := by
    calc
      ((s * s - s * t + t * t : Int) : ℂ)
          = ((s : ℂ) + (t : ℂ) * omegaComplex) *
              ((s : ℂ) + (t : ℂ) * Complex.conj omegaComplex) := by
                push_cast
                rw [omegaComplex_conj]
                ring
      _ = 0 := by rw [hlin']; simp
  have hnormI : s * s - s * t + t * t = 0 := by
    exact_mod_cast hnormC
  exact eisenstein_int_norm_zero hnormI

/-- The complex cyclotomic model is faithful on the literal EisensteinQA
carrier. -/
theorem eisensteinComplexEmbedding_injective :
    Function.Injective eisensteinComplexEmbedding := by
  rw [QuadraticAlgebra.lift_injective_iff omegaComplex_lift_relation]
  exact one_omegaComplex_linearIndependent

/-- The image order of the faithful Eisenstein embedding. -/
abbrev EisensteinComplexOrder : Subalgebra Int ℂ :=
  eisensteinComplexEmbedding.range

/-- The literal repo carrier is algebra-equivalent to its complex image order. -/
noncomputable def eisensteinQAEquivComplexOrder :
    EisensteinQA ≃ₐ[Int] EisensteinComplexOrder :=
  AlgEquiv.ofInjective eisensteinComplexEmbedding
    eisensteinComplexEmbedding_injective

/-- Its image is exactly the order generated by `omegaComplex`. -/
theorem eisensteinComplexEmbedding_range :
    eisensteinComplexEmbedding.range =
      Algebra.adjoin Int ({omegaComplex} : Set ℂ) := by
  simpa [eisensteinComplexEmbedding] using
    (QuadraticAlgebra.range_lift omegaComplex_lift_relation)

/-- `zeta_6` and `omega=zeta_6-1` generate the same integral complex order. -/
theorem sixthCyclotomicOrder_eq_eisensteinComplexOrder :
    Algebra.adjoin Int ({sixthRoot} : Set ℂ) =
      Algebra.adjoin Int ({omegaComplex} : Set ℂ) := by
  apply le_antisymm
  · apply Algebra.adjoin_le.2
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    have hu := Algebra.self_mem_adjoin_singleton Int omegaComplex
    have h1 : (1 : ℂ) ∈ Algebra.adjoin Int ({omegaComplex} : Set ℂ) :=
      (Algebra.adjoin Int ({omegaComplex} : Set ℂ)).one_mem
    have : omegaComplex + 1 ∈ Algebra.adjoin Int ({omegaComplex} : Set ℂ) :=
      (Algebra.adjoin Int ({omegaComplex} : Set ℂ)).add_mem hu h1
    simpa [omegaComplex] using this
  · apply Algebra.adjoin_le.2
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    have hu := Algebra.self_mem_adjoin_singleton Int sixthRoot
    have h1 : (1 : ℂ) ∈ Algebra.adjoin Int ({sixthRoot} : Set ℂ) :=
      (Algebra.adjoin Int ({sixthRoot} : Set ℂ)).one_mem
    exact (Algebra.adjoin Int ({sixthRoot} : Set ℂ)).sub_mem hu h1

------------------------------------------------------------------------
-- Pull the canonical split Jacobi sum into literal EisensteinQA.
------------------------------------------------------------------------

private theorem splitJacobiSum_mem_embeddingRange
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    splitJacobiSum p hp3 ∈ eisensteinComplexEmbedding.range := by
  rw [eisensteinComplexEmbedding_range]
  rw [← sixthCyclotomicOrder_eq_eisensteinComplexOrder]
  exact splitJacobiSum_mem_sixthCyclotomicOrder p hp2 hp3

/-- The canonical split Jacobi sum, pulled back to the ACTUAL repository
Eisenstein quadratic-algebra carrier. -/
noncomputable def splitJacobiEisensteinElement
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    EisensteinQA :=
  eisensteinQAEquivComplexOrder.symm
    ⟨splitJacobiSum p hp3, splitJacobiSum_mem_embeddingRange p hp2 hp3⟩

/-- Pullback is exact, not merely up to norm or associates. -/
theorem eisensteinComplexEmbedding_splitJacobiEisensteinElement
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    eisensteinComplexEmbedding (splitJacobiEisensteinElement p hp2 hp3) =
      splitJacobiSum p hp3 := by
  change ((eisensteinQAEquivComplexOrder
    (splitJacobiEisensteinElement p hp2 hp3) : EisensteinComplexOrder) : ℂ) = _
  simp [splitJacobiEisensteinElement]

------------------------------------------------------------------------
-- Quadratic involution = complex conjugation and norm transport.
------------------------------------------------------------------------

/-- The explicit embedding intertwines the quadratic involution with complex
conjugation. -/
theorem eisensteinComplexEmbedding_star (z : EisensteinQA) :
    eisensteinComplexEmbedding (star z) =
      Complex.conj (eisensteinComplexEmbedding z) := by
  simp only [eisensteinComplexEmbedding, QuadraticAlgebra.lift_apply_apply,
    QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  rw [map_add, map_mul, map_neg, map_one, omegaComplex_conj]
  push_cast
  ring

private theorem embedding_norm_identity (z : EisensteinQA) :
    ((QuadraticAlgebra.norm z : Int) : ℂ) =
      eisensteinComplexEmbedding z *
        Complex.conj (eisensteinComplexEmbedding z) := by
  have h := QuadraticAlgebra.algebraMap_norm_eq_mul_star z
  have hm := congrArg eisensteinComplexEmbedding h
  simpa [map_mul, eisensteinComplexEmbedding_star] using hm

/-- The canonical Jacobi pullback has the literal repo Eisenstein norm `p`. -/
theorem splitJacobiEisensteinElement_norm
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    QuadraticAlgebra.norm (splitJacobiEisensteinElement p hp2 hp3) = p := by
  let z := splitJacobiEisensteinElement p hp2 hp3
  have hnorm := embedding_norm_identity z
  rw [eisensteinComplexEmbedding_splitJacobiEisensteinElement p hp2 hp3] at hnorm
  rw [splitJacobiSum_mul_conj p hp2 hp3] at hnorm
  exact_mod_cast hnorm

------------------------------------------------------------------------
-- Collapse the Jacobi trace to the Eisenstein quadratic trace.
------------------------------------------------------------------------

private theorem quadraticCharComplex_self_inverse
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) :
    (quadraticCharComplex : MulChar (ZMod p) ℂ)⁻¹ = quadraticCharComplex := by
  let χ := (quadraticCharComplex : MulChar (ZMod p) ℂ)
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have hsq : χ ^ 2 = 1 := by
    ext u
    have hu0 : (u : ZMod p) ≠ 0 := Units.ne_zero u
    have hs := quadraticChar_sq_one (F := ZMod p) hu0
    have hsc := congrArg (fun z : Int => (z : ℂ)) hs
    simpa [χ, MulChar.pow_apply_coe, quadraticCharComplex_apply,
      MulChar.one_apply_coe] using hsc
  have hmul : χ * χ = 1 := by simpa [pow_two] using hsq
  exact (mul_eq_one_iff_eq_inv.mp hmul).symm

private theorem splitCubic_square_eq_inverse
    (p : Nat) [Fact p.Prime] (hp3 : p % 3 = 1) :
    splitCubicCharacter p hp3 * splitCubicCharacter p hp3 =
      (splitCubicCharacter p hp3)⁻¹ := by
  have h3 : splitCubicCharacter p hp3 ^ 3 = 1 := by
    change canonicalCubicCharacter
      (F := ZMod p) (by simpa [ZMod.card] using hp3) ^ 3 = 1
    exact canonicalCubicCharacter_pow_three
      (F := ZMod p) (by simpa [ZMod.card] using hp3)
  have hmul :
      (splitCubicCharacter p hp3 * splitCubicCharacter p hp3) *
        splitCubicCharacter p hp3 = 1 := by
    simpa [pow_succ, pow_two, mul_assoc] using h3
  exact mul_eq_one_iff_eq_inv.mp hmul

private theorem splitCubic_at_neg_one
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    splitCubicCharacter p hp3 (-1) = 1 := by
  have hm1 : (-1 : ZMod p) ≠ 0 := by
    simpa using (one_ne_zero : (1 : ZMod p) ≠ 0)
  change canonicalCubicCharacter
      (F := ZMod p) (by simpa [ZMod.card] using hp3) (-1) = 1
  apply (canonicalCubicCharacter_eq_one_iff_cube
    (F := ZMod p) (by simpa [ZMod.card] using hp3) hm1).2
  exact ⟨-1, by ring⟩

private theorem splitCubicSq_at_neg_one
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    (splitCubicCharacter p hp3 * splitCubicCharacter p hp3) (-1) = 1 := by
  rw [MulChar.mul_apply, splitCubic_at_neg_one p hp2 hp3]
  simp

private theorem second_splitJacobi_is_conj
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    jacobiSum (splitCubicCharacter p hp3 * splitCubicCharacter p hp3)
        (quadraticCharComplex : MulChar (ZMod p) ℂ)
      = Complex.conj (splitJacobiSum p hp3) := by
  rw [splitCubic_square_eq_inverse p hp3,
    ← quadraticCharComplex_self_inverse p hp2]
  symm
  exact conj_jacobiSum_eq_inv
    (splitCubicCharacter p hp3)
    (quadraticCharComplex : MulChar (ZMod p) ℂ)

private theorem jZeroTrace_cast_eq_neg_splitJacobi_trace
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    ((jZeroFrobeniusTraceInt (ZMod p) : Int) : ℂ) =
      -(splitJacobiSum p hp3 + Complex.conj (splitJacobiSum p hp3)) := by
  let cert := splitCertificate p hp3
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have hcompile := jZeroTrace_cast_eq_cubicJacobiTrace
    (F := ZMod p) hchar cert
  rw [hcompile]
  unfold cubicJacobiTrace
  change
    -(splitCubicCharacter p hp3 (-1) * splitJacobiSum p hp3 +
      (splitCubicCharacter p hp3 * splitCubicCharacter p hp3) (-1) *
        jacobiSum (splitCubicCharacter p hp3 * splitCubicCharacter p hp3)
          (quadraticCharComplex : MulChar (ZMod p) ℂ)) = _
  rw [splitCubic_at_neg_one p hp2 hp3,
    splitCubicSq_at_neg_one p hp2 hp3,
    second_splitJacobi_is_conj p hp2 hp3]
  ring

private theorem embedding_add_conj_eq_trace (z : EisensteinQA) :
    eisensteinComplexEmbedding z + Complex.conj (eisensteinComplexEmbedding z) =
      ((2 * z.re - z.im : Int) : ℂ) := by
  rw [← eisensteinComplexEmbedding_star]
  simp only [eisensteinComplexEmbedding, QuadraticAlgebra.lift_apply_apply,
    QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  push_cast
  ring

/-- Closed split-prime Frobenius trace on the literal EisensteinQA Jacobi
pullback. -/
theorem splitPrime_jZero_trace_formula
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    jZeroFrobeniusTraceInt (ZMod p) =
      -(2 * (splitJacobiEisensteinElement p hp2 hp3).re
        - (splitJacobiEisensteinElement p hp2 hp3).im) := by
  let z := splitJacobiEisensteinElement p hp2 hp3
  have ht := jZeroTrace_cast_eq_neg_splitJacobi_trace p hp2 hp3
  have htrace := embedding_add_conj_eq_trace z
  rw [eisensteinComplexEmbedding_splitJacobiEisensteinElement p hp2 hp3] at htrace
  rw [htrace] at ht
  exact_mod_cast ht

------------------------------------------------------------------------
-- Split local Euler polynomial.
------------------------------------------------------------------------

/-- Same-curve split local Euler polynomial in the variable `T`. -/
def splitPrimeLocalEulerPolynomial
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) : Int → Int :=
  fun T => 1 - jZeroFrobeniusTraceInt (ZMod p) * T + p * T ^ 2

/-- Literal coordinate form of the split local factor. -/
theorem splitPrimeLocalEulerPolynomial_formula
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    splitPrimeLocalEulerPolynomial p hp2 hp3 =
      fun T => 1 +
        (2 * (splitJacobiEisensteinElement p hp2 hp3).re
          - (splitJacobiEisensteinElement p hp2 hp3).im) * T + p * T ^ 2 := by
  funext T
  simp only [splitPrimeLocalEulerPolynomial,
    splitPrime_jZero_trace_formula p hp2 hp3]
  ring

------------------------------------------------------------------------
-- Terminal source boundary.
------------------------------------------------------------------------

structure SplitPrimeEisensteinCarrierBoundary where
  explicitEisensteinComplexEmbeddingPaid : Bool := true
  embeddingInjectivePaid : Bool := true
  sixthCyclotomicOrderEqualsComplexEisensteinOrderPaid : Bool := true
  splitJacobiPulledBackToLiteralEisensteinQAPaid : Bool := true
  splitJacobiLiteralNormEqualsPrimePaid : Bool := true
  splitPrimeFrobeniusCoordinateFormulaPaid : Bool := true
  splitPrimeLocalEulerPolynomialPaid : Bool := true
  canonicalAssociateToPreexistingSplitWitnessPaid : Bool := false
  canonicalUnitNormalizationPaid : Bool := false
  heckeGroessencharacterPaid : Bool := false
  globalEllipticLFunctionPaid : Bool := false

/-- Machine-readable boundary for the now-closed split local branch. -/
def canonicalBoundary : SplitPrimeEisensteinCarrierBoundary := {}

end Integration.EisensteinJZeroSplitPrimeEisensteinCarrierExact
