import Integration.EisensteinJZeroMixedJacobiNormExact
import Integration.EisensteinQuadraticAlgebraExact
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Integral Eisenstein-valued Jacobi sum for the split j=0 branch

The preceding owners prove the split-prime elliptic trace as an unweighted
pair of complex Jacobi sums and prove the mixed Jacobi norm is the same prime.
This owner removes the remaining "complex number might not be integral"
ambiguity by constructing the cubic character directly with values in the
repository's literal `EisensteinQA = Z[ω]` carrier.

For every prime `p ≡ 1 (mod 3)` we construct an integral Jacobi element `J_p`
and prove

  N(J_p)  = p,
  Tr(J_p) = -a_p,

where `a_p` is the same j=0 Frobenius trace already owned by the finite-field
lane.

Attribution: Mathlib owns `QuadraticAlgebra`, generic multiplicative
characters, roots of unity and Jacobi sums.  DASHI/Lean owns this specialization
and same-object composition.  No external theorem is treated as a proof term.
No primary-associate identification, Hecke character, or global elliptic
L-series equality is claimed here.
-/

namespace Integration.EisensteinJZeroIntegralJacobiExact

open scoped BigOperators ComplexConjugate
open Finset
open Dashi.EisensteinQuadraticAlgebraExact
open Integration.EisensteinJZeroFiniteFieldTraceExact
open Integration.EisensteinJZeroCubicJacobiExact
open Integration.EisensteinJZeroCubicCharacterCertificateExact
open Integration.EisensteinJZeroCubicCharacterExistenceExact

------------------------------------------------------------------------
-- The integral Eisenstein cube root.
------------------------------------------------------------------------

private theorem eisensteinOmega_ne_one :
    (QuadraticAlgebra.omega : EisensteinQA) ≠ 1 := by
  intro h
  have hi := congrArg QuadraticAlgebra.im h
  norm_num at hi

private theorem eisensteinOmega_sq_ne_one :
    (QuadraticAlgebra.omega : EisensteinQA) ^ 2 ≠ 1 := by
  intro h
  rw [Dashi.EisensteinQuadraticAlgebraExact.omega_square_relation] at h
  have hi := congrArg QuadraticAlgebra.im h
  norm_num at hi

private theorem eisensteinOmega_cube :
    (QuadraticAlgebra.omega : EisensteinQA) ^ 3 = 1 := by
  calc
    (QuadraticAlgebra.omega : EisensteinQA) ^ 3
        = QuadraticAlgebra.omega ^ 2 * QuadraticAlgebra.omega := by ring
    _ = (-(1 : EisensteinQA) - QuadraticAlgebra.omega) * QuadraticAlgebra.omega := by
          rw [Dashi.EisensteinQuadraticAlgebraExact.omega_square_relation]
    _ = -QuadraticAlgebra.omega - QuadraticAlgebra.omega ^ 2 := by ring
    _ = 1 := by
      rw [Dashi.EisensteinQuadraticAlgebraExact.omega_square_relation]
      ring

/-- The repository's integral generator is a primitive third root of unity. -/
theorem eisensteinOmega_isPrimitiveRoot_three :
    IsPrimitiveRoot (QuadraticAlgebra.omega : EisensteinQA) 3 := by
  refine ⟨eisensteinOmega_cube, ?_⟩
  intro n hn
  rw [← Nat.mod_add_div n 3, pow_add, pow_mul, eisensteinOmega_cube,
    one_pow, mul_one] at hn
  have hr : n % 3 < 3 := Nat.mod_lt n (by norm_num)
  interval_cases hrem : n % 3
  · exact Nat.dvd_of_mod_eq_zero hrem
  · simp only [hrem, pow_one] at hn
    exact (eisensteinOmega_ne_one hn).elim
  · simp only [hrem] at hn
    exact (eisensteinOmega_sq_ne_one hn).elim

------------------------------------------------------------------------
-- Integral-valued cubic and quadratic characters.
------------------------------------------------------------------------

private theorem split_three_dvd_card_sub_one
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    3 ∣ Fintype.card (ZMod p) - 1 := by
  simpa [ZMod.card] using (show 3 ∣ p - 1 by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega)

/-- An exact-order-three character taking values in literal `Z[ω]`. -/
noncomputable def eisensteinCubicCharacter
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    MulChar (ZMod p) EisensteinQA :=
  Classical.choose <|
    MulChar.exists_mulChar_orderOf (ZMod p)
      (split_three_dvd_card_sub_one p hmod)
      eisensteinOmega_isPrimitiveRoot_three

/-- The integral-valued character has exact order three. -/
theorem eisensteinCubicCharacter_order
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    orderOf (eisensteinCubicCharacter p hmod) = 3 :=
  Classical.choose_spec <|
    MulChar.exists_mulChar_orderOf (ZMod p)
      (split_three_dvd_card_sub_one p hmod)
      eisensteinOmega_isPrimitiveRoot_three

/-- Quadratic character with values embedded in the same integral ring. -/
noncomputable def eisensteinQuadraticCharacter
    (p : Nat) [Fact p.Prime] : MulChar (ZMod p) EisensteinQA :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom EisensteinQA)

/-- The literal integral mixed Jacobi element. -/
noncomputable def eisensteinMixedJacobi
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) : EisensteinQA :=
  jacobiSum (eisensteinCubicCharacter p hmod)
    (eisensteinQuadraticCharacter p)

------------------------------------------------------------------------
-- Explicit embedding Z[ω] -> C.
------------------------------------------------------------------------

/-- Standard complex Eisenstein root. -/
noncomputable def complexOmega : ℂ :=
  ((-1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2

private theorem complexOmega_sq_relation :
    complexOmega * complexOmega = (-1 : Int) • (1 : ℂ) + (-1 : Int) • complexOmega := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext
  · simp [complexOmega, Complex.mul_re, hs]
    ring
  · simp [complexOmega, Complex.mul_im]
    ring

/-- Coordinate embedding sending the integral generator to the standard
complex primitive cube root. -/
noncomputable def eisensteinToComplex : EisensteinQA →+* ℂ :=
  (QuadraticAlgebra.lift
    (R := Int) (a := (-1 : Int)) (b := (-1 : Int))
    ⟨complexOmega, complexOmega_sq_relation⟩).toRingHom

@[simp]
theorem eisensteinToComplex_omega :
    eisensteinToComplex (QuadraticAlgebra.omega : EisensteinQA) = complexOmega := by
  simp [eisensteinToComplex]

private theorem complexOmega_im_pos : 0 < complexOmega.im := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  simp [complexOmega]
  positivity

/-- The standard complex embedding is injective; its imaginary coordinate
recovers the integral `ω` coefficient. -/
theorem eisensteinToComplex_injective : Function.Injective eisensteinToComplex := by
  intro x y hxy
  suffices h0 : x - y = 0 by exact sub_eq_zero.mp h0
  have hm : eisensteinToComplex (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  let z := x - y
  have hz : eisensteinToComplex z = 0 := hm
  have hformula : eisensteinToComplex z =
      (z.re : ℂ) + (z.im : ℂ) * complexOmega := by
    simp [eisensteinToComplex, QuadraticAlgebra.lift_apply, z]
  rw [hformula] at hz
  have himC := congrArg Complex.im hz
  have hωpos := complexOmega_im_pos
  have himR : (z.im : ℝ) = 0 := by
    simp only [map_zero, Complex.zero_im, Complex.add_im, Complex.intCast_im,
      zero_add, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      zero_mul, add_zero] at himC
    nlinarith
  have him : z.im = 0 := by exact_mod_cast himR
  have hreC := congrArg Complex.re hz
  have hreR : (z.re : ℝ) = 0 := by
    simp [him] at hreC
    exact hreC
  have hre : z.re = 0 := by exact_mod_cast hreR
  apply QuadraticAlgebra.ext <;> simp [z, hre, him]

private theorem complexOmega_conj : star complexOmega = -(1 : ℂ) - complexOmega := by
  apply Complex.ext
  · simp [complexOmega]
    ring
  · simp [complexOmega]
    ring

/-- The embedding commutes with quadratic/Eisenstein conjugation. -/
theorem eisensteinToComplex_star (z : EisensteinQA) :
    eisensteinToComplex (star z) = star (eisensteinToComplex z) := by
  have hz : z = z.re • (1 : EisensteinQA) + z.im • QuadraticAlgebra.omega :=
    (QuadraticAlgebra.re_smul_add_im_smul z).symm
  rw [hz]
  simp [eisensteinToComplex_omega, complexOmega_conj, QuadraticAlgebra.star_eq]
  ring

------------------------------------------------------------------------
-- Transport the integral Jacobi element into the complex compiler.
------------------------------------------------------------------------

noncomputable def complexCharacterFromEisenstein
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) : MulChar (ZMod p) ℂ :=
  (eisensteinCubicCharacter p hmod).ringHomComp eisensteinToComplex

private theorem complexCharacterFromEisenstein_order
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    orderOf (complexCharacterFromEisenstein p hmod) = 3 := by
  let ψ := eisensteinCubicCharacter p hmod
  let ψc := complexCharacterFromEisenstein p hmod
  have hp3 : ψc ^ 3 = 1 := by
    rw [ψc, complexCharacterFromEisenstein, MulChar.ringHomComp_pow]
    have h := pow_orderOf_eq_one ψ
    rw [eisensteinCubicCharacter_order p hmod] at h
    rw [h]
    simp
  have hne : ψc ≠ 1 := by
    exact (MulChar.ringHomComp_ne_one_iff eisensteinToComplex_injective).2 <| by
      intro h
      have ho := eisensteinCubicCharacter_order p hmod
      rw [h, orderOf_one] at ho
      norm_num at ho
  exact orderOf_eq_prime_iff.mpr ⟨hp3, hne⟩

private theorem mappedQuadraticCharacter_eq_complex
    (p : Nat) [Fact p.Prime] :
    (eisensteinQuadraticCharacter p).ringHomComp eisensteinToComplex =
      (quadraticCharComplex : MulChar (ZMod p) ℂ) := by
  ext x
  simp [eisensteinQuadraticCharacter, quadraticCharComplex, eisensteinToComplex]

/-- Mapping the integral Jacobi element gives the mixed Jacobi sum for the
mapped exact-order-three complex character. -/
theorem map_eisensteinMixedJacobi
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    eisensteinToComplex (eisensteinMixedJacobi p hmod) =
      jacobiSum (complexCharacterFromEisenstein p hmod)
        quadraticCharComplex := by
  rw [eisensteinMixedJacobi, ← jacobiSum_ringHomComp]
  simp [complexCharacterFromEisenstein, mappedQuadraticCharacter_eq_complex]

private theorem complexCharacter_certificate
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    CubicCharacterCertificate (ZMod p) := by
  let ψ := complexCharacterFromEisenstein p hmod
  have hψ := complexCharacterFromEisenstein_order p hmod
  refine
    { character := ψ
      nontrivial := ?_
      squareNontrivial := ?_
      cubeWeightedReindex := cubeWeightedReindex_of_orderThree p hmod ψ hψ }
  · intro h
    have ho := hψ
    rw [h, orderOf_one] at ho
    norm_num at ho
  · intro hsq
    have hp2 : ψ ^ 2 = 1 := by simpa [pow_two] using hsq
    have hd := orderOf_dvd_of_pow_eq_one hp2
    rw [hψ] at hd
    norm_num at hd

private theorem mappedMixedJacobi_conj
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    star (eisensteinToComplex (eisensteinMixedJacobi p hmod)) =
      jacobiSum
        (complexCharacterFromEisenstein p hmod *
          complexCharacterFromEisenstein p hmod)
        quadraticCharComplex := by
  let cert := complexCharacter_certificate p hmod
  have hneg := orderThreeCharacter_negOne cert.character
    (complexCharacterFromEisenstein_order p hmod)
  have htrace := cubicJacobiTrace_eq_neg_unweightedPair cert
    (complexCharacterFromEisenstein_order p hmod)
  have hstar :
      star (jacobiSum cert.character quadraticCharComplex) =
        jacobiSum (cert.character * cert.character) quadraticCharComplex := by
    have hsquare : cert.character * cert.character = cert.character⁻¹ := by
      apply mul_left_cancel (a := cert.character)
      have hp3 := pow_orderOf_eq_one cert.character
      rw [complexCharacterFromEisenstein_order p hmod] at hp3
      calc
        cert.character * (cert.character * cert.character) = cert.character ^ 3 := by ring
        _ = 1 := hp3
        _ = cert.character * cert.character⁻¹ := by simp
    have hquad : (quadraticCharComplex : MulChar (ZMod p) ℂ)⁻¹ = quadraticCharComplex :=
      ((quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)).inv
    rw [jacobiSum, jacobiSum]
    simp_rw [map_sum, map_mul, MulChar.star_apply', map_sub, map_one]
    rw [hsquare, hquad]
  rw [map_eisensteinMixedJacobi p hmod]
  simpa [cert] using hstar

------------------------------------------------------------------------
-- Norm and trace on the integral carrier.
------------------------------------------------------------------------

private theorem mappedMixedJacobi_normSq
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    eisensteinToComplex (eisensteinMixedJacobi p hmod) *
        star (eisensteinToComplex (eisensteinMixedJacobi p hmod)) = (p : ℂ) := by
  let ψ := complexCharacterFromEisenstein p hmod
  let η := (quadraticCharComplex : MulChar (ZMod p) ℂ)
  have hψorder := complexCharacterFromEisenstein_order p hmod
  have hψne : ψ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hψorder
    norm_num at hψorder
  have hp2 : p ≠ 2 := by
    intro hp
    subst p
    norm_num at hmod
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have hηquad : η.IsQuadratic :=
    (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)
  have hηne : η ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff Int.cast_injective).2
      (quadraticChar_ne_one (F := ZMod p) hchar)
  have hprod : ψ * η ≠ 1 := by
    intro h
    have hψη : ψ = η := by
      calc
        ψ = ψ * η * η⁻¹ := by simp
        _ = η⁻¹ := by rw [h]; simp
        _ = η := hηquad.inv
    have hψ2 : ψ ^ 2 = 1 := by rw [hψη]; exact hηquad.sq_eq_one
    have hd := orderOf_dvd_of_pow_eq_one hψ2
    rw [hψorder] at hd
    norm_num at hd
  have hJ := jacobiSum_mul_jacobiSum_inv
    (F := ZMod p) (F' := ℂ)
    (by rw [ZMod.ringChar_zmod_n]; simp [Fact.out.ne_zero])
    hψne hηne hprod
  rw [map_eisensteinMixedJacobi p hmod, mappedMixedJacobi_conj p hmod]
  simpa [ψ, η, hηquad.inv] using hJ

/-- The integral Jacobi element has literal Eisenstein norm `p`. -/
theorem eisensteinMixedJacobi_norm
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    QuadraticAlgebra.norm (eisensteinMixedJacobi p hmod) = p := by
  let J := eisensteinMixedJacobi p hmod
  have hmul : J * star J = algebraMap Int EisensteinQA (QuadraticAlgebra.norm J) := by
    exact (QuadraticAlgebra.algebraMap_norm_eq_mul_star J).symm
  have hmap := congrArg eisensteinToComplex hmul
  have hnorm := mappedMixedJacobi_normSq p hmod
  have hcast : ((QuadraticAlgebra.norm J : Int) : ℂ) = (p : ℂ) := by
    rw [map_mul, eisensteinToComplex_star] at hmap
    simpa [J] using hmap.symm.trans hnorm
  exact_mod_cast hcast

/-- The integral Jacobi trace is the negative of the same curve's Frobenius
trace. -/
theorem eisensteinMixedJacobi_trace
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    QuadraticAlgebra.trace (eisensteinMixedJacobi p hmod) =
      -jZeroFrobeniusTraceInt (ZMod p) := by
  let J := eisensteinMixedJacobi p hmod
  let cert := complexCharacter_certificate p hmod
  have hcompiler := jZeroTrace_cast_eq_neg_unweightedJacobiPair
    (F := ZMod p)
    (by rw [ZMod.ringChar_zmod_n]; intro hp; subst p; norm_num at hmod)
    cert (complexCharacterFromEisenstein_order p hmod)
  have htraceAlg :
      algebraMap Int EisensteinQA (QuadraticAlgebra.trace J) = J + star J :=
    QuadraticAlgebra.algebraMap_trace_eq_add_star J
  have hmap := congrArg eisensteinToComplex htraceAlg
  have hcast : ((QuadraticAlgebra.trace J : Int) : ℂ) =
      -((jZeroFrobeniusTraceInt (ZMod p) : Int) : ℂ) := by
    rw [map_add, eisensteinToComplex_star] at hmap
    rw [map_eisensteinMixedJacobi p hmod] at hmap
    have hconj := mappedMixedJacobi_conj p hmod
    rw [hconj] at hmap
    exact hmap.symm.trans hcompiler.symm
  exact_mod_cast hcast

structure IntegralJacobiBoundary where
  integralEisensteinCubicCharacterPaid : Bool := true
  literalIntegralJacobiElementPaid : Bool := true
  complexEmbeddingPaid : Bool := true
  integralJacobiNormEqualsSplitPrime : Bool := true
  integralJacobiTraceMatchesFrobenius : Bool := true
  primaryAssociateIdentificationPaid : Bool := false
  heckeCharacterPaid : Bool := false
  globalEllipticLSeriesPaid : Bool := false

/-- The local split-prime arithmetic is now reduced to primary-associate
normalization: an explicit integral norm-p factor with exactly the correct
Frobenius trace is already constructed. -/
def canonicalBoundary : IntegralJacobiBoundary := {}

end Integration.EisensteinJZeroIntegralJacobiExact
