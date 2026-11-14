import Integration.EisensteinJZeroIntegralJacobiExact
import Integration.EisensteinJZeroSplitEulerFactorExact
import Integration.EisensteinJZeroIntegralHeckeCharacterExact
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Split Jacobi/Frobenius prime = conductor-normalized Hecke ideal value

This owner pays the decisive same-prime local/global weld without importing a
CM reciprocity theorem as a proof term.

Let

  J_p = Σ_x ψ(x) η(1-x) ∈ Z[ω]

be the integral Jacobi element constructed on this branch, and let
`π_p = -J_p`, already proved to satisfy `N(π_p)=p` and
`Tr(π_p)=a_p` for the same j=0 curve.

The conductor normalization is proved directly from the sum:

* modulo 2, the quadratic values ±1 coincide and
  `J_p ≡ Σ_{x≠1} ψ(x) = -1`;
* modulo sqrt(-3)=1+2ω, every nonzero cubic-character value is congruent to
  one, hence `J_p ≡ Σ_{x≠0} η(1-x) = -1`;
* 2 and sqrt(-3) are explicitly coprime, so
  `π_p=-J_p ≡ 1 mod 2*sqrt(-3)`.

Thus the principal ideal `(π_p)` is conductor-coprime and the integral Hecke
character returns π_p exactly.  External CM literature motivates the conductor
but is not used as proof authority for this equality.
-/

namespace Integration.EisensteinJZeroJacobiHeckePrimeMatchExact

open scoped BigOperators
open Finset
open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinSixUnitsExact
open Integration.EisensteinJZeroIntegralJacobiExact
open Integration.EisensteinJZeroSplitEulerFactorExact
open Integration.EisensteinJZeroHeckeConductorExact
open Integration.EisensteinJZeroHeckeIdealNormalizationExact
open Integration.EisensteinJZeroIntegralHeckeCharacterExact

private abbrev E := EisensteinQA

private def nonzeroIndicator {p : Nat} (t : ZMod p) : E :=
  if t = 0 then 0 else 1

------------------------------------------------------------------------
-- Quadratic character reduction modulo two.
------------------------------------------------------------------------

private theorem quadraticCharacter_congr_indicator_mod_two
    (p : Nat) [Fact p.Prime] (t : ZMod p) :
    (2 : E) ∣ eisensteinQuadraticCharacter p t - nonzeroIndicator t := by
  by_cases ht : t = 0
  · subst t
    simp [eisensteinQuadraticCharacter, nonzeroIndicator]
  · have hχ := quadraticChar_dichotomy (F := ZMod p) ht
    rcases hχ with hχ | hχ
    · simp [eisensteinQuadraticCharacter, nonzeroIndicator, ht, hχ]
    · refine ⟨-1, ?_⟩
      simp [eisensteinQuadraticCharacter, nonzeroIndicator, ht, hχ]
      ring

private theorem cubicCharacter_nontrivial
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    eisensteinCubicCharacter p hmod ≠ 1 := by
  intro h
  have ho := eisensteinCubicCharacter_order p hmod
  rw [h, orderOf_one] at ho
  norm_num at ho

private theorem cubicCharacter_sum_zero
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    ∑ x : ZMod p, eisensteinCubicCharacter p hmod x = 0 :=
  MulChar.sum_eq_zero_of_ne_one (cubicCharacter_nontrivial p hmod)

private theorem indicator_shifted_cubic_sum_neg_one
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    ∑ x : ZMod p,
      eisensteinCubicCharacter p hmod x * nonzeroIndicator (1 - x) = -1 := by
  classical
  let ψ := eisensteinCubicCharacter p hmod
  have hsum : ∑ x : ZMod p, ψ x = 0 := cubicCharacter_sum_zero p hmod
  have hrew :
      (∑ x : ZMod p, ψ x * nonzeroIndicator (1 - x)) =
        ∑ x in (Finset.univ.erase (1 : ZMod p)), ψ x := by
    apply Finset.sum_congr
    · ext x
      simp [nonzeroIndicator, sub_eq_zero]
    · intro x hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx
      simp [nonzeroIndicator, sub_ne_zero.mpr hx.1]
  rw [hrew]
  calc
    (∑ x in (Finset.univ.erase (1 : ZMod p)), ψ x)
        = (∑ x : ZMod p, ψ x) - ψ 1 := by
            rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : ZMod p))]
            ring
    _ = -1 := by rw [hsum]; simp

private theorem jacobi_plus_one_dvd_two
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    (2 : E) ∣ eisensteinMixedJacobi p hmod + 1 := by
  let ψ := eisensteinCubicCharacter p hmod
  let η := eisensteinQuadraticCharacter p
  have hdiff :
      (2 : E) ∣
        eisensteinMixedJacobi p hmod -
          ∑ x : ZMod p, ψ x * nonzeroIndicator (1 - x) := by
    rw [eisensteinMixedJacobi, jacobiSum, ← Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro x hx
    have hη := quadraticCharacter_congr_indicator_mod_two p (1 - x)
    exact dvd_mul_of_dvd_right hη (ψ x)
  rw [indicator_shifted_cubic_sum_neg_one p hmod] at hdiff
  simpa [sub_neg_eq_add] using hdiff

------------------------------------------------------------------------
-- Cubic character reduction modulo sqrt(-3).
------------------------------------------------------------------------

private theorem cubicCharacter_value_cube_one
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1)
    (t : ZMod p) (ht : t ≠ 0) :
    eisensteinCubicCharacter p hmod t ^ 3 = 1 := by
  have hp := pow_orderOf_eq_one (eisensteinCubicCharacter p hmod)
  rw [eisensteinCubicCharacter_order p hmod] at hp
  have h := congrArg (fun χ : MulChar (ZMod p) E => χ t) hp
  simpa [MulChar.pow_apply', MulChar.one_apply (isUnit_iff_ne_zero.mpr ht)] using h

private theorem cubicCharacter_congr_indicator_mod_sqrtMinusThree
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) (t : ZMod p) :
    sqrtMinusThreeEisenstein ∣
      eisensteinCubicCharacter p hmod t - nonzeroIndicator t := by
  by_cases ht : t = 0
  · subst t
    simp [nonzeroIndicator]
  · let U : Eˣ :=
      (eisensteinCubicCharacter p hmod).toUnitHom (Units.mk0 t ht)
    have hUval : (U : E) = eisensteinCubicCharacter p hmod t := rfl
    have hcube : (U : E) ^ 3 = 1 := by
      rw [hUval]
      exact cubicCharacter_value_cube_one p hmod t ht
    have hclass := unit_classification (U : E) U.isUnit
    rcases hclass with h | h | h | h | h | h
    · rw [hUval] at h
      simp [nonzeroIndicator, ht, h, unitOne, asQuadraticAlgebra]
    · rw [h] at hcube
      native_decide at hcube
    · rw [hUval] at h
      refine ⟨1 + (QuadraticAlgebra.omega : E), ?_⟩
      simp [nonzeroIndicator, ht, h, unitOmega, asQuadraticAlgebra,
        sqrtMinusThreeEisenstein]
      rw [omega_square_relation]
      ring
    · rw [h] at hcube
      native_decide at hcube
    · rw [hUval] at h
      refine ⟨(QuadraticAlgebra.omega : E), ?_⟩
      simp [nonzeroIndicator, ht, h, unitOmegaSquared, asQuadraticAlgebra,
        sqrtMinusThreeEisenstein]
      rw [omega_square_relation]
      ring
    · rw [h] at hcube
      native_decide at hcube

private theorem quadraticCharacter_nontrivial
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    eisensteinQuadraticCharacter p ≠ 1 := by
  have hp2 : p ≠ 2 := by
    intro hp
    subst p
    norm_num at hmod
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  exact (MulChar.ringHomComp_ne_one_iff (Int.castRingHom E).injective).2
    (quadraticChar_ne_one (F := ZMod p) hchar)

private theorem shiftedQuadratic_sum_zero
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    ∑ x : ZMod p, eisensteinQuadraticCharacter p (1 - x) = 0 := by
  have hsum : ∑ y : ZMod p, eisensteinQuadraticCharacter p y = 0 :=
    MulChar.sum_eq_zero_of_ne_one (quadraticCharacter_nontrivial p hmod)
  let e : ZMod p ≃ ZMod p := Equiv.subLeft 1
  simpa [e, Equiv.subLeft_apply] using
    e.sum_comp (eisensteinQuadraticCharacter p) |>.trans hsum

private theorem indicator_cubic_shiftedQuadratic_sum_neg_one
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    ∑ x : ZMod p,
      nonzeroIndicator x * eisensteinQuadraticCharacter p (1 - x) = -1 := by
  classical
  let η := eisensteinQuadraticCharacter p
  have hsum := shiftedQuadratic_sum_zero p hmod
  have hrew :
      (∑ x : ZMod p, nonzeroIndicator x * η (1 - x)) =
        ∑ x in (Finset.univ.erase (0 : ZMod p)), η (1 - x) := by
    apply Finset.sum_congr
    · ext x
      simp [nonzeroIndicator]
    · intro x hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx
      simp [nonzeroIndicator, hx.1]
  rw [hrew]
  calc
    (∑ x in (Finset.univ.erase (0 : ZMod p)), η (1 - x))
        = (∑ x : ZMod p, η (1 - x)) - η 1 := by
            rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p))]
            ring
    _ = -1 := by rw [hsum]; simp

private theorem jacobi_plus_one_dvd_sqrtMinusThree
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    sqrtMinusThreeEisenstein ∣ eisensteinMixedJacobi p hmod + 1 := by
  let ψ := eisensteinCubicCharacter p hmod
  let η := eisensteinQuadraticCharacter p
  have hdiff :
      sqrtMinusThreeEisenstein ∣
        eisensteinMixedJacobi p hmod -
          ∑ x : ZMod p, nonzeroIndicator x * η (1 - x) := by
    rw [eisensteinMixedJacobi, jacobiSum, ← Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro x hx
    have hψ := cubicCharacter_congr_indicator_mod_sqrtMinusThree p hmod x
    exact dvd_mul_of_dvd_left hψ (η (1 - x))
  rw [indicator_cubic_shiftedQuadratic_sum_neg_one p hmod] at hdiff
  simpa [sub_neg_eq_add] using hdiff

------------------------------------------------------------------------
-- Chinese-remainder combination into the literal conductor.
------------------------------------------------------------------------

private theorem two_isCoprime_sqrtMinusThree :
    IsCoprime (2 : E) sqrtMinusThreeEisenstein := by
  refine ⟨-(QuadraticAlgebra.omega : E), 1, ?_⟩
  unfold sqrtMinusThreeEisenstein
  ring

private theorem conductor_dvd_of_two_and_sqrt_dvd
    {d : E} (h2 : (2 : E) ∣ d)
    (hs : sqrtMinusThreeEisenstein ∣ d) :
    heckeConductorElement ∣ d := by
  rcases h2 with ⟨a, ha⟩
  have hsa : sqrtMinusThreeEisenstein ∣ a := by
    apply (isCoprime_comm.mp two_isCoprime_sqrtMinusThree).dvd_of_dvd_mul_left
    rw [← ha]
    exact hs
  rcases hsa with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [heckeConductorElement, ha, hq]
  ring

/-- The actual Frobenius/Jacobi factor is one modulo the literal Hecke
conductor. -/
theorem jacobiFrobeniusPrime_congruent_one
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    CongruentModHeckeConductor (jacobiFrobeniusPrime p hmod) 1 := by
  unfold CongruentModHeckeConductor jacobiFrobeniusPrime
  have h2 := jacobi_plus_one_dvd_two p hmod
  have hs := jacobi_plus_one_dvd_sqrtMinusThree p hmod
  have hcond := conductor_dvd_of_two_and_sqrt_dvd h2 hs
  exact dvd_neg.mpr <| by
    simpa [neg_sub] using hcond

------------------------------------------------------------------------
-- Principal ideal and exact Hecke-character value.
------------------------------------------------------------------------

/-- Principal ideal generated by the same split-prime Frobenius factor. -/
noncomputable def jacobiFrobeniusIdeal
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) : Ideal E :=
  Ideal.span ({jacobiFrobeniusPrime p hmod} : Set E)

/-- Congruence to one immediately gives element-level coprimality with the
conductor. -/
private theorem isCoprime_conductor_of_congruent_one
    {z : E} (hz : CongruentModHeckeConductor z 1) :
    IsCoprime z heckeConductorElement := by
  unfold CongruentModHeckeConductor at hz
  rcases hz with ⟨q, hq⟩
  refine ⟨1, -q, ?_⟩
  rw [hq]
  ring

/-- The Jacobi/Frobenius principal ideal lies in the conductor-coprime ideal
monoid. -/
theorem jacobiFrobeniusIdeal_coprime
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    IdealCoprimeToHeckeConductor (jacobiFrobeniusIdeal p hmod) := by
  unfold IdealCoprimeToHeckeConductor heckeConductorIdeal jacobiFrobeniusIdeal
  exact (Ideal.isCoprime_span_singleton_iff _ _).2
    (isCoprime_conductor_of_congruent_one
      (jacobiFrobeniusPrime_congruent_one p hmod))

/-- Same ideal bundled as an input to the integral ideal character. -/
noncomputable def jacobiFrobeniusIdealCode
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) : HeckeIdealMonoid :=
  ⟨jacobiFrobeniusIdeal p hmod, jacobiFrobeniusIdeal_coprime p hmod⟩

/-- Exact prime-value match: the conductor-normalized ideal character returns
the SAME integral Frobenius factor whose norm and trace already produce the
elliptic local Euler polynomial. -/
theorem integralHeckeCharacter_jacobiFrobeniusIdeal
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    integralHeckeCharacter (jacobiFrobeniusIdealCode p hmod) =
      jacobiFrobeniusPrime p hmod := by
  apply integralHeckeCharacter_eq_of_normalized
  · rfl
  · exact jacobiFrobeniusPrime_congruent_one p hmod

structure JacobiHeckePrimeMatchBoundary where
  jacobiMinusOneModuloTwoPaid : Bool := true
  jacobiMinusOneModuloRamifiedThreePaid : Bool := true
  conductorCoprimeFactorsPaid : Bool := true
  jacobiFrobeniusConductorNormalizationPaid : Bool := true
  splitPrimeIdealCharacterValueMatchPaid : Bool := true
  splitPrimeEllipticHeckeLocalMatchReady : Bool := true
  inertPrimeIdealCharacterLocalMatchPaid : Bool := false
  analyticEulerProductPaid : Bool := false
  globalLSeriesAgreementPaid : Bool := false

/-- The split prime-value reciprocity seam is paid internally from the Jacobi
sum; no external CM equality is promoted into the kernel. -/
def canonicalBoundary : JacobiHeckePrimeMatchBoundary := {}

end Integration.EisensteinJZeroJacobiHeckePrimeMatchExact
