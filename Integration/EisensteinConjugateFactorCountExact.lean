import Integration.EisensteinNormFactorEquationExact
import Mathlib.Algebra.Group.Irreducible.Lemmas

namespace Dashi.EisensteinConjugateFactorCountExact

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinEuclideanDomainExact

------------------------------------------------------------------------
-- Divisibility transport through the involutive ring automorphism `star`.
------------------------------------------------------------------------

theorem star_dvd_star_iff (a b : EisensteinQA) :
    star a ∣ star b ↔ a ∣ b := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨star c, ?_⟩
    have hstar := congrArg star hc
    simpa [mul_comm] using hstar
  · rintro ⟨c, hc⟩
    refine ⟨star c, ?_⟩
    simpa [hc, mul_comm]

theorem pow_dvd_star_iff_conjugate_pow_dvd
    (q z : EisensteinQA) (k : Nat) :
    q ^ k ∣ star z ↔ (star q) ^ k ∣ z := by
  simpa using (star_dvd_star_iff (q ^ k) (star z))

/-- Conjugation preserves irreducibility. -/
theorem star_irreducible {q : EisensteinQA} (hq : Irreducible q) :
    Irreducible (star q) := by
  exact hq.map (starRingAut (R := EisensteinQA))

------------------------------------------------------------------------
-- Valuation transport through the involution.
------------------------------------------------------------------------

theorem conjugate_prime_count_le
    (z : EisensteinQA) (hz : z ≠ 0)
    (q : EisensteinQA) (hq : Irreducible q) :
    Associates.count (Associates.mk q)
        (Associates.mk (star z)).factors
      ≤ Associates.count (Associates.mk (star q))
        (Associates.mk z).factors := by
  classical
  have hzstar : star z ≠ 0 := by
    intro hs
    apply hz
    have := congrArg star hs
    simpa using this
  have hqA : Irreducible (Associates.mk q) :=
    Associates.irreducible_mk.mpr hq
  have hqs : Irreducible (star q) := star_irreducible hq
  have hqsA : Irreducible (Associates.mk (star q)) :=
    Associates.irreducible_mk.mpr hqs
  let k := Associates.count (Associates.mk q)
      (Associates.mk (star z)).factors
  have hk_le :
      (Associates.mk q) ^ k ≤ Associates.mk (star z) := by
    apply (Associates.prime_pow_dvd_iff_le
      (Associates.mk_ne_zero.mpr hzstar) hqA).2
    exact le_rfl
  have hk_dvd : q ^ k ∣ star z := by
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
    exact hk_le
  have hk_star_dvd : (star q) ^ k ∣ z :=
    (pow_dvd_star_iff_conjugate_pow_dvd q z k).1 hk_dvd
  have hk_star_le :
      (Associates.mk (star q)) ^ k ≤ Associates.mk z := by
    rw [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd]
    exact hk_star_dvd
  exact (Associates.prime_pow_dvd_iff_le
    (Associates.mk_ne_zero.mpr hz) hqsA).1 hk_star_le

/-- Prime-factor multiplicities are transported exactly by conjugation. -/
theorem conjugate_prime_count
    (z : EisensteinQA) (hz : z ≠ 0)
    (q : EisensteinQA) (hq : Irreducible q) :
    Associates.count (Associates.mk q)
        (Associates.mk (star z)).factors
      = Associates.count (Associates.mk (star q))
        (Associates.mk z).factors := by
  apply Nat.le_antisymm
  · exact conjugate_prime_count_le z hz q hq
  · have hzstar : star z ≠ 0 := by
      intro hs
      apply hz
      have := congrArg star hs
      simpa using this
    have hqs : Irreducible (star q) := star_irreducible hq
    have h := conjugate_prime_count_le (star z) hzstar (star q) hqs
    simpa using h

structure EisensteinConjugateFactorBoundary where
  starDivisibilityTransportPaid : Bool := true
  starPreservesIrreduciblePaid : Bool := true
  primePowerDivisibilityTransportPaid : Bool := true
  factorMultiplicityTransportPaid : Bool := true
  localExponentEquationsReady : Bool := true
  globalCardinalityFormulaPaid : Bool := false

def canonicalBoundary : EisensteinConjugateFactorBoundary := {}

end Dashi.EisensteinConjugateFactorCountExact
