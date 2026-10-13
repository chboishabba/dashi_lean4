import Integration.EisensteinSplitPrimeExact
import Integration.EisensteinInertPrimeLegendreExact

namespace Dashi.EisensteinPrimeClassificationExact

open Dashi.EisensteinLatticeCounting
open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinEuclideanDomainExact
open Dashi.EisensteinSplitPrimeExact
open Dashi.EisensteinInertPrimeLegendreExact

------------------------------------------------------------------------
-- Turn the transformed-coordinate obstruction into literal coefficient
-- divisibility for odd inert primes.
------------------------------------------------------------------------

theorem odd_inert_prime_forces_coordinates
    (p : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (hmod : p % 3 = 2)
    {a b : Int}
    (hdiv : (p : Int) ∣ eisensteinNorm a b) :
    (p : Int) ∣ a ∧ (p : Int) ∣ b := by
  obtain ⟨htrans, hb⟩ :=
    odd_prime_mod_three_two_forces_transformed_coordinates
      p hp hp2 hmod hdiv
  have h2a : (p : Int) ∣ 2 * a := by
    have hadd := dvd_add htrans hb
    simpa [sub_add_cancel] using hadd
  have hpInt : Prime (p : Int) :=
    (Nat.prime_iff_prime_int).1 hp
  rcases hpInt.dvd_or_dvd h2a with hp2int | ha
  · have hp2nat : p ∣ 2 := by exact_mod_cast hp2int
    have peq : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hp2nat
    exact (hp2 peq).elim
  · exact ⟨ha, hb⟩

------------------------------------------------------------------------
-- If a prime divides both coordinates of a norm-p element, positive
-- definiteness gives the impossible equation p = p^2 * positive_integer.
------------------------------------------------------------------------

theorem prime_coordinate_divisibility_blocks_norm_p
    (p : Nat) (hp : p.Prime)
    {a b : Int}
    (ha : (p : Int) ∣ a)
    (hb : (p : Int) ∣ b) :
    eisensteinNorm a b ≠ p := by
  rintro hnorm
  rcases ha with ⟨A, rfl⟩
  rcases hb with ⟨B, rfl⟩
  have hfactor :
      eisensteinNorm ((p : Int) * A) ((p : Int) * B)
        = (p : Int) ^ 2 * eisensteinNorm A B := by
    simp [eisensteinNorm]
    ring
  have hk_nonneg : 0 ≤ eisensteinNorm A B := by
    simpa [norm_eq_coordinate_norm, asQuadraticAlgebra] using
      norm_nonneg (asQuadraticAlgebra A B)
  have hp_pos : (0 : Int) < p := by exact_mod_cast hp.pos
  have hp_gt_one : (1 : Int) < p := by exact_mod_cast hp.one_lt
  rw [hfactor] at hnorm
  have heq :
      (p : Int) = (p : Int) ^ 2 * eisensteinNorm A B := hnorm.symm
  have hk_pos : 0 < eisensteinNorm A B := by
    nlinarith
  have hk_one : 1 ≤ eisensteinNorm A B := by omega
  nlinarith

/-- No prime in the inert residue class is itself an Eisenstein norm.  The
exceptional prime `2` uses the direct parity theorem; all odd inert primes use
quadratic reciprocity. -/
theorem inert_prime_has_no_norm_witness
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 2) :
    ¬ ∃ z : EisensteinQA, QuadraticAlgebra.norm z = p := by
  rintro ⟨z, hz⟩
  have hdiv : (p : Int) ∣ QuadraticAlgebra.norm z := by
    rw [hz]
  have hcoords : (p : Int) ∣ z.re ∧ (p : Int) ∣ z.im := by
    by_cases hp2 : p = 2
    · subst p
      simpa [norm_eq_coordinate_norm] using
        two_dvd_norm_forces_coordinates
          (a := z.re) (b := z.im) hdiv
    · simpa [norm_eq_coordinate_norm] using
        odd_inert_prime_forces_coordinates
          p hp hp2 hmod hdiv
  exact prime_coordinate_divisibility_blocks_norm_p
    p hp hcoords.1 hcoords.2
    (by simpa [norm_eq_coordinate_norm] using hz)

/-- In a Euclidean/UFD Eisenstein ring, an inert rational prime is irreducible:
otherwise the generic prime-square factor argument would produce a forbidden
norm-p factor. -/
theorem inert_prime_irreducible
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 2) :
    Irreducible (p : EisensteinQA) := by
  by_contra hnot
  obtain ⟨z, hz⟩ :=
    norm_witness_of_nat_prime_of_not_irreducible p hp hnot
  exact inert_prime_has_no_norm_witness p hp hmod ⟨z, hz⟩

/-- Split residue-class primes are reducible by the explicit modular-root test
construction. -/
theorem split_prime_reducible
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1) :
    ¬ Irreducible (p : EisensteinQA) :=
  split_prime_not_irreducible p hp hmod

/-- Rational-prime trichotomy relevant to factorization in `Z[ω]`. -/
inductive RationalPrimeBehavior where
  | ramifiedThree
  | splitModThreeOne
  | inertModThreeTwo
  deriving DecidableEq

def rationalPrimeBehavior (p : Nat) : RationalPrimeBehavior :=
  if p = 3 then .ramifiedThree
  else if p % 3 = 1 then .splitModThreeOne
  else .inertModThreeTwo

structure EisensteinPrimeClassificationBoundary where
  ramifiedThreePaid : Bool := true
  splitResidueReducibilityPaid : Bool := true
  splitNormPrimeWitnessPaid : Bool := true
  inertResidueIrreducibilityPaid : Bool := true
  exceptionalPrimeTwoPaid : Bool := true
  allRationalPrimeLocalBehaviorPaid : Bool := true
  globalExponentCountPaid : Bool := false

def canonicalBoundary : EisensteinPrimeClassificationBoundary := {}

end Dashi.EisensteinPrimeClassificationExact
