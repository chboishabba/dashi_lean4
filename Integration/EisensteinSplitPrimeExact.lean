import Integration.EisensteinEuclideanDomainExact
import Integration.EisensteinLegendreModThreeExact
import Mathlib.Data.Nat.Prime.Int

namespace Dashi.EisensteinSplitPrimeExact

open Nat
open ZMod
open Dashi.EisensteinLatticeCounting
open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinEuclideanDomainExact
open Dashi.EisensteinLegendreModThreeExact

------------------------------------------------------------------------
-- Divisibility and units on the standard coefficient carrier.
------------------------------------------------------------------------

theorem natCast_dvd_iff_coordinates (p : Nat) (z : EisensteinQA) :
    (p : EisensteinQA) ∣ z ↔
      (p : Int) ∣ z.re ∧ (p : Int) ∣ z.im := by
  constructor
  · rintro ⟨w, rfl⟩
    constructor
    · refine ⟨w.re, ?_⟩
      simp
    · refine ⟨w.im, ?_⟩
      simp
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    refine ⟨asQuadraticAlgebra u v, ?_⟩
    ext <;> simp [asQuadraticAlgebra, hu, hv]

/-- Because the Eisenstein norm is nonnegative, the only integer-unit value it
can take is `+1`. -/
theorem isUnit_iff_norm_eq_one (z : EisensteinQA) :
    IsUnit z ↔ QuadraticAlgebra.norm z = 1 := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, Int.isUnit_iff]
  constructor
  · rintro (h | h)
    · exact h
    · have hz := norm_nonneg z
      omega
  · exact Or.inl

/-- Equivalent natural-valued form used by the prime-square factor count. -/
theorem natAbs_norm_eq_one_iff_isUnit (z : EisensteinQA) :
    (QuadraticAlgebra.norm z).natAbs = 1 ↔ IsUnit z := by
  constructor
  · intro h
    apply (isUnit_iff_norm_eq_one z).2
    have hcast : ((QuadraticAlgebra.norm z).natAbs : Int) = 1 := by
      exact_mod_cast h
    rwa [Int.natAbs_of_nonneg (norm_nonneg z)] at hcast
  · intro h
    have hn := (isUnit_iff_norm_eq_one z).1 h
    simp [hn]

------------------------------------------------------------------------
-- A modular square root of -3 produces an element whose norm is divisible by p
-- but which itself is not divisible by p.
------------------------------------------------------------------------

def splitTestElement (r : Int) : EisensteinQA :=
  asQuadraticAlgebra (r + 1) 2

theorem splitTestElement_norm (r : Int) :
    QuadraticAlgebra.norm (splitTestElement r) = r ^ 2 + 3 := by
  rw [norm_asQuadraticAlgebra]
  simp [splitTestElement, eisensteinNorm]
  ring

/-- Lift a mod-p square root of `-3` to an integral Eisenstein test element whose
norm is divisible by `p`. -/
theorem split_test_element_of_legendre_one
    (p : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (hleg : legendreSym p (-3) = 1) :
    ∃ r : Int,
      (p : Int) ∣ QuadraticAlgebra.norm (splitTestElement r) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hnonzero : ((-3 : Int) : ZMod p) ≠ 0 := by
    intro hz
    have hzleg : legendreSym p (-3) = 0 :=
      (legendreSym.eq_zero_iff p (-3)).2 hz
    omega
  obtain ⟨root, hroot⟩ := (legendreSym.eq_one_iff p hnonzero).1 hleg
  let r : Int := root.val
  refine ⟨r, ?_⟩
  rw [splitTestElement_norm]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (r ^ 2 + 3) p).mp
  have hr_cast : ((r : Int) : ZMod p) = root := by
    simpa [r] using ZMod.natCast_zmod_val root
  have hroot' : root ^ 2 = (-3 : ZMod p) := by
    simpa [pow_two] using hroot.symm
  push_cast
  rw [hr_cast, hroot']
  norm_num

/-- An odd prime cannot divide the split test element because its second
coefficient is literally `2`. -/
theorem splitTestElement_not_dvd
    (p : Nat) (hp : p.Prime) (hp2 : p ≠ 2) (r : Int) :
    ¬ (p : EisensteinQA) ∣ splitTestElement r := by
  intro h
  have hcoords :=
    (natCast_dvd_iff_coordinates p (splitTestElement r)).1 h
  have h2int : (p : Int) ∣ (2 : Int) := by
    simpa [splitTestElement, asQuadraticAlgebra] using hcoords.2
  have h2nat : p ∣ 2 := by
    exact_mod_cast h2int
  have peq : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h2nat
  exact hp2 peq

/-- Nor can it divide the conjugate test element: conjugation only negates the
second coefficient. -/
theorem splitTestElement_star_not_dvd
    (p : Nat) (hp : p.Prime) (hp2 : p ≠ 2) (r : Int) :
    ¬ (p : EisensteinQA) ∣ star (splitTestElement r) := by
  intro h
  have hcoords :=
    (natCast_dvd_iff_coordinates p (star (splitTestElement r))).1 h
  have hneg2 : (p : Int) ∣ (-2 : Int) := by
    simpa [splitTestElement, asQuadraticAlgebra] using hcoords.2
  have h2int : (p : Int) ∣ (2 : Int) := by
    simpa using (dvd_neg.mp hneg2)
  have h2nat : p ∣ 2 := by
    exact_mod_cast h2int
  have peq : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h2nat
  exact hp2 peq

/-- Integer divisibility of a norm becomes divisibility of `z * star z` by the
embedded rational prime. -/
theorem natCast_dvd_mul_star_of_dvd_norm
    (p : Nat) (z : EisensteinQA)
    (hdiv : (p : Int) ∣ QuadraticAlgebra.norm z) :
    (p : EisensteinQA) ∣ z * star z := by
  rcases hdiv with ⟨k, hk⟩
  refine ⟨(k : EisensteinQA), ?_⟩
  rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star z, hk]
  simp

------------------------------------------------------------------------
-- Split residue class => reducibility of the embedded rational prime.
------------------------------------------------------------------------

theorem split_prime_not_irreducible
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1) :
    ¬ Irreducible (p : EisensteinQA) := by
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hmod
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (3 : Nat).Prime := ⟨by norm_num⟩
  have hleg : legendreSym p (-3) = 1 :=
    legendre_neg_three_eq_one_of_mod_three_one p hp hp2 hmod
  obtain ⟨r, hnormdiv⟩ :=
    split_test_element_of_legendre_one p hp hp2 hleg
  intro hirr
  have hprime : Prime (p : EisensteinQA) := hirr.prime
  have hprod : (p : EisensteinQA) ∣
      splitTestElement r * star (splitTestElement r) :=
    natCast_dvd_mul_star_of_dvd_norm p (splitTestElement r) hnormdiv
  rcases hprime.dvd_or_dvd hprod with hz | hzs
  · exact splitTestElement_not_dvd p hp hp2 r hz
  · exact splitTestElement_star_not_dvd p hp hp2 r hzs

------------------------------------------------------------------------
-- In a Euclidean domain, reducibility of a rational prime forces a factor of
-- norm exactly p.  This is the Eisenstein analogue of Mathlib's Gaussian
-- `sq_add_sq_of_nat_prime_of_not_irreducible` theorem.
------------------------------------------------------------------------

theorem norm_witness_of_nat_prime_of_not_irreducible
    (p : Nat) (hp : p.Prime)
    (hpi : ¬ Irreducible (p : EisensteinQA)) :
    ∃ z : EisensteinQA, QuadraticAlgebra.norm z = p := by
  have hpu : ¬ IsUnit (p : EisensteinQA) := by
    rw [isUnit_iff_norm_eq_one]
    simp [QuadraticAlgebra.norm_natCast]
    nlinarith [hp.one_lt]
  have hab :
      ∃ a b : EisensteinQA,
        (p : EisensteinQA) = a * b ∧ ¬ IsUnit a ∧ ¬ IsUnit b := by
    simpa [irreducible_iff, hpu, not_forall, not_or] using hpi
  obtain ⟨a, b, hpab, hau, hbu⟩ := hab
  have hna1 : (QuadraticAlgebra.norm a).natAbs ≠ 1 :=
    mt (natAbs_norm_eq_one_iff_isUnit a).1 hau
  have hnb1 : (QuadraticAlgebra.norm b).natAbs ≠ 1 :=
    mt (natAbs_norm_eq_one_iff_isUnit b).1 hbu
  have hprod :
      (QuadraticAlgebra.norm a).natAbs *
        (QuadraticAlgebra.norm b).natAbs = p ^ 2 := by
    rw [← Int.natAbs_mul, ← map_mul, ← hpab]
    simp [QuadraticAlgebra.norm_natCast, Int.natAbs_pow]
  have hna : (QuadraticAlgebra.norm a).natAbs = p :=
    ((hp.mul_eq_prime_sq_iff hna1 hnb1).1 hprod).1
  refine ⟨a, ?_⟩
  have hna_cast : ((QuadraticAlgebra.norm a).natAbs : Int) = p := by
    exact_mod_cast hna
  rwa [Int.natAbs_of_nonneg (norm_nonneg a)] at hna_cast

/-- Prime-splitting theorem in the exact form consumed by the norm-shell count. -/
theorem split_prime_has_norm_witness
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1) :
    ∃ z : EisensteinQA, QuadraticAlgebra.norm z = p :=
  norm_witness_of_nat_prime_of_not_irreducible
    p hp (split_prime_not_irreducible p hp hmod)

/-- Coordinate form: every split prime is represented by
`a^2 - a*b + b^2`. -/
theorem split_prime_has_coordinate_witness
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1) :
    ∃ a b : Int, eisensteinNorm a b = p := by
  obtain ⟨z, hz⟩ := split_prime_has_norm_witness p hp hmod
  exact ⟨z.re, z.im, (norm_eq_coordinate_norm z).symm.trans hz⟩

structure EisensteinSplitPrimeBoundary where
  modThreeLegendreResiduePaid : Bool := true
  splitTestElementConstructed : Bool := true
  embeddedPrimeReducibilityPaid : Bool := true
  normPFactorExistencePaid : Bool := true
  coordinatePrimeRepresentationPaid : Bool := true
  primePowerRepresentationCountPaid : Bool := false
  globalRepresentationCountPaid : Bool := false

def canonicalBoundary : EisensteinSplitPrimeBoundary := {}

end Dashi.EisensteinSplitPrimeExact
