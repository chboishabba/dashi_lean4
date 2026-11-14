import Integration.EisensteinSplitPrimeExact

namespace Dashi.EisensteinPrimeNormIrreducibleExact

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinEuclideanDomainExact
open Dashi.EisensteinSplitPrimeExact

/-- A nonzero Eisenstein element whose positive norm is a rational prime is
irreducible.  Any factorization would factor that prime into two nonnegative
integer norms, forcing one factor to have norm one and hence be a unit. -/
theorem irreducible_of_norm_nat_prime
    (z : EisensteinQA) (p : Nat) (hp : p.Prime)
    (hz : QuadraticAlgebra.norm z = p) :
    Irreducible z := by
  rw [irreducible_iff]
  constructor
  · intro hu
    have hunitNorm := (isUnit_iff_norm_eq_one z).1 hu
    rw [hz] at hunitNorm
    exact hp.ne_one (by exact_mod_cast hunitNorm)
  · intro a b hab
    have hnormProd :
        QuadraticAlgebra.norm a * QuadraticAlgebra.norm b = p := by
      rw [← map_mul, ← hab, hz]
    have hnatProd :
        (QuadraticAlgebra.norm a).natAbs *
          (QuadraticAlgebra.norm b).natAbs = p := by
      rw [← Int.natAbs_mul, hnormProd]
      simp
    have haDvd : (QuadraticAlgebra.norm a).natAbs ∣ p :=
      ⟨(QuadraticAlgebra.norm b).natAbs, hnatProd.symm⟩
    rcases hp.eq_one_or_self_of_dvd _ haDvd with haOne | haPrime
    · exact Or.inl ((natAbs_norm_eq_one_iff_isUnit a).1 haOne)
    · have hbOne : (QuadraticAlgebra.norm b).natAbs = 1 := by
        rw [haPrime] at hnatProd
        exact Nat.eq_of_mul_eq_mul_left hp.pos hnatProd
      exact Or.inr ((natAbs_norm_eq_one_iff_isUnit b).1 hbOne)

/-- In particular every selected factor above a split rational prime is
irreducible. -/
theorem splitPrimeRepresentative_irreducible
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1)
    (z : EisensteinQA)
    (hz : QuadraticAlgebra.norm z = p) :
    Irreducible z :=
  irreducible_of_norm_nat_prime z p hp hz

end Dashi.EisensteinPrimeNormIrreducibleExact
