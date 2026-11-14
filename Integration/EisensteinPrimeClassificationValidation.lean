import Integration.EisensteinPrimeClassificationExact

namespace Dashi.EisensteinPrimeClassificationValidation

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinPrimeClassificationExact

/-- Inert residue-class primes remain irreducible in the Eisenstein UFD. -/
example (p : Nat) (hp : p.Prime) (hmod : p % 3 = 2) :
    Irreducible (p : EisensteinQA) :=
  inert_prime_irreducible p hp hmod

/-- Split residue-class primes are reducible. -/
example (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1) :
    ¬ Irreducible (p : EisensteinQA) :=
  split_prime_reducible p hp hmod

example : Irreducible (2 : EisensteinQA) :=
  inert_prime_irreducible 2 (by norm_num) (by norm_num)

end Dashi.EisensteinPrimeClassificationValidation
