import Integration.EisensteinJZeroCanonicalCubicCharacterExact

/-!
RED-first regression for the split-prime cubic-character producer.

The intended owner pays exactly the finite-field step missing from the existing
Jacobi compiler:

* construct a distinguished order-three multiplicative character when
  `#F ≡ 1 (mod 3)`;
* prove that its kernel on nonzero field elements is exactly the cube image;
* prove the literal cube-fibre weighted reindexing identity;
* package the result as the existing `CubicCharacterCertificate`;
* specialize to `ZMod p` and weld the same split prime to the already-existing
  Eisenstein norm-p witness.

No Jacobi-sum evaluation as an Eisenstein prime and no Hecke character is
asserted here.
-/

namespace Integration.EisensteinJZeroCanonicalCubicCharacterRegression

open Integration.EisensteinJZeroCubicJacobiExact
open Integration.EisensteinJZeroCanonicalCubicCharacterExact
open Dashi.EisensteinQuadraticAlgebraExact

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

example (hq : Fintype.card F % 3 = 1) :
    orderOf (canonicalCubicCharacter (F := F) hq) = 3 :=
  canonicalCubicCharacter_order hq

example (hq : Fintype.card F % 3 = 1) {t : F} (ht : t ≠ 0) :
    canonicalCubicCharacter (F := F) hq t = 1 ↔ ∃ x : F, x ^ 3 = t :=
  canonicalCubicCharacter_eq_one_iff_cube hq ht

example (hq : Fintype.card F % 3 = 1) :
    CubicCharacterCertificate F :=
  canonicalCubicCharacterCertificate hq

example (p : Nat) [Fact p.Prime] (hp3 : p % 3 = 1) :
    CubicCharacterCertificate (ZMod p) :=
  splitPrimeCubicCharacterCertificate p hp3

example (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    SplitPrimeArithmeticJacobiWeld p :=
  splitPrimeArithmeticJacobiWeld p hp2 hp3

example (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    QuadraticAlgebra.norm (SplitPrimeArithmeticJacobiWeld.eisensteinFactor
      (splitPrimeArithmeticJacobiWeld p hp2 hp3)) = p :=
  SplitPrimeArithmeticJacobiWeld.eisensteinFactorNorm
    (splitPrimeArithmeticJacobiWeld p hp2 hp3)

end Integration.EisensteinJZeroCanonicalCubicCharacterRegression
