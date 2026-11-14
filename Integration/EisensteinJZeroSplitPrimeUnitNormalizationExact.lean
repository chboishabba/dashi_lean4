import Integration.EisensteinJZeroSplitPrimeEisensteinCarrierExact
import Integration.EisensteinSixUnitOrbitExact
import Integration.EisensteinSplitPrimeExact

/-!
# Six-unit / split-choice normalization of the canonical split Jacobi element

The split Jacobi sum has already been pulled back to a literal
`EisensteinQA` element of norm `p`.  Earlier #69 machinery gives an exact
bijection

    six listed Eisenstein units × split exponent choices
      ≃
    positive norm-p fibre.

This file simply reuses that canonical equivalence.  No new arithmetic
classification is introduced: the Jacobi element is decoded into the existing
unit/choice code, paying the unit ambiguity and associate normalization by the
same owner used for every other represented Eisenstein norm.

Attribution: all six-unit/UFD/choice machinery is pre-existing DASHI/Lean #69
work.  This file owns only the specialization to the Jacobi element.
-/

namespace Integration.EisensteinJZeroSplitPrimeUnitNormalizationExact

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinRepresentationCriterionExact
open Dashi.EisensteinSplitPrimeExact
open Dashi.EisensteinSixUnitOrbitExact
open Integration.EisensteinJZeroSplitPrimeEisensteinCarrierExact

/-- Split primes satisfy the already-established inert-even representation
criterion.  This receipt is built from the existing norm-p split witness, not
from the Jacobi construction. -/
noncomputable def splitPrimeInertEven
    (p : Nat) [Fact p.Prime] (hp3 : p % 3 = 1) : InertEvenCondition p := by
  obtain ⟨z, hz⟩ := split_prime_has_norm_witness p Fact.out hp3
  exact (norm_representable_iff_inert_even p Fact.out.pos).1 ⟨z, hz⟩

/-- The unique six-unit × split-choice code of the canonical Jacobi pullback. -/
noncomputable def splitJacobiNormFiberCode
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    NormFiberCode p :=
  (normFiberCodeEquiv p (by omega) (splitPrimeInertEven p hp3)).symm
    ⟨splitJacobiEisensteinElement p hp2 hp3,
      splitJacobiEisensteinElement_norm p hp2 hp3⟩

/-- Decoding the canonical unit/choice code returns exactly the literal Jacobi
Eisenstein element. -/
theorem decode_splitJacobiNormFiberCode
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    (decodeNormFiberCode p (by omega) (splitPrimeInertEven p hp3)
      (splitJacobiNormFiberCode p hp2 hp3)).1 =
      splitJacobiEisensteinElement p hp2 hp3 := by
  have h := (normFiberCodeEquiv p (by omega)
    (splitPrimeInertEven p hp3)).apply_symm_apply
      ⟨splitJacobiEisensteinElement p hp2 hp3,
        splitJacobiEisensteinElement_norm p hp2 hp3⟩
  exact congrArg Subtype.val h

/-- The normalized unit is one of the repository's exact six units. -/
theorem splitJacobi_normalizedUnit_mem
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    (splitJacobiNormFiberCode p hp2 hp3).1.1 ∈
      Dashi.EisensteinSixUnitsExact.eisensteinUnits :=
  (splitJacobiNormFiberCode p hp2 hp3).1.2

/-- Explicit normal form: listed unit times the canonical split-choice
representative equals the Jacobi Eisenstein element. -/
theorem splitJacobi_unit_mul_choiceRepresentative
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    (splitJacobiNormFiberCode p hp2 hp3).1.1 *
        Dashi.EisensteinChoiceRepresentativeExact.choiceRepresentative
          p (splitPrimeInertEven p hp3)
          (splitJacobiNormFiberCode p hp2 hp3).2
      = splitJacobiEisensteinElement p hp2 hp3 := by
  exact decode_splitJacobiNormFiberCode p hp2 hp3

structure SplitPrimeUnitNormalizationBoundary where
  existingSixUnitOrbitReused : Bool := true
  existingSplitChoiceObserverReused : Bool := true
  jacobiElementUniqueNormFiberCodePaid : Bool := true
  listedUnitNormalizationPaid : Bool := true
  unitTimesCanonicalChoiceEqualityPaid : Bool := true
  externalHeckeCharacterUsed : Bool := false

/-- Machine-readable terminal normalization receipt. -/
def canonicalBoundary : SplitPrimeUnitNormalizationBoundary := {}

end Integration.EisensteinJZeroSplitPrimeUnitNormalizationExact
