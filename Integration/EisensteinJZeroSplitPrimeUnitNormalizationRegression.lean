import Integration.EisensteinJZeroSplitPrimeUnitNormalizationExact

/-! RED-first regression for six-unit / split-choice normalization of the
literal Jacobi Eisenstein element. -/

namespace Integration.EisensteinJZeroSplitPrimeUnitNormalizationRegression

open Dashi.EisensteinSixUnitOrbitExact
open Integration.EisensteinJZeroSplitPrimeUnitNormalizationExact

example (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    NormFiberCode p := splitJacobiNormFiberCode p hp2 hp3

example (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    (decodeNormFiberCode p (by omega) (splitPrimeInertEven p hp3)
      (splitJacobiNormFiberCode p hp2 hp3)).1 =
      Integration.EisensteinJZeroSplitPrimeEisensteinCarrierExact.splitJacobiEisensteinElement
        p hp2 hp3 :=
  decode_splitJacobiNormFiberCode p hp2 hp3

end Integration.EisensteinJZeroSplitPrimeUnitNormalizationRegression
