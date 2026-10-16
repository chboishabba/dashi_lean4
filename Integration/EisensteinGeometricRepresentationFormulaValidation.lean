import Integration.EisensteinGeometricRepresentationFormulaExact

namespace Dashi.EisensteinGeometricRepresentationFormulaValidation

open Dashi.EisensteinLatticeCounting
open Dashi.EisensteinGeometricRepresentationFormulaExact

example (n : Nat) :
    (geometricNormShellCount (n + 1) : Int)
      = signedEisensteinDivisorShellCount (n + 1) :=
  geometricNormShell_eq_signedDivisorShell_positive n

example : SignedEisensteinNormRepresentationBridge :=
  canonicalSignedEisensteinNormRepresentationBridge

end Dashi.EisensteinGeometricRepresentationFormulaValidation
