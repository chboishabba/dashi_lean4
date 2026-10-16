import Integration.EisensteinJZeroCubicCharacterCertificateExact

namespace Integration.EisensteinJZeroCubicCharacterCertificateValidation

open Integration.EisensteinJZeroCubicJacobiExact
open Integration.EisensteinJZeroCubicCharacterCertificateExact

example (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1)
    (ψ : MulChar (ZMod p) ℂ) (hψ : orderOf ψ = 3) :
    cubeSubgroup p = ψ.toUnitHom.ker :=
  cubeSubgroup_eq_orderThreeCharacterKernel p hmod ψ hψ

example (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1)
    (ψ : MulChar (ZMod p) ℂ) (hψ : orderOf ψ = 3)
    (f : ZMod p → ℂ) :
    (∑ x : ZMod p, f (x ^ 3)) =
      ∑ t : ZMod p, (1 + ψ t + (ψ * ψ) t) * f t :=
  cubeWeightedReindex_of_orderThree p hmod ψ hψ f

example (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    CubicCharacterCertificate (ZMod p) :=
  splitPrimeCubicCharacterCertificate p hmod

example (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    ((Integration.EisensteinJZeroFiniteFieldTraceExact.jZeroFrobeniusTraceInt (ZMod p) : Int) : ℂ) =
      -(jacobiSum (splitPrimeCubicCharacterCertificate p hmod).character quadraticCharComplex
        + jacobiSum
            ((splitPrimeCubicCharacterCertificate p hmod).character *
              (splitPrimeCubicCharacterCertificate p hmod).character)
            quadraticCharComplex) :=
  splitPrime_jZeroTrace_eq_unweightedJacobiPair p hmod

end Integration.EisensteinJZeroCubicCharacterCertificateValidation
