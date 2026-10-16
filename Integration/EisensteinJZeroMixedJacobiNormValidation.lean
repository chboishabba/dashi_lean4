import Integration.EisensteinJZeroMixedJacobiNormExact

namespace Integration.EisensteinJZeroMixedJacobiNormValidation

open Integration.EisensteinJZeroCubicJacobiExact
open Integration.EisensteinJZeroCubicCharacterCertificateExact
open Integration.EisensteinJZeroMixedJacobiNormExact

example (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    star (splitPrimeMixedJacobi p hmod) =
      jacobiSum
        ((splitPrimeCubicCharacterCertificate p hmod).character *
          (splitPrimeCubicCharacterCertificate p hmod).character)
        quadraticCharComplex :=
  splitPrimeMixedJacobi_conj p hmod

example (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    splitPrimeMixedJacobi p hmod * star (splitPrimeMixedJacobi p hmod) = (p : ℂ) :=
  splitPrimeMixedJacobi_normSq p hmod

example (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    ((Integration.EisensteinJZeroFiniteFieldTraceExact.jZeroFrobeniusTraceInt (ZMod p) : Int) : ℂ) =
      -(2 : ℂ) * (splitPrimeMixedJacobi p hmod).re :=
  splitPrimeFrobeniusTrace_eq_neg_two_re_mixedJacobi p hmod

end Integration.EisensteinJZeroMixedJacobiNormValidation
