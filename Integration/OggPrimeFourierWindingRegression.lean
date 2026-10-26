import Integration.OggPrimeFourierWinding

namespace Integration.OggPrimeFourierWindingRegression

open Integration.OggPrimeFourierWinding

example : oggPrimes.card = 15 := oggPrimes_card
example : nonOggPrimes.card = 5 := nonOggPrimes_card
example : contrastSum 0 = 0 := contrastSum_zero

example (ω : ℝ) (p : ℕ) :
    rotor (-ω) p = Complex.conj (rotor ω p) :=
  rotor_neg_eq_conj ω p

example {m k p q : ℕ}
    (h : phaseIndex m k p = phaseIndex m k q) :
    rootRotor m k p = rootRotor m k q :=
  rootRotor_depends_only_on_phaseIndex h

example : analyticIdentificationClaimed = false :=
  analyticIdentificationClaimed_false

end Integration.OggPrimeFourierWindingRegression
