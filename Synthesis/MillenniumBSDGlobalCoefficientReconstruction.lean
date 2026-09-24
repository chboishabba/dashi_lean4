import Synthesis.MillenniumBSDGlobalEulerPrimePower
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-!
# Reconstructing every global L-function coefficient

The global arithmetic function is multiplicative.  Odd prime powers have now
been identified with the explicit recurrence A_p(k).  Therefore every
coefficient is reconstructed from its prime factorization, with the entire
remaining bad-prime ambiguity concentrated in the single sequence a_{2^k}.
-/

namespace Synthesis.Millennium.BSD

open ArithmeticFunction

noncomputable def explicitPrimePowerCoefficientNat
    (p k : ℕ) : ℤ :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    explicitPrimePowerCoefficient p k
  else 0

theorem explicitPrimePowerCoefficientNat_of_prime
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    explicitPrimePowerCoefficientNat p k =
      @explicitPrimePowerCoefficient p ⟨hp⟩ k := by
  simp [explicitPrimePowerCoefficientNat, hp]

noncomputable def cmBadTwoPrimePowerCoefficient
    (k : ℕ) : ℤ :=
  cmAllNCoefficient (2 ^ k)

noncomputable def cmReconstructedPrimePowerCoefficient
    (p k : ℕ) : ℤ :=
  if p = 2 then cmBadTwoPrimePowerCoefficient k
  else explicitPrimePowerCoefficientNat p k

theorem cmReconstructedPrimePowerCoefficient_of_odd_prime
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    cmReconstructedPrimePowerCoefficient p k =
      @explicitPrimePowerCoefficient p ⟨hp⟩ k := by
  simp [cmReconstructedPrimePowerCoefficient, hp2,
    explicitPrimePowerCoefficientNat, hp]

theorem cmReconstructedPrimePowerCoefficient_two
    (k : ℕ) :
    cmReconstructedPrimePowerCoefficient 2 k =
      cmAllNCoefficient (2 ^ k) := by
  simp [cmReconstructedPrimePowerCoefficient,
    cmBadTwoPrimePowerCoefficient]

noncomputable def cmExplicitReconstructedCoefficient
    (n : ℕ) : ℤ :=
  if n = 0 then 0
  else n.factorization.prod
    (fun p k => cmReconstructedPrimePowerCoefficient p k)

@[simp] theorem cmExplicitReconstructedCoefficient_zero :
    cmExplicitReconstructedCoefficient 0 = 0 := by
  simp [cmExplicitReconstructedCoefficient]

theorem cmAllNCoefficient_factorization
    {n : ℕ} (hn : n ≠ 0) :
    cmAllNCoefficient n =
      n.factorization.prod
        (fun p k => cmAllNCoefficient (p ^ k)) := by
  exact cmFormalLFunction_isMultiplicative.multiplicative_factorization
    cmFormalLFunction n hn

theorem cmAllNCoefficient_primePower_reconstructed
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    cmAllNCoefficient (p ^ k) =
      cmReconstructedPrimePowerCoefficient p k := by
  by_cases hp2 : p = 2
  · subst p
    symm
    exact cmReconstructedPrimePowerCoefficient_two k
  · letI : Fact p.Prime := ⟨hp⟩
    rw [cmAllNCoefficient_odd_primePower hp2 k]
    symm
    exact cmReconstructedPrimePowerCoefficient_of_odd_prime hp hp2 k

theorem cmAllNCoefficient_eq_reconstructed
    (n : ℕ) :
    cmAllNCoefficient n = cmExplicitReconstructedCoefficient n := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [cmExplicitReconstructedCoefficient, if_neg hn]
  rw [cmAllNCoefficient_factorization hn]
  apply Finsupp.prod_congr
  intro p hpSupp
  have hp : p.Prime := Nat.prime_of_mem_primeFactors
    (Nat.mem_primeFactors.mpr ⟨hn, Nat.dvd_of_factorization_pos
      (Finsupp.mem_support_iff.mp hpSupp)⟩)
  exact cmAllNCoefficient_primePower_reconstructed hp _

theorem cmAllNCoefficient_odd_factorization
    {n : ℕ} (hn0 : n ≠ 0) (hnodd : Odd n) :
    cmAllNCoefficient n =
      n.factorization.prod
        (fun p k => explicitPrimePowerCoefficientNat p k) := by
  rw [cmAllNCoefficient_factorization hn0]
  apply Finsupp.prod_congr
  intro p hpSupp
  have hfp : n.factorization p ≠ 0 :=
    Finsupp.mem_support_iff.mp hpSupp
  have hpdvd : p ∣ n := Nat.dvd_of_factorization_pos hfp
  have hp : p.Prime := Nat.prime_of_dvd_of_ne_one hpdvd
    (by intro hp1; subst p; simpa using hfp)
  have hp2 : p ≠ 2 := by
    intro hpEq
    subst p
    exact hnodd.not_two_dvd_nat hpdvd
  letI : Fact p.Prime := ⟨hp⟩
  rw [cmAllNCoefficient_odd_primePower hp2]
  symm
  exact explicitPrimePowerCoefficientNat_of_prime hp _

noncomputable def cmReconstructedArithmeticFunction :
    ArithmeticFunction ℤ :=
  ⟨cmExplicitReconstructedCoefficient,
    cmExplicitReconstructedCoefficient_zero⟩

theorem cmReconstructedArithmeticFunction_eq_cmFormalLFunction :
    cmReconstructedArithmeticFunction = cmFormalLFunction := by
  ext n
  exact (cmAllNCoefficient_eq_reconstructed n).symm

theorem cmFormalLFunction_eq_reconstructed :
    cmFormalLFunction = cmReconstructedArithmeticFunction :=
  cmReconstructedArithmeticFunction_eq_cmFormalLFunction.symm

noncomputable def cmReconstructedLSeries (s : ℂ) : ℂ :=
  LSeries ((↑) ∘ cmExplicitReconstructedCoefficient) s

theorem cmLSeries_eq_reconstructedLSeries
    (s : ℂ) :
    cmLSeries s = cmReconstructedLSeries s := by
  unfold cmLSeries WeierstrassCurve.LSeries cmReconstructedLSeries
  congr 2
  funext n
  rw [Function.comp_apply, Function.comp_apply]
  exact_mod_cast cmAllNCoefficient_eq_reconstructed n

end Synthesis.Millennium.BSD
