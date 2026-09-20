import Synthesis.MillenniumBSDGlobalCoefficientReconstruction
import Synthesis.MillenniumBSDGlobalEulerPrimePower
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-!
# Fully explicit coefficients of the literal global BSD L-function

The additive p=2 factor is now paid.  Therefore every prime-power coefficient
of the actual global WeierstrassCurve.LFunction is explicit, and unique
factorization reconstructs every coefficient with no opaque bad-prime lane.
-/

namespace Synthesis.Millennium.BSD

open ArithmeticFunction

noncomputable def explicitAllPrimePowerCoefficientNat
    (p k : ℕ) : ℤ :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    explicitAllPrimePowerCoefficient p k
  else 0

theorem explicitAllPrimePowerCoefficientNat_of_prime
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    explicitAllPrimePowerCoefficientNat p k =
      @explicitAllPrimePowerCoefficient p ⟨hp⟩ k := by
  simp [explicitAllPrimePowerCoefficientNat, hp]

noncomputable def cmFullyExplicitCoefficient
    (n : ℕ) : ℤ :=
  if n = 0 then 0
  else n.factorization.prod
    (fun p k => explicitAllPrimePowerCoefficientNat p k)

@[simp] theorem cmFullyExplicitCoefficient_zero :
    cmFullyExplicitCoefficient 0 = 0 := by
  simp [cmFullyExplicitCoefficient]

theorem cmAllNCoefficient_factorization_allPrime
    {n : ℕ} (hn : n ≠ 0) :
    cmAllNCoefficient n =
      n.factorization.prod
        (fun p k => explicitAllPrimePowerCoefficientNat p k) := by
  rw [cmAllNCoefficient_factorization hn]
  apply Finsupp.prod_congr
  intro p hpSupp
  have hfp : n.factorization p ≠ 0 :=
    Finsupp.mem_support_iff.mp hpSupp
  have hpdvd : p ∣ n := Nat.dvd_of_factorization_pos hfp
  have hp : p.Prime := Nat.prime_of_dvd_of_ne_one hpdvd
    (by
      intro hp1
      subst p
      simpa using hfp)
  letI : Fact p.Prime := ⟨hp⟩
  rw [cmAllNCoefficient_primePower]
  symm
  exact explicitAllPrimePowerCoefficientNat_of_prime hp _

theorem cmAllNCoefficient_eq_fullyExplicit
    (n : ℕ) :
    cmAllNCoefficient n = cmFullyExplicitCoefficient n := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [cmFullyExplicitCoefficient, if_neg hn]
  exact cmAllNCoefficient_factorization_allPrime hn

noncomputable def cmFullyExplicitArithmeticFunction :
    ArithmeticFunction ℤ :=
  ⟨cmFullyExplicitCoefficient, cmFullyExplicitCoefficient_zero⟩

theorem cmFullyExplicitArithmeticFunction_eq_cmFormalLFunction :
    cmFullyExplicitArithmeticFunction = cmFormalLFunction := by
  ext n
  exact (cmAllNCoefficient_eq_fullyExplicit n).symm

theorem cmFormalLFunction_eq_fullyExplicit :
    cmFormalLFunction = cmFullyExplicitArithmeticFunction :=
  cmFullyExplicitArithmeticFunction_eq_cmFormalLFunction.symm

noncomputable def cmFullyExplicitLSeries (s : ℂ) : ℂ :=
  LSeries ((↑) ∘ cmFullyExplicitCoefficient) s

theorem cmLSeries_eq_fullyExplicitLSeries
    (s : ℂ) :
    cmLSeries s = cmFullyExplicitLSeries s := by
  unfold cmLSeries WeierstrassCurve.LSeries cmFullyExplicitLSeries
  congr 2
  funext n
  rw [Function.comp_apply, Function.comp_apply]
  exact_mod_cast cmAllNCoefficient_eq_fullyExplicit n

theorem cmFullyExplicitCoefficient_twoPower
    (k : ℕ) :
    cmFullyExplicitCoefficient (2 ^ k) =
      if k = 0 then 1 else 0 := by
  rw [← cmAllNCoefficient_eq_fullyExplicit]
  exact cmAllNCoefficient_twoPower k

end Synthesis.Millennium.BSD
