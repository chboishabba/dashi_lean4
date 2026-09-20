import Synthesis.MillenniumBSDGlobalLocalFactorSameObject
import Synthesis.MillenniumBSDMathlibLFunctionWeld
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

/-!
# Extracting a single rational prime from the global Euler product

For Q, height-one places are equivalent to rational primes and their residue
cardinality is exactly that prime.  Hence at p^k every local factor away from
the unique p-place vanishes on positive p-powers and contributes only its
constant coefficient 1 to Dirichlet convolution.

This file turns the local same-object theorem into a theorem about the actual
global WeierstrassCurve.LFunction coefficients at odd prime powers.
-/

namespace Synthesis.Millennium.BSD

open ArithmeticFunction
open NumberField
open IsDedekindDomain
open Rat.HeightOneSpectrum
open Filter

noncomputable def rationalHeightOneNorm
    (v : HeightOneSpectrum (𝓞 ℚ)) : ℕ :=
  (Rat.HeightOneSpectrum.primesEquiv v).1

theorem rationalHeightOneNorm_prime
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Nat.Prime (rationalHeightOneNorm v) :=
  (Rat.HeightOneSpectrum.primesEquiv v).2

noncomputable def rationalHeightOneResidueEquivZMod
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)
      ≃+* ZMod (rationalHeightOneNorm v) :=
  (IsLocalRing.ResidueField.mapEquiv
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv).trans
    (padicResidueEquivZMod (rationalHeightOneNorm v))

theorem rationalHeightOneResidue_natCard
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))
      = rationalHeightOneNorm v := by
  rw [Nat.card_congr (rationalHeightOneResidueEquivZMod v).toEquiv]
  simp

instance rationalHeightOneNorm_northcott :
    Northcott rationalHeightOneNorm where
  finite_le b := by
    let e : HeightOneSpectrum (𝓞 ℚ) ↪ ℕ :=
      ⟨rationalHeightOneNorm, fun x y h => by
        apply Rat.HeightOneSpectrum.primesEquiv.injective
        apply Subtype.ext
        exact h⟩
    have hfin : ({n : ℕ | n ≤ b} : Set ℕ).Finite := Set.finite_le_nat b
    simpa [e, rationalHeightOneNorm] using
      hfin.preimage e.injective.injOn

noncomputable def cmHeightOneLocalFactor
    (v : HeightOneSpectrum (𝓞 ℚ)) : ArithmeticFunction ℤ :=
  (cmWeierstrass.baseChange (v.adicCompletion ℚ)).localEulerFactor
    (v.adicCompletionIntegers ℚ)

noncomputable def cmHeightOneLocalSeries
    (v : HeightOneSpectrum (𝓞 ℚ)) : PowerSeries ℤ :=
  (cmWeierstrass.baseChange (v.adicCompletion ℚ)).localPowerSeries
    (v.adicCompletionIntegers ℚ)

theorem cmHeightOneLocalFactor_eq_ofPowerSeries
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    cmHeightOneLocalFactor v =
      ArithmeticFunction.ofPowerSeries (rationalHeightOneNorm v)
        (cmHeightOneLocalSeries v) := by
  unfold cmHeightOneLocalFactor WeierstrassCurve.localEulerFactor
  rw [rationalHeightOneResidue_natCard]
  rfl

theorem cmHeightOneLocalSeries_constantCoeff
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    (cmHeightOneLocalSeries v).constantCoeff = 1 := by
  unfold cmHeightOneLocalSeries WeierstrassCurve.localPowerSeries
  simp

theorem distinct_prime_pow_ne
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (ha : a ≠ 0) (hb : b ≠ 0) :
    p ^ a ≠ q ^ b := by
  intro h
  have hpdiv : p ∣ q ^ b := by
    rw [← h]
    exact dvd_pow_self p ha
  have hpq' : p = q := hp.eq_of_dvd_of_prime hq (hq.dvd_of_dvd_pow hpdiv)
  exact hpq hpq'

theorem cmHeightOneLocalFactor_off_prime_pow
    {p : ℕ} (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : rationalHeightOneNorm v ≠ p)
    {k : ℕ} (hk : k ≠ 0) :
    cmHeightOneLocalFactor v (p ^ k) = 0 := by
  rw [cmHeightOneLocalFactor_eq_ofPowerSeries]
  rw [ArithmeticFunction.ofPowerSeries_apply
    (rationalHeightOneNorm_prime v).one_lt]
  rw [Function.extend_apply']
  · rfl
  · rintro ⟨j, hj⟩
    by_cases hj0 : j = 0
    · subst j
      simp at hj
      exact (hp.one_lt.pow_pos hk).ne' hj.symm
    exact distinct_prime_pow_ne
      (rationalHeightOneNorm_prime v) hp hv hj0 hk hj

theorem cmHeightOneLocalFactor_one
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    cmHeightOneLocalFactor v 1 = 1 := by
  rw [cmHeightOneLocalFactor_eq_ofPowerSeries]
  simpa [cmHeightOneLocalSeries_constantCoeff]

theorem mul_apply_prime_pow_right_delta
    (f g : ArithmeticFunction ℤ)
    {p k : ℕ} (hp : p.Prime)
    (hg1 : g 1 = 1)
    (hg : ∀ j : ℕ, j ≠ 0 → g (p ^ j) = 0) :
    (f * g) (p ^ k) = f (p ^ k) := by
  rw [ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal fun a b => f a * g b]
  rw [Nat.sum_divisors_prime_pow hp]
  rw [Finset.sum_eq_single k]
  · simp [hg1]
  · intro j hj hjk
    have hjle : j ≤ k := by simpa using Finset.mem_range.mp hj
    have hsub : k - j ≠ 0 := by omega
    simp [Nat.pow_sub_div_pow hp.ne_zero hjle, hg (k-j) hsub]
  · simp

theorem mul_apply_prime_pow_left_delta
    (f g : ArithmeticFunction ℤ)
    {p k : ℕ} (hp : p.Prime)
    (hf1 : f 1 = 1)
    (hf : ∀ j : ℕ, j ≠ 0 → f (p ^ j) = 0) :
    (f * g) (p ^ k) = g (p ^ k) := by
  rw [mul_comm]
  exact mul_apply_prime_pow_right_delta g f hp hf1 hf

theorem cmFiniteLocalProduct_primePower
    {p : ℕ} (hp : p.Prime)
    (s : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (k : ℕ) :
    (∏ v ∈ s, cmHeightOneLocalFactor v) (p ^ k)
      = if rationalPrimePlace p ∈ s then
          cmHeightOneLocalFactor (rationalPrimePlace p) (p ^ k)
        else if k = 0 then 1 else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      by_cases hk : k = 0
      · subst k; simp
      · simp [hk, hp.ne_zero]
  | @insert v s hv ih =>
      simp only [Finset.prod_insert hv]
      by_cases hvp : v = rationalPrimePlace p
      · subst v
        have hnorm : rationalHeightOneNorm (rationalPrimePlace p) = p := by
          simp [rationalHeightOneNorm, rationalPrimePlace]
        by_cases hmem : rationalPrimePlace p ∈ s
        · simp [hmem]
        · rw [ih]
          simp [hmem]
          by_cases hk : k = 0
          · subst k; simp [cmHeightOneLocalFactor_one]
          · apply mul_apply_prime_pow_left_delta
              (cmHeightOneLocalFactor (rationalPrimePlace p))
              (∏ v ∈ s, cmHeightOneLocalFactor v) hp
            · simpa [hmem] using
                (show (∏ v ∈ s, cmHeightOneLocalFactor v) 1 = 1 by
                  induction s using Finset.induction_on <;>
                    simp [cmHeightOneLocalFactor_one, *])
            · intro j hj
              rw [ih]
              simp [hmem, hj]
      · have hnorm_ne : rationalHeightOneNorm v ≠ p := by
          intro hnorm
          apply hvp
          apply Rat.HeightOneSpectrum.primesEquiv.injective
          apply Subtype.ext
          simpa [rationalHeightOneNorm, rationalPrimePlace] using hnorm
        rw [ih]
        by_cases hmem : rationalPrimePlace p ∈ s
        · simp [hmem]
          exact mul_apply_prime_pow_right_delta
            (cmHeightOneLocalFactor (rationalPrimePlace p))
            (cmHeightOneLocalFactor v) hp
            (cmHeightOneLocalFactor_one v)
            (fun j hj => cmHeightOneLocalFactor_off_prime_pow hp v hnorm_ne hj)
        · by_cases hk : k = 0
          · subst k
            simp [hmem, cmHeightOneLocalFactor_one]
          · simp [hmem, hk]
            rw [mul_apply_prime_pow_right_delta
              (∏ x ∈ s, cmHeightOneLocalFactor x)
              (cmHeightOneLocalFactor v) hp
              (cmHeightOneLocalFactor_one v)
              (fun j hj => cmHeightOneLocalFactor_off_prime_pow hp v hnorm_ne hj)]
            rw [ih]
            simp [hmem, hk]

theorem cmEulerProduct_primePower
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ArithmeticFunction.eulerProduct cmHeightOneLocalFactor (p ^ k)
      = cmHeightOneLocalFactor (rationalPrimePlace p) (p ^ k) := by
  classical
  have hev := ArithmeticFunction.tendsTo_eulerProduct_ofPowerSeries
    rationalHeightOneNorm cmHeightOneLocalSeries
    cmHeightOneLocalSeries_constantCoeff (p ^ k)
  filter_upwards [hev] with s hs
  rw [← hs]
  have hs' :
      (∏ v ∈ (insert (rationalPrimePlace p) s), cmHeightOneLocalFactor v) (p ^ k)
        = ArithmeticFunction.eulerProduct cmHeightOneLocalFactor (p ^ k) := by
    exact (Filter.Eventually.of_forall fun _ => rfl)
  rw [cmFiniteLocalProduct_primePower hp]
  simp

theorem cmFormalLFunction_eq_heightOneEulerProduct :
    cmFormalLFunction = ArithmeticFunction.eulerProduct cmHeightOneLocalFactor := by
  rfl

theorem cmFormalLFunction_primePower
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    cmFormalLFunction (p ^ k)
      = cmHeightOneLocalFactor (rationalPrimePlace p) (p ^ k) := by
  rw [cmFormalLFunction_eq_heightOneEulerProduct]
  exact cmEulerProduct_primePower hp k

theorem cmAllNCoefficient_odd_primePower
    {p : ℕ} [Fact hp : p.Prime]
    (hp2 : p ≠ 2) (k : ℕ) :
    cmAllNCoefficient (p ^ k) = explicitPrimePowerCoefficient p k := by
  unfold cmAllNCoefficient
  rw [cmFormalLFunction_primePower hp.out k]
  exact globalHeightOne_localEulerFactor_primePower hp2 k

end Synthesis.Millennium.BSD
