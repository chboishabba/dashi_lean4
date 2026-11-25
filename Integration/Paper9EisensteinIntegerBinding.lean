import Integration.Paper9IntegerSectorWeld
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-! SOURCE-WRITTEN, UNCOMPILED.
Original E4/E6 Fourier streams via Birkbeck's pinned q_expansion_bernoulli
and ModularFormClass.qExpansion_coeff_unique, not a new analytic evaluator.
Keep the zero mode and the signed 1728 residual. -/
namespace Integration.Paper9EisensteinIntegerBinding

open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass
open ArithmeticFunction
open scoped BigOperators ArithmeticFunction.sigma
open Integration.Paper9OriginalEisensteinDerivative
open Integration.Paper9DiscriminantUnitReflection

-- Exactly the divisor streams of check_cm163_junit_discriminant_reflection.py:
-- no extra contribution at the zero index.
def e4Z (n : ℕ) : ℤ := if n = 0 then 1 else 240 * (sigma 3 n : ℤ)
def e6Z (n : ℕ) : ℤ := if n = 0 then 1 else -504 * (sigma 5 n : ℤ)

theorem sigmaBound (k n : ℕ) : sigma k n ≤ n^(k+1) := by
  rw [ArithmeticFunction.sigma_apply]
  calc
    _ ≤ ∑ d ∈ n.divisors, n^k := by
      apply Finset.sum_le_sum
      intro d hd
      exact Nat.pow_le_pow_left (Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors hd))
        (Nat.dvd_of_mem_divisors hd)) _
    _ = n.divisors.card * n^k := by simp
    _ ≤ n^(k+1) := by
      rw [pow_succ, mul_comm (n^k)]
      exact Nat.mul_le_mul_right _ (Nat.card_divisors_le_self n)

-- Use a polynomial-geometric majorant on the actual q disk.
theorem sigmaSummable (k : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => (sigma k n : ℂ)*q^n) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_norm_pow_mul_geometric_of_norm_lt_one (k+1) hq)
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast sigmaBound k n) (by positivity)

-- The pinned Eisenstein theorem is in positive-natural coordinates.
-- Split off the original constant coefficient, using sigma(k,0)=0.
theorem divisorSeries (k : ℕ) (a q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (if n=0 then 1 else a*(sigma k n : ℂ))*q^n)
      (1+a*∑' n : ℕ+, (sigma k n : ℂ)*q^(n:ℕ)) := by
  have hs := (sigmaSummable k q hq).hasSum
  have hz : (∑' n : ℕ, (sigma k n : ℂ)*q^n) =
      ∑' n : ℕ+, (sigma k n : ℂ)*q^(n:ℕ) := by
    rw [← tsum_zero_pnat_eq_tsum_nat (sigmaSummable k q hq)]
    simp
  have ha := hs.mul_left a
  have hsingle := hasSum_ite_eq (0 : ℕ) (1 : ℂ)
  have hsum := hsingle.add ha
  rw [hz] at hsum
  convert hsum using 1
  · funext n
    by_cases hn : n=0
    · subst n; simp
    · simp [hn, mul_assoc]
  · rfl

-- Actual all-index coefficient statements, via the original modular forms.
theorem e4Integer (n : ℕ) : E4PS.coeff n = (e4Z n : ℂ) := by
  symm
  apply ModularFormClass.qExpansion_coeff_unique (h := 1) one_pos one_mem_strictPeriods_SL
  intro τ
  have h := divisorSeries 3 240 (Periodic.qParam 1 τ)
    (by simpa [Periodic.qParam] using Complex.norm_exp_two_pi_I_lt_one τ)
  have he := EisensteinSeries.q_expansion_bernoulli (k := 4)
    (by norm_num) (by norm_num) τ
  norm_num [show bernoulli 4 = -1 / 30 by decide +kernel] at he
  simpa [E4PS, e4Z, Integration.MoonshineEisensteinAnalytic.E4, Periodic.qParam,
    smul_eq_mul, zpow_natCast, sub_eq_add_neg] using (he ▸ h)

theorem e6Integer (n : ℕ) : E6PS.coeff n = (e6Z n : ℂ) := by
  symm
  apply ModularFormClass.qExpansion_coeff_unique (h := 1) one_pos one_mem_strictPeriods_SL
  intro τ
  have h := divisorSeries 5 (-504) (Periodic.qParam 1 τ)
    (by simpa [Periodic.qParam] using Complex.norm_exp_two_pi_I_lt_one τ)
  have he := EisensteinSeries.q_expansion_bernoulli (k := 6)
    (by norm_num) (by norm_num) τ
  norm_num [show bernoulli 6 = 1 / 42 by decide +kernel] at he
  simpa [E6PS, e6Z, Integration.MoonshineEisensteinAnalytic.E6, Periodic.qParam,
    smul_eq_mul, zpow_natCast, sub_eq_add_neg] using (he ▸ h)

def e4PSZ : PowerSeries ℤ := PowerSeries.mk e4Z
def e6PSZ : PowerSeries ℤ := PowerSeries.mk e6Z

theorem e4Map : PowerSeries.map (Int.castRingHom ℂ) e4PSZ = E4PS := by
  ext n
  simp [e4PSZ, PowerSeries.coeff_map, e4Integer]

theorem e6Map : PowerSeries.map (Int.castRingHom ℂ) e6PSZ = E6PS := by
  ext n
  simp [e6PSZ, PowerSeries.coeff_map, e6Integer]

-- Any finite certificate for the original shifted discriminant must
-- retain exact signed residuals, not rounded integer division.
theorem uIntegerPrefix (D : ℕ) (u : PowerSeries ℤ)
    (hu : ∀ n≤D, 1728*u.coeff n =
      (e4PSZ^3-e6PSZ^2).coeff (n+1)) :
    ∀ n≤D, U.coeff n = (u.coeff n : ℂ) := by
  intro n hn
  have h := congrArg (fun x : ℤ => (x : ℂ)) (hu n hn)
  push_cast at h
  have hm : ((e4PSZ^3-e6PSZ^2).coeff (n+1) : ℂ) =
      (E4PS^3-E6PS^2).coeff (n+1) := by
    rw [← e4Map, ← e6Map, ← map_pow, ← map_pow, ← map_sub, PowerSeries.coeff_map]
    rfl
  rw [hm] at h
  rw [UCoefficient, ← h]
  ring

-- Finite triangular uniqueness without inventing an inverse stream:
-- the term (0,n) is the only term carrying the unknown n-th coefficient.
theorem quotientPrefixUnique (D : ℕ) (V A B : PowerSeries ℂ)
    (hv : V.coeff 0=1)
    (h : ∀ n≤D, (V*A).coeff n=(V*B).coeff n) :
    ∀ n≤D, A.coeff n=B.coeff n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have he := h n hn
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul] at he
    have hm : (0,n) ∈ Finset.Nat.antidiagonal n := by simp
    rw [← Finset.add_sum_erase _ _ hm, ← Finset.add_sum_erase _ _ hm] at he
    have hs : (∑ ij ∈ (Finset.Nat.antidiagonal n).erase (0,n),
        V.coeff ij.1*A.coeff ij.2) =
      ∑ ij ∈ (Finset.Nat.antidiagonal n).erase (0,n),
        V.coeff ij.1*B.coeff ij.2 := by
      apply Finset.sum_congr rfl
      intro ij hij
      have hmem := Finset.mem_erase.mp hij
      have hadd := Finset.Nat.mem_antidiagonal.mp hmem.2
      have hpos : 0<ij.1 := by
        by_contra hh
        have hzero : ij.1=0 := by omega
        apply hmem.1
        exact Prod.ext hzero (by omega)
      rw [ih ij.2 (by omega) (by omega)]
    simp only [hv, one_mul] at he
    rw [hs] at he
    exact add_right_cancel he

-- Exact actual J prefix from the two finite signed residual families.
-- The remaining executable checker must establish hu and hj on the
-- original integer arrays; these are not supplied by a receipt hash.
theorem jIntegerPrefix (D : ℕ) (u j : PowerSeries ℤ)
    (hu : ∀ n≤D, 1728*u.coeff n =
      (e4PSZ^3-e6PSZ^2).coeff (n+1))
    (hj : ∀ n≤D, (u*j).coeff n=(e4PSZ^3).coeff n) :
    ∀ n≤D, J.coeff n=(j.coeff n : ℂ) := by
  let jC := PowerSeries.map (Int.castRingHom ℂ) j
  have hU : U.coeff 0=1 := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using UZero
  have h := quotientPrefixUnique D U J jC hU (by
    intro n hn
    rw [JRelation, PowerSeries.coeff_mul]
    have hc : (∑ ij ∈ Finset.Nat.antidiagonal n,
        U.coeff ij.1*jC.coeff ij.2) =
      (PowerSeries.map (Int.castRingHom ℂ) (u*j)).coeff n := by
      rw [map_mul, PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro ij hij
      have he := Finset.Nat.mem_antidiagonal.mp hij
      rw [uIntegerPrefix D u hu ij.1 (by omega), PowerSeries.coeff_map]
      rfl
    rw [hc, PowerSeries.coeff_map, hj n hn, ← e4Map, ← map_pow, PowerSeries.coeff_map])
  intro n hn
  simpa [jC, PowerSeries.coeff_map] using h n hn

end Integration.Paper9EisensteinIntegerBinding
