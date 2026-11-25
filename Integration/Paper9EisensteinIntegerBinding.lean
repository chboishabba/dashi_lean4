import Integration.Paper9IntegerSectorWeld
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-! SOURCE-WRITTEN, UNCOMPILED.
Original E4/E6 Fourier streams via Birkbeck's pinned q_expansion_bernoulli
and qExpansion_coeff_unique, not a new analytic evaluator.
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

-- Reuse the actual shifted term and limit owners, rather than proving a
-- second summability theorem. The original source includes the zero term
-- separately; HasSum's finite-prefix reflection restores precisely that term.
theorem qOfTargetPeriodic (τ : ℍ) :
    Integration.MoonshineEisensteinAgdaTarget.qOfTarget τ=Periodic.qParam 1 τ := by
  rw [Integration.MoonshineEisensteinAgdaTarget.qOfTarget_eq_qParam]
  simp [Integration.MoonshineEisensteinAnalytic.qParam, Periodic.qParam]

theorem e4HasSum (τ : ℍ) :
    HasSum (fun n : ℕ => (e4Z n : ℂ) • Periodic.qParam 1 τ ^ n)
      (Integration.MoonshineEisensteinAnalytic.E4 τ) := by
  let f := fun n : ℕ => (e4Z n : ℂ) • Periodic.qParam 1 τ ^ n
  have hs : HasSum (fun n : ℕ => f (n+1))
      (∑' n : ℕ, Integration.MoonshineEisensteinAgdaTarget.e4Term τ n) := by
    convert (Integration.MoonshineEisensteinAgdaTarget.summable_e4Term τ).hasSum using 1
    funext n
    simp [f, e4Z, Integration.MoonshineEisensteinAgdaTarget.e4Term,
      Integration.MoonshineEisensteinAgdaTarget.scaleNatTarget,
      qOfTargetPeriodic, smul_eq_mul, mul_assoc]
  have h := (hasSum_nat_add_iff' 1).mp hs
  rw [← Integration.MoonshineEisensteinAgdaTarget.e4Limit_eq_mathlib_E4 τ]
  simpa [f, e4Z, Integration.MoonshineEisensteinAgdaTarget.e4Limit, add_comm] using h

theorem e6HasSum (τ : ℍ) :
    HasSum (fun n : ℕ => (e6Z n : ℂ) • Periodic.qParam 1 τ ^ n)
      (Integration.MoonshineEisensteinAnalytic.E6 τ) := by
  let f := fun n : ℕ => (e6Z n : ℂ) • Periodic.qParam 1 τ ^ n
  have hs : HasSum (fun n : ℕ => f (n+1))
      (-(∑' n : ℕ, Integration.MoonshineEisensteinAgdaTarget.e6Term τ n)) := by
    convert (Integration.MoonshineEisensteinAgdaTarget.summable_e6Term τ).hasSum.neg using 1
    funext n
    simp [f, e6Z, Integration.MoonshineEisensteinAgdaTarget.e6Term,
      Integration.MoonshineEisensteinAgdaTarget.scaleNatTarget,
      qOfTargetPeriodic, smul_eq_mul, mul_assoc, neg_mul]
  have h := (hasSum_nat_add_iff' 1).mp hs
  rw [← Integration.MoonshineEisensteinAgdaTarget.e6Limit_eq_mathlib_E6 τ]
  simpa [f, e6Z, Integration.MoonshineEisensteinAgdaTarget.e6Limit,
    sub_eq_add_neg, add_comm] using h

theorem e4Integer (n : ℕ) : E4PS.coeff n = (e4Z n : ℂ) := by
  symm
  unfold E4PS
  exact qExpansion_coeff_unique (h := 1) one_pos one_mem_strictPeriods_SL e4HasSum n

theorem e6Integer (n : ℕ) : E6PS.coeff n = (e6Z n : ℂ) := by
  symm
  unfold E6PS
  exact qExpansion_coeff_unique (h := 1) one_pos one_mem_strictPeriods_SL e6HasSum n

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
