import Synthesis.MillenniumBSDGlobalAnalyticEulerWeld
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# Coarse global coefficient growth and prime-to-2 Dirichlet convergence

The elementary point-count bound |a_p| <= p gives a deliberately coarse
prime-power estimate |A_p(k)| <= (2p)^k.  For odd n, multiplicativity then
gives |a_n| <= n^2.  This is enough to prove absolute convergence of the
prime-to-2 Dirichlet series for Re(s) > 3, entirely from already formalized
input and without Hasse's theorem.
-/

namespace Synthesis.Millennium.BSD

theorem explicitPrimePowerCoefficient_abs_le_twoPrimePow
    {p : ℕ} [Fact hp : p.Prime]
    (hp2 : p ≠ 2) :
    ∀ k : ℕ,
      |explicitPrimePowerCoefficient p k|
        ≤ ((2 * p : ℕ) ^ k : ℤ) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => simp [explicitPrimePowerCoefficient]
  | one =>
      simpa [explicitPrimePowerCoefficient] using
        frobeniusCoefficient_abs_le_prime hp2
  | more k hk hk1 =>
      rw [explicitPrimePowerCoefficient_recurrence]
      calc
        |frobeniusCoefficient p * explicitPrimePowerCoefficient p (k+1)
            - (p : ℤ) * explicitPrimePowerCoefficient p k|
          ≤ |frobeniusCoefficient p|
              * |explicitPrimePowerCoefficient p (k+1)|
            + (p : ℤ) * |explicitPrimePowerCoefficient p k| := by
              simpa [abs_mul] using
                abs_sub_le
                  (frobeniusCoefficient p * explicitPrimePowerCoefficient p (k+1))
                  ((p : ℤ) * explicitPrimePowerCoefficient p k)
        _ ≤ (p : ℤ) * ((2*p : ℕ)^(k+1) : ℤ)
            + (p : ℤ) * ((2*p : ℕ)^k : ℤ) := by
              gcongr
              · exact frobeniusCoefficient_abs_le_prime hp2
              · exact hk1
              · positivity
              · exact hk
        _ ≤ ((2*p : ℕ)^(k+2) : ℤ) := by
              have hp2le : 2 ≤ p := hp.out.two_le
              norm_num [Nat.cast_pow]
              nlinarith [show (0 : ℤ) ≤ (2*p : ℕ)^k by positivity]

theorem explicitPrimePowerCoefficient_abs_le_primePow_sq
    {p : ℕ} [Fact hp : p.Prime]
    (hp2 : p ≠ 2) (k : ℕ) :
    |explicitPrimePowerCoefficient p k|
      ≤ ((p ^ k : ℕ) : ℤ) ^ 2 := by
  calc
    |explicitPrimePowerCoefficient p k|
      ≤ ((2*p : ℕ)^k : ℤ) :=
        explicitPrimePowerCoefficient_abs_le_twoPrimePow hp2 k
    _ ≤ ((p^2 : ℕ)^k : ℤ) := by
      exact_mod_cast Nat.pow_le_pow_left
        (by nlinarith [hp.out.two_le] : 2*p ≤ p^2) k
    _ = ((p^k : ℕ) : ℤ)^2 := by
      push_cast
      ring

theorem cmAllNCoefficient_abs_le_sq_of_odd :
    ∀ n : ℕ, Odd n →
      |cmAllNCoefficient n| ≤ ((n : ℤ) ^ 2) := by
  intro n
  induction n using Nat.recOnPrimeCoprime with
  | zero =>
      intro hodd
      exact (Nat.not_odd_zero hodd).elim
  | prime_pow p k hp =>
      intro hodd
      by_cases hk0 : k = 0
      · subst k
        simp [cmAllNCoefficient_one]
      by_cases hp2 : p = 2
      · subst p
        exfalso
        apply hodd.not_two_dvd_nat
        exact dvd_pow_self 2 hk0
      · letI : Fact p.Prime := ⟨hp⟩
        rw [cmAllNCoefficient_odd_primePower hp2 k]
        exact explicitPrimePowerCoefficient_abs_le_primePow_sq hp2 k
  | coprime a b ha hb hab hia hib =>
      intro hodd
      have hoa : Odd a := by
        exact (Nat.odd_mul.mp hodd).1
      have hob : Odd b := by
        exact (Nat.odd_mul.mp hodd).2
      rw [cmAllNCoefficient_coprime_mul hab, abs_mul]
      calc
        |cmAllNCoefficient a| * |cmAllNCoefficient b|
          ≤ (a : ℤ)^2 * (b : ℤ)^2 := by
            gcongr
            · exact hia hoa
            · exact hib hob
        _ = ((a*b : ℕ) : ℤ)^2 := by push_cast; ring

noncomputable def cmOddDirichletSummand
    (s : ℂ) (n : ℕ) : ℂ :=
  if Odd n then
    (cmAllNCoefficient n : ℂ) * (n : ℂ) ^ (-s)
  else 0

theorem cmOddDirichletSummand_norm_le
    {s : ℂ} (hs : 3 < s.re) (n : ℕ) :
    ‖cmOddDirichletSummand s n‖
      ≤ (n : ℝ) ^ (2 - s.re) := by
  by_cases hnodd : Odd n
  · have hnpos : 0 < n := hnodd.pos
    rw [cmOddDirichletSummand, if_pos hnodd, norm_mul,
      Complex.norm_intCast]
    rw [norm_natCast_cpow_of_pos hnpos (-s)]
    have hcoef := cmAllNCoefficient_abs_le_sq_of_odd n hnodd
    calc
      |cmAllNCoefficient n| * (n : ℝ) ^ (-s.re)
        ≤ (n : ℝ)^2 * (n : ℝ)^(-s.re) := by
          gcongr
          exact_mod_cast hcoef
      _ = (n : ℝ) ^ (2 - s.re) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_add (by positivity : 0 < (n : ℝ))]
        congr 2
        ring
  · simp [cmOddDirichletSummand, hnodd]
    positivity

theorem cmOddDirichletSummand_summable
    {s : ℂ} (hs : 3 < s.re) :
    Summable (cmOddDirichletSummand s) := by
  have hmaj : Summable (fun n : ℕ => (n : ℝ) ^ (2 - s.re)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact (hmaj.of_nonneg_of_le
    (fun n => norm_nonneg (cmOddDirichletSummand s n))
    (cmOddDirichletSummand_norm_le hs)).of_norm

noncomputable def cmOddLSeries
    (s : ℂ) : ℂ :=
  ∑' n : ℕ, cmOddDirichletSummand s n

theorem cmOddLSeries_hasSum
    {s : ℂ} (hs : 3 < s.re) :
    HasSum (cmOddDirichletSummand s) (cmOddLSeries s) :=
  (cmOddDirichletSummand_summable hs).hasSum

end Synthesis.Millennium.BSD
