import Mathlib.Tactic
import NSBControl.Rational345BPProduction

/-!
# B_P genuine real helical bounds

The evolving observable uses the physical real mode radius, not the rational
snapshot calibration.  This file proves a uniform component-sup estimate on
the entire radius-four cube:

  ||H_k^± v||_∞ <= 21/4 ||v||_∞.

It also records the exact linear difference identities and the elementary
cross-product bounds used by the mixed/commutator owners.
-/

namespace NSBControl
namespace Rational345BPHelicalBounds

open Rational345RealRadius4
open Rational345BQGeometry
open Rational345BQFieldBound
open Rational345BPBudget

classical

theorem normSq_eq_natCast (k : Mode) :
    normSq k = (normSqNat k : ℝ) := by
  simp [normSq, normSqNat, absCoord, kReal, Fin.sum_univ_succ,
    Nat.cast_add, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs, sq_abs]
  ring

theorem normSqNat_ge_one_of_nonzero :
    ∀ k : Mode, ¬ isZeroMode k → 1 ≤ normSqNat k := by
  native_decide

theorem modeNorm_ge_one (k : Mode) (hk : ¬ isZeroMode k) :
    1 ≤ modeNorm k := by
  rw [modeNorm, Real.one_le_sqrt]
  rw [normSq_eq_natCast]
  exact_mod_cast normSqNat_ge_one_of_nonzero k hk

theorem inverseModeNorm_abs_le_one (k : Mode) :
    |inverseModeNorm k| ≤ 1 := by
  by_cases hk : isZeroMode k
  · have hsq : normSq k = 0 := by
      have hcoords : ∀ j : Fin 3, kReal k j = 0 := by
        intro j
        simpa [kReal] using hk j
      simp [normSq, hcoords]
    simp [inverseModeNorm, modeNorm, hsq]
  · have hnorm : 1 ≤ modeNorm k := modeNorm_ge_one k hk
    have hpos : 0 < modeNorm k := zero_lt_one.trans_le hnorm
    rw [inverseModeNorm, abs_of_pos (one_div_pos.mpr hpos)]
    simpa using one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hnorm

/-- General Leray projection bound in component-sup norm. -/
theorem leray_component_norm_le
    (k : Mode) (value : Vec3) (j : Fin 3) :
    ‖leray k value j‖ ≤ (5 : ℝ) / 2 * ‖value‖ := by
  by_cases hk : isZeroMode k
  · simp [leray, hk]
  · have hdot :
        ‖bilinearDot (kComplex k) value‖ ≤
          (|kReal k 0| + |kReal k 1| + |kReal k 2|) * ‖value‖ := by
      unfold bilinearDot
      calc
        ‖∑ a : Fin 3, kComplex k a * value a‖
          ≤ ∑ a : Fin 3, ‖kComplex k a * value a‖ := norm_sum_le _ _
        _ = ∑ a : Fin 3, |kReal k a| * ‖value a‖ := by
          apply Finset.sum_congr rfl
          intro a ha
          simp [kComplex, norm_mul, mul_comm]
        _ ≤ ∑ a : Fin 3, |kReal k a| * ‖value‖ := by
          apply Finset.sum_le_sum
          intro a ha
          gcongr
          exact norm_le_pi_norm value a
        _ = (|kReal k 0| + |kReal k 1| + |kReal k 2|) * ‖value‖ := by
          simp [Fin.sum_univ_succ]
          ring
    have hratio := leray_ratio_real k j hk
    unfold leray
    simp only [if_neg hk]
    calc
      ‖value j - (kReal k j : ℂ) *
          (bilinearDot (kComplex k) value / (normSq k : ℂ))‖
        ≤ ‖value j‖ +
          ‖(kReal k j : ℂ) *
            (bilinearDot (kComplex k) value / (normSq k : ℂ))‖ := norm_sub_le _ _
      _ ≤ ‖value‖ +
          |kReal k j| *
            ((|kReal k 0| + |kReal k 1| + |kReal k 2|) * ‖value‖) /
            normSq k := by
        gcongr
        · exact norm_le_pi_norm value j
        · rw [norm_mul, norm_div]
          simp only [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (normSq_nonneg k)]
          gcongr
      _ ≤ ‖value‖ + ((3 : ℝ) / 2) * ‖value‖ := by
        gcongr
        calc
          |kReal k j| *
              ((|kReal k 0| + |kReal k 1| + |kReal k 2|) * ‖value‖) /
              normSq k
            = (|kReal k j| *
                (|kReal k 0| + |kReal k 1| + |kReal k 2|) /
                normSq k) * ‖value‖ := by ring
          _ ≤ ((3 : ℝ) / 2) * ‖value‖ := by gcongr
      _ = (5 : ℝ) / 2 * ‖value‖ := by ring

/-- Curl symbol bound on the radius-four cube. -/
theorem curl_component_norm_le
    (k : Mode) (value : Vec3) (j : Fin 3) :
    ‖curlSymbol k value j‖ ≤ 8 * ‖value‖ := by
  rw [curlSymbol, norm_mul]
  simp only [Complex.norm_I, one_mul]
  fin_cases j
  · simp [cross, kComplex]
    calc
      ‖(kReal k 1 : ℂ) * value 2 - (kReal k 2 : ℂ) * value 1‖
        ≤ ‖(kReal k 1 : ℂ) * value 2‖ +
          ‖(kReal k 2 : ℂ) * value 1‖ := norm_sub_le _ _
      _ ≤ 4 * ‖value‖ + 4 * ‖value‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        gcongr
        · exact kReal_abs_le_four k 1
        · exact norm_le_pi_norm value 2
        · exact kReal_abs_le_four k 2
        · exact norm_le_pi_norm value 1
      _ = 8 * ‖value‖ := by ring
  · simp [cross, kComplex]
    calc
      ‖(kReal k 2 : ℂ) * value 0 - (kReal k 0 : ℂ) * value 2‖
        ≤ ‖(kReal k 2 : ℂ) * value 0‖ +
          ‖(kReal k 0 : ℂ) * value 2‖ := norm_sub_le _ _
      _ ≤ 4 * ‖value‖ + 4 * ‖value‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        gcongr
        · exact kReal_abs_le_four k 2
        · exact norm_le_pi_norm value 0
        · exact kReal_abs_le_four k 0
        · exact norm_le_pi_norm value 2
      _ = 8 * ‖value‖ := by ring
  · simp [cross, kComplex]
    calc
      ‖(kReal k 0 : ℂ) * value 1 - (kReal k 1 : ℂ) * value 0‖
        ≤ ‖(kReal k 0 : ℂ) * value 1‖ +
          ‖(kReal k 1 : ℂ) * value 0‖ := norm_sub_le _ _
      _ ≤ 4 * ‖value‖ + 4 * ‖value‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        gcongr
        · exact kReal_abs_le_four k 0
        · exact norm_le_pi_norm value 1
        · exact kReal_abs_le_four k 1
        · exact norm_le_pi_norm value 0
      _ = 8 * ‖value‖ := by ring

theorem helicalPlus_component_norm_le
    (k : Mode) (value : Vec3) (j : Fin 3) :
    ‖helicalPlus k value j‖ ≤ helicalConstant * ‖value‖ := by
  unfold helicalPlus
  rw [norm_mul]
  norm_num
  calc
    (1 / 2 : ℝ) *
        ‖leray k value j +
          (inverseModeNorm k : ℂ) * curlSymbol k value j‖
      ≤ (1 / 2 : ℝ) *
        (‖leray k value j‖ +
          ‖(inverseModeNorm k : ℂ) * curlSymbol k value j‖) := by
          gcongr
          exact norm_add_le _ _
    _ ≤ (1 / 2 : ℝ) *
        (((5 : ℝ) / 2) * ‖value‖ + 1 * (8 * ‖value‖)) := by
          gcongr
          · exact leray_component_norm_le k value j
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            gcongr
            · exact inverseModeNorm_abs_le_one k
            · exact curl_component_norm_le k value j
    _ = helicalConstant * ‖value‖ := by
      norm_num [helicalConstant]
      ring

theorem helicalMinus_component_norm_le
    (k : Mode) (value : Vec3) (j : Fin 3) :
    ‖helicalMinus k value j‖ ≤ helicalConstant * ‖value‖ := by
  unfold helicalMinus
  rw [norm_mul]
  norm_num
  calc
    (1 / 2 : ℝ) *
        ‖leray k value j -
          (inverseModeNorm k : ℂ) * curlSymbol k value j‖
      ≤ (1 / 2 : ℝ) *
        (‖leray k value j‖ +
          ‖(inverseModeNorm k : ℂ) * curlSymbol k value j‖) := by
          gcongr
          exact norm_sub_le _ _
    _ ≤ (1 / 2 : ℝ) *
        (((5 : ℝ) / 2) * ‖value‖ + 1 * (8 * ‖value‖)) := by
          gcongr
          · exact leray_component_norm_le k value j
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            gcongr
            · exact inverseModeNorm_abs_le_one k
            · exact curl_component_norm_le k value j
    _ = helicalConstant * ‖value‖ := by
      norm_num [helicalConstant]
      ring

theorem helicalPlus_norm_le (k : Mode) (value : Vec3) :
    ‖helicalPlus k value‖ ≤ helicalConstant * ‖value‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro j
  exact helicalPlus_component_norm_le k value j

theorem helicalMinus_norm_le (k : Mode) (value : Vec3) :
    ‖helicalMinus k value‖ ≤ helicalConstant * ‖value‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro j
  exact helicalMinus_component_norm_le k value j

/-- Exact linear difference identities. -/
theorem helicalPlus_sub (k : Mode) (a b : Vec3) :
    helicalPlus k a - helicalPlus k b = helicalPlus k (a - b) := by
  funext j
  unfold helicalPlus leray curlSymbol bilinearDot cross
  split_ifs <;> simp [Fin.sum_univ_succ] <;> ring

theorem helicalMinus_sub (k : Mode) (a b : Vec3) :
    helicalMinus k a - helicalMinus k b = helicalMinus k (a - b) := by
  funext j
  unfold helicalMinus leray curlSymbol bilinearDot cross
  split_ifs <;> simp [Fin.sum_univ_succ] <;> ring

/-- Cross product component bound and exact two-factor difference identity. -/
theorem cross_component_norm_le
    (a b : Vec3) (j : Fin 3) :
    ‖cross a b j‖ ≤ 2 * ‖a‖ * ‖b‖ := by
  fin_cases j <;> simp [cross]
  all_goals
    calc
      _ ≤ _ := norm_sub_le _ _
      _ ≤ ‖a‖ * ‖b‖ + ‖a‖ * ‖b‖ := by
        simp only [norm_mul]
        gcongr <;> apply norm_le_pi_norm
      _ = 2 * ‖a‖ * ‖b‖ := by ring

theorem cross_sub_cross (a₁ a₂ b₁ b₂ : Vec3) :
    cross a₁ b₁ - cross a₂ b₂ =
      cross (a₁ - a₂) b₁ + cross a₂ (b₁ - b₂) := by
  funext j
  fin_cases j <;> simp [cross] <;> ring

end Rational345BPHelicalBounds
end NSBControl
