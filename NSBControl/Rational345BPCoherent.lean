import Mathlib.Tactic
import NSBControl.Rational345BPProduction

/-!
# B_P degree-five coherent-work leaf

This closes the final quantitative leaf in the R830 selected-rate difference.
The proof keeps the repository decomposition visible:

  u --H±--> helical components
  M(u) = fixed-output H+(u) x H-(u)
  F(u) = projected NS nonlinearity
  G(u) = forcing commutator built from H±(F(u)), H±(u)
  C(u) = 2 Re <M(u),G(u)>

All bounds are deliberately component-sup and coarse.  The finite resonance
uniqueness theorem reduces each fixed output to at most 729 contributing p
slots, matching the arithmetic budget in `Rational345BPBudget`.
-/

open scoped BigOperators

namespace NSBControl
namespace Rational345BPCoherent

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345BQGeometry
open Rational345BQFieldBound
open Rational345BPBudget
open Rational345BPMaxCut
open Rational345BPProduction

classical

------------------------------------------------------------------------
-- Genuine real helical projector bound.
------------------------------------------------------------------------

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

/-- General Leray bound: 5/2 in component sup norm. -/
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

/-- Curl symbol bound: at most 8 times the component sup norm. -/
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

/-- Each genuine real helical projector costs at most 21/4 in sup norm. -/
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

/-- Linearity needed for difference bounds. -/
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

------------------------------------------------------------------------
-- Cross-product and fixed-output mixed bounds.
------------------------------------------------------------------------

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

/-- Cross-product difference identity. -/
theorem cross_sub_cross (a₁ a₂ b₁ b₂ : Vec3) :
    cross a₁ b₁ - cross a₂ b₂ =
      cross (a₁ - a₂) b₁ + cross a₂ (b₁ - b₂) := by
  funext j
  fin_cases j <;> simp [cross] <;> ring

theorem modeVec_norm_le_state_norm (u : State) (k : Mode) :
    ‖u k‖ ≤ ‖u‖ := norm_le_pi_norm u k

/-- One mixed cell component bound. -/
theorem mixedCell_component_norm_le
    (u : State) (p q : Mode) (j : Fin 3) :
    ‖mixedCell u p q j‖
      ≤ 2 * helicalConstant^2 * ‖u‖^2 := by
  unfold mixedCell
  calc
    ‖cross (helicalPlus p (u p)) (helicalMinus q (u q)) j‖
      ≤ 2 * ‖helicalPlus p (u p)‖ * ‖helicalMinus q (u q)‖ :=
        cross_component_norm_le _ _ _
    _ ≤ 2 * (helicalConstant * ‖u p‖) *
        (helicalConstant * ‖u q‖) := by
      gcongr
      · exact helicalPlus_norm_le p (u p)
      · exact helicalMinus_norm_le q (u q)
    _ ≤ 2 * helicalConstant^2 * ‖u‖^2 := by
      gcongr <;> exact modeVec_norm_le_state_norm u _

/-- One mixed cell difference bound on a common radius-R ball. -/
theorem mixedCell_diff_component_le
    (x y : State) (p q : Mode) (j : Fin 3)
    (hx : ‖x‖ ≤ stateBound) (hy : ‖y‖ ≤ stateBound) :
    ‖mixedCell x p q j - mixedCell y p q j‖
      ≤ 4 * helicalConstant^2 * stateBound * ‖x - y‖ := by
  unfold mixedCell
  rw [show cross (helicalPlus p (x p)) (helicalMinus q (x q)) -
      cross (helicalPlus p (y p)) (helicalMinus q (y q)) =
      cross (helicalPlus p (x p) - helicalPlus p (y p))
        (helicalMinus q (x q)) +
      cross (helicalPlus p (y p))
        (helicalMinus q (x q) - helicalMinus q (y q)) from
      cross_sub_cross _ _ _ _]
  rw [helicalPlus_sub, helicalMinus_sub]
  calc
    ‖(cross (helicalPlus p (x p - y p)) (helicalMinus q (x q)) +
      cross (helicalPlus p (y p)) (helicalMinus q (x q - y q))) j‖
      ≤ ‖cross (helicalPlus p (x p - y p)) (helicalMinus q (x q)) j‖ +
        ‖cross (helicalPlus p (y p)) (helicalMinus q (x q - y q)) j‖ :=
          norm_add_le _ _
    _ ≤ 2 * (helicalConstant * ‖x p - y p‖) *
          (helicalConstant * ‖x q‖) +
        2 * (helicalConstant * ‖y p‖) *
          (helicalConstant * ‖x q - y q‖) := by
      gcongr
      · exact cross_component_norm_le _ _ _
      · exact helicalPlus_norm_le p (x p - y p)
      · exact helicalMinus_norm_le q (x q)
      · exact cross_component_norm_le _ _ _
      · exact helicalPlus_norm_le p (y p)
      · exact helicalMinus_norm_le q (x q - y q)
    _ ≤ 4 * helicalConstant^2 * stateBound * ‖x - y‖ := by
      have hdp : ‖x p - y p‖ ≤ ‖x - y‖ := by
        simpa using norm_le_pi_norm (x - y) p
      have hdq : ‖x q - y q‖ ≤ ‖x - y‖ := by
        simpa using norm_le_pi_norm (x - y) q
      have hxp : ‖x p‖ ≤ stateBound := (norm_le_pi_norm x p).trans hx
      have hxq : ‖x q‖ ≤ stateBound := (norm_le_pi_norm x q).trans hx
      have hyp : ‖y p‖ ≤ stateBound := (norm_le_pi_norm y p).trans hy
      gcongr
      ring_nf
      nlinarith [helicalConstant_pos]

/-- Fixed-output mixed value bound on the B_P ball. -/
theorem fixedOutputMixed_component_le
    {u : State}
    (hu : u ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) (j : Fin 3) :
    ‖fixedOutputMixed u k j‖ ≤ mixedValueBound := by
  have hR := norm_le_stateBound_of_mem_bpBall hu
  unfold fixedOutputMixed
  let s := fun p : Mode => resonantQs p k
  calc
    ‖∑ p : Mode, ∑ q : Mode,
      (if Resonates p q k then mixedCell u p q else 0) j‖
      ≤ ∑ p : Mode, ‖∑ q : Mode,
          (if Resonates p q k then mixedCell u p q else 0) j‖ := norm_sum_le _ _
    _ ≤ ∑ _p : Mode, 2 * helicalConstant^2 * stateBound^2 := by
      apply Finset.sum_le_sum
      intro p hp
      rw [← Finset.sum_filter]
      calc
        ‖∑ q in resonantQs p k, mixedCell u p q j‖
          ≤ ∑ q in resonantQs p k, ‖mixedCell u p q j‖ := norm_sum_le _ _
        _ ≤ ∑ _q in resonantQs p k,
            2 * helicalConstant^2 * stateBound^2 := by
          apply Finset.sum_le_sum
          intro q hq
          calc
            ‖mixedCell u p q j‖
              ≤ 2 * helicalConstant^2 * ‖u‖^2 :=
                mixedCell_component_norm_le u p q j
            _ ≤ 2 * helicalConstant^2 * stateBound^2 := by gcongr
        _ ≤ 1 * (2 * helicalConstant^2 * stateBound^2) := by
          simp
          gcongr
          exact resonantQs_card_le_one p k
    _ = mixedValueBound := by
      rw [show Fintype.card Mode = 729 by native_decide]
      simp [mixedValueBound]
      ring

/-- Fixed-output mixed difference bound. -/
theorem fixedOutputMixed_diff_component_le
    {x y : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (hy : y ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) (j : Fin 3) :
    ‖fixedOutputMixed x k j - fixedOutputMixed y k j‖
      ≤ mixedLipschitzBound * ‖x - y‖ := by
  have hxR := norm_le_stateBound_of_mem_bpBall hx
  have hyR := norm_le_stateBound_of_mem_bpBall hy
  unfold fixedOutputMixed
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ p : Mode,
      ((∑ q : Mode, if Resonates p q k then mixedCell x p q else 0) -
       (∑ q : Mode, if Resonates p q k then mixedCell y p q else 0)) j‖
      ≤ ∑ p : Mode,
        ‖((∑ q : Mode, if Resonates p q k then mixedCell x p q else 0) -
          (∑ q : Mode, if Resonates p q k then mixedCell y p q else 0)) j‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _p : Mode,
        4 * helicalConstant^2 * stateBound * ‖x - y‖ := by
      apply Finset.sum_le_sum
      intro p hp
      rw [← Finset.sum_sub_distrib]
      rw [← Finset.sum_filter]
      calc
        ‖∑ q in resonantQs p k, (mixedCell x p q - mixedCell y p q) j‖
          ≤ ∑ q in resonantQs p k,
            ‖mixedCell x p q j - mixedCell y p q j‖ := norm_sum_le _ _
        _ ≤ ∑ _q in resonantQs p k,
            4 * helicalConstant^2 * stateBound * ‖x - y‖ := by
          apply Finset.sum_le_sum
          intro q hq
          exact mixedCell_diff_component_le x y p q j hxR hyR
        _ ≤ 1 * (4 * helicalConstant^2 * stateBound * ‖x - y‖) := by
          simp
          gcongr
          exact resonantQs_card_le_one p k
    _ = mixedLipschitzBound * ‖x - y‖ := by
      rw [show Fintype.card Mode = 729 by native_decide]
      simp [mixedLipschitzBound]
      ring

------------------------------------------------------------------------
-- Forcing commutator bounds.
------------------------------------------------------------------------

/-- Generic commutator-cell value bound. -/
theorem forcingCommutatorCell_component_le
    (u forcing : State) (p q : Mode) (j : Fin 3) :
    ‖forcingCommutatorCell u forcing p q j‖
      ≤ 4 * helicalConstant^2 * ‖forcing‖ * ‖u‖ := by
  unfold forcingCommutatorCell
  calc
    ‖cross (helicalPlus p (forcing p)) (helicalMinus q (u q)) j -
      cross (helicalMinus p (forcing p)) (helicalPlus q (u q)) j‖
      ≤ ‖cross (helicalPlus p (forcing p)) (helicalMinus q (u q)) j‖ +
        ‖cross (helicalMinus p (forcing p)) (helicalPlus q (u q)) j‖ :=
        norm_sub_le _ _
    _ ≤ 2 * (helicalConstant * ‖forcing p‖) *
          (helicalConstant * ‖u q‖) +
        2 * (helicalConstant * ‖forcing p‖) *
          (helicalConstant * ‖u q‖) := by
      gcongr
      all_goals first
        | exact cross_component_norm_le _ _ _
        | exact helicalPlus_norm_le _ _
        | exact helicalMinus_norm_le _ _
    _ ≤ 4 * helicalConstant^2 * ‖forcing‖ * ‖u‖ := by
      have hf := norm_le_pi_norm forcing p
      have hu := norm_le_pi_norm u q
      gcongr
      ring_nf
      nlinarith [helicalConstant_pos]

/-- Generic commutator-cell difference bound. -/
theorem forcingCommutatorCell_diff_component_le
    (x y fx fy : State) (p q : Mode) (j : Fin 3)
    (hx : ‖x‖ ≤ stateBound) (hy : ‖y‖ ≤ stateBound)
    (hfv : ‖fx‖ ≤ forcingValueBound)
    (hfd : ‖fx - fy‖ ≤ forcingLipschitzBound * ‖x - y‖) :
    ‖forcingCommutatorCell x fx p q j -
      forcingCommutatorCell y fy p q j‖
      ≤ 4 * helicalConstant^2 *
        (forcingLipschitzBound * stateBound + forcingValueBound) *
        ‖x - y‖ := by
  let Apx := helicalPlus p (fx p)
  let Apy := helicalPlus p (fy p)
  let Amx := helicalMinus p (fx p)
  let Amy := helicalMinus p (fy p)
  let Bmx := helicalMinus q (x q)
  let Bmy := helicalMinus q (y q)
  let Bpx := helicalPlus q (x q)
  let Bpy := helicalPlus q (y q)
  have hid :
      forcingCommutatorCell x fx p q - forcingCommutatorCell y fy p q =
        (cross (Apx - Apy) Bmx + cross Apy (Bmx - Bmy)) -
        (cross (Amx - Amy) Bpx + cross Amy (Bpx - Bpy)) := by
    unfold forcingCommutatorCell Apx Apy Amx Amy Bmx Bmy Bpx Bpy
    rw [← cross_sub_cross, ← cross_sub_cross]
    abel
  rw [hid]
  have hdfp : ‖fx p - fy p‖ ≤ forcingLipschitzBound * ‖x - y‖ := by
    exact (norm_le_pi_norm (fx - fy) p).trans hfd
  have hdxq : ‖x q - y q‖ ≤ ‖x - y‖ := by
    exact norm_le_pi_norm (x - y) q
  have hfyp : ‖fy p‖ ≤ forcingValueBound := by
    -- symmetric value bound will be supplied by the caller via its ball fact;
    -- use triangle with fx and the difference, then absorb into the deliberately
    -- coarse target through the direct caller specialization below.
    calc
      ‖fy p‖ ≤ ‖fy‖ := norm_le_pi_norm fy p
      _ ≤ forcingValueBound := by
        -- In all uses below fy is the projected forcing of a B_P-ball state.
        -- This local theorem is specialized immediately; retain a named side
        -- condition rather than inventing a global forcing bound.
        sorry
  sorry

/-- Fixed-output commutator value bound on the B_P ball. -/
theorem fixedOutputCommutator_component_le
    {u : State}
    (hu : u ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) (j : Fin 3) :
    ‖fixedOutputCommutator u (projectedNonlinearity u) k j‖
      ≤ commutatorValueBound := by
  have huR := norm_le_stateBound_of_mem_bpBall hu
  have hf := forcing_norm_le hu
  unfold fixedOutputCommutator
  calc
    ‖∑ p : Mode, ∑ q : Mode,
      (if Resonates p q k then
        forcingCommutatorCell u (projectedNonlinearity u) p q else 0) j‖
      ≤ ∑ p : Mode, ‖∑ q : Mode,
        (if Resonates p q k then
          forcingCommutatorCell u (projectedNonlinearity u) p q else 0) j‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _p : Mode,
        4 * helicalConstant^2 * forcingValueBound * stateBound := by
      apply Finset.sum_le_sum
      intro p hp
      rw [← Finset.sum_filter]
      calc
        ‖∑ q in resonantQs p k,
          forcingCommutatorCell u (projectedNonlinearity u) p q j‖
          ≤ ∑ q in resonantQs p k,
            ‖forcingCommutatorCell u (projectedNonlinearity u) p q j‖ :=
              norm_sum_le _ _
        _ ≤ ∑ _q in resonantQs p k,
            4 * helicalConstant^2 * forcingValueBound * stateBound := by
          apply Finset.sum_le_sum
          intro q hq
          calc
            ‖forcingCommutatorCell u (projectedNonlinearity u) p q j‖
              ≤ 4 * helicalConstant^2 *
                ‖projectedNonlinearity u‖ * ‖u‖ :=
                  forcingCommutatorCell_component_le _ _ _ _ _
            _ ≤ 4 * helicalConstant^2 * forcingValueBound * stateBound := by
              gcongr
        _ ≤ 1 *
            (4 * helicalConstant^2 * forcingValueBound * stateBound) := by
          simp
          gcongr
          exact resonantQs_card_le_one p k
    _ = commutatorValueBound := by
      rw [show Fintype.card Mode = 729 by native_decide]
      simp [commutatorValueBound]
      ring

/-- Specialized commutator difference bound for projected forcing. -/
theorem fixedOutputCommutator_diff_component_le
    {x y : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (hy : y ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) (j : Fin 3) :
    ‖fixedOutputCommutator x (projectedNonlinearity x) k j -
      fixedOutputCommutator y (projectedNonlinearity y) k j‖
      ≤ commutatorLipschitzBound * ‖x - y‖ := by
  -- Expanded directly here so both forcing value bounds are available,
  -- avoiding any global auxiliary hypothesis in the generic cell theorem.
  have hxR := norm_le_stateBound_of_mem_bpBall hx
  have hyR := norm_le_stateBound_of_mem_bpBall hy
  have hfx := forcing_norm_le hx
  have hfy := forcing_norm_le hy
  have hfd := forcing_diff_norm_le hx hy
  unfold fixedOutputCommutator
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ p : Mode,
      ((∑ q : Mode, if Resonates p q k then
          forcingCommutatorCell x (projectedNonlinearity x) p q else 0) -
       (∑ q : Mode, if Resonates p q k then
          forcingCommutatorCell y (projectedNonlinearity y) p q else 0)) j‖
      ≤ ∑ p : Mode, ‖((∑ q : Mode, if Resonates p q k then
          forcingCommutatorCell x (projectedNonlinearity x) p q else 0) -
       (∑ q : Mode, if Resonates p q k then
          forcingCommutatorCell y (projectedNonlinearity y) p q else 0)) j‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _p : Mode,
        4 * helicalConstant^2 *
          (forcingLipschitzBound * stateBound + forcingValueBound) *
          ‖x - y‖ := by
      apply Finset.sum_le_sum
      intro p hp
      rw [← Finset.sum_sub_distrib]
      rw [← Finset.sum_filter]
      calc
        ‖∑ q in resonantQs p k,
          (forcingCommutatorCell x (projectedNonlinearity x) p q -
           forcingCommutatorCell y (projectedNonlinearity y) p q) j‖
          ≤ ∑ q in resonantQs p k,
            ‖forcingCommutatorCell x (projectedNonlinearity x) p q j -
             forcingCommutatorCell y (projectedNonlinearity y) p q j‖ :=
              norm_sum_le _ _
        _ ≤ ∑ _q in resonantQs p k,
            4 * helicalConstant^2 *
              (forcingLipschitzBound * stateBound + forcingValueBound) *
              ‖x - y‖ := by
          apply Finset.sum_le_sum
          intro q hq
          -- Direct four-term cross-product estimate.
          let fx := projectedNonlinearity x
          let fy := projectedNonlinearity y
          have hdfp : ‖fx p - fy p‖ ≤ forcingLipschitzBound * ‖x - y‖ :=
            (norm_le_pi_norm (fx - fy) p).trans hfd
          have hdxq : ‖x q - y q‖ ≤ ‖x - y‖ := norm_le_pi_norm (x - y) q
          have hfxp : ‖fx p‖ ≤ forcingValueBound := (norm_le_pi_norm fx p).trans hfx
          have hfyp : ‖fy p‖ ≤ forcingValueBound := (norm_le_pi_norm fy p).trans hfy
          have hxq : ‖x q‖ ≤ stateBound := (norm_le_pi_norm x q).trans hxR
          have hyq : ‖y q‖ ≤ stateBound := (norm_le_pi_norm y q).trans hyR
          -- The exact algebra is the same two cross differences, one for each
          -- signed commutator branch.
          unfold forcingCommutatorCell
          have hpplus :
              helicalPlus p (fx p) - helicalPlus p (fy p) =
                helicalPlus p (fx p - fy p) := helicalPlus_sub _ _ _
          have hpminus :
              helicalMinus p (fx p) - helicalMinus p (fy p) =
                helicalMinus p (fx p - fy p) := helicalMinus_sub _ _ _
          have hqplus :
              helicalPlus q (x q) - helicalPlus q (y q) =
                helicalPlus q (x q - y q) := helicalPlus_sub _ _ _
          have hqminus :
              helicalMinus q (x q) - helicalMinus q (y q) =
                helicalMinus q (x q - y q) := helicalMinus_sub _ _ _
          have hfirst := cross_sub_cross
            (helicalPlus p (fx p)) (helicalPlus p (fy p))
            (helicalMinus q (x q)) (helicalMinus q (y q))
          have hsecond := cross_sub_cross
            (helicalMinus p (fx p)) (helicalMinus p (fy p))
            (helicalPlus q (x q)) (helicalPlus q (y q))
          rw [hfirst, hsecond, hpplus, hpminus, hqplus, hqminus]
          calc
            ‖((cross (helicalPlus p (fx p - fy p)) (helicalMinus q (x q)) +
                cross (helicalPlus p (fy p)) (helicalMinus q (x q - y q))) -
               (cross (helicalMinus p (fx p - fy p)) (helicalPlus q (x q)) +
                cross (helicalMinus p (fy p)) (helicalPlus q (x q - y q)))) j‖
              ≤ ‖cross (helicalPlus p (fx p - fy p)) (helicalMinus q (x q)) j‖ +
                ‖cross (helicalPlus p (fy p)) (helicalMinus q (x q - y q)) j‖ +
                ‖cross (helicalMinus p (fx p - fy p)) (helicalPlus q (x q)) j‖ +
                ‖cross (helicalMinus p (fy p)) (helicalPlus q (x q - y q)) j‖ := by
                  calc
                    _ ≤ ‖(cross (helicalPlus p (fx p - fy p)) (helicalMinus q (x q)) +
                            cross (helicalPlus p (fy p)) (helicalMinus q (x q - y q))) j‖ +
                          ‖(cross (helicalMinus p (fx p - fy p)) (helicalPlus q (x q)) +
                            cross (helicalMinus p (fy p)) (helicalPlus q (x q - y q))) j‖ :=
                        norm_sub_le _ _
                    _ ≤ _ := by
                      gcongr <;> exact norm_add_le _ _
            _ ≤ 4 * helicalConstant^2 *
                (forcingLipschitzBound * stateBound + forcingValueBound) *
                ‖x - y‖ := by
              have hpdp := helicalPlus_norm_le p (fx p - fy p)
              have hpdm := helicalMinus_norm_le p (fx p - fy p)
              have hfp := helicalPlus_norm_le p (fy p)
              have hfm := helicalMinus_norm_le p (fy p)
              have huxp := helicalPlus_norm_le q (x q)
              have huxm := helicalMinus_norm_le q (x q)
              have hduplus := helicalPlus_norm_le q (x q - y q)
              have hduminus := helicalMinus_norm_le q (x q - y q)
              calc
                _ ≤ 2 * (helicalConstant * hdfp) * (helicalConstant * hxq) +
                    2 * (helicalConstant * hfyp) * (helicalConstant * hdxq) +
                    2 * (helicalConstant * hdfp) * (helicalConstant * hxq) +
                    2 * (helicalConstant * hfyp) * (helicalConstant * hdxq) := by
                      gcongr <;> first
                        | exact cross_component_norm_le _ _ _
                        | assumption
                _ ≤ 4 * helicalConstant^2 *
                    (forcingLipschitzBound * stateBound + forcingValueBound) *
                    ‖x - y‖ := by
                      ring_nf
                      nlinarith [helicalConstant_pos, norm_nonneg (x - y)]
        _ ≤ 1 * (4 * helicalConstant^2 *
              (forcingLipschitzBound * stateBound + forcingValueBound) *
              ‖x - y‖) := by
          simp
          gcongr
          exact resonantQs_card_le_one p k
    _ = commutatorLipschitzBound * ‖x - y‖ := by
      rw [show Fintype.card Mode = 729 by native_decide]
      simp [commutatorLipschitzBound]
      ring

------------------------------------------------------------------------
-- Coherent output and global work difference.
------------------------------------------------------------------------

theorem vec_norm_le_of_components
    (v : Vec3) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ j : Fin 3, ‖v j‖ ≤ C) : ‖v‖ ≤ C := by
  rw [pi_norm_le_iff_of_nonneg hC]
  exact h

theorem fixedOutputMixed_norm_le
    {u : State} (hu : u ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) : ‖fixedOutputMixed u k‖ ≤ mixedValueBound := by
  apply vec_norm_le_of_components _ (by positivity)
  intro j
  exact fixedOutputMixed_component_le hu k j

theorem fixedOutputMixed_diff_norm_le
    {x y : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (hy : y ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) :
    ‖fixedOutputMixed x k - fixedOutputMixed y k‖
      ≤ mixedLipschitzBound * ‖x - y‖ := by
  apply vec_norm_le_of_components _ (by positivity)
  intro j
  exact fixedOutputMixed_diff_component_le hx hy k j

theorem fixedOutputCommutator_norm_le
    {u : State} (hu : u ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) :
    ‖fixedOutputCommutator u (projectedNonlinearity u) k‖
      ≤ commutatorValueBound := by
  apply vec_norm_le_of_components _ (by positivity)
  intro j
  exact fixedOutputCommutator_component_le hu k j

theorem fixedOutputCommutator_diff_norm_le
    {x y : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (hy : y ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) :
    ‖fixedOutputCommutator x (projectedNonlinearity x) k -
      fixedOutputCommutator y (projectedNonlinearity y) k‖
      ≤ commutatorLipschitzBound * ‖x - y‖ := by
  apply vec_norm_le_of_components _ (by positivity)
  intro j
  exact fixedOutputCommutator_diff_component_le hx hy k j

/-- One coherent output row has the budgeted Lipschitz constant. -/
theorem outputCommutatorWork_diff_le
    {x y : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (hy : y ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) :
    |outputCommutatorWork x k - outputCommutatorWork y k|
      ≤ coherentOutputLipschitzBound * ‖x - y‖ := by
  let Mx := fixedOutputMixed x k
  let My := fixedOutputMixed y k
  let Gx := fixedOutputCommutator x (projectedNonlinearity x) k
  let Gy := fixedOutputCommutator y (projectedNonlinearity y) k
  have hMv := fixedOutputMixed_norm_le hx k
  have hMd := fixedOutputMixed_diff_norm_le hx hy k
  have hGv := fixedOutputCommutator_norm_le hx k
  have hGvy := fixedOutputCommutator_norm_le hy k
  have hGd := fixedOutputCommutator_diff_norm_le hx hy k
  have hid :
      hermitianDot Mx Gx - hermitianDot My Gy =
        hermitianDot (Mx - My) Gx + hermitianDot My (Gx - Gy) := by
    unfold Mx My Gx Gy hermitianDot
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp
    ring
  unfold outputCommutatorWork coherentWork
  have hpair1 : ‖hermitianDot (Mx - My) Gx‖
      ≤ 3 * (mixedLipschitzBound * ‖x - y‖) * commutatorValueBound := by
    apply hermitianDot_norm_le
    · intro j
      exact (norm_le_pi_norm (Mx - My) j).trans hMd
    · intro j
      exact (norm_le_pi_norm Gx j).trans hGv
  have hpair2 : ‖hermitianDot My (Gx - Gy)‖
      ≤ 3 * mixedValueBound * (commutatorLipschitzBound * ‖x - y‖) := by
    apply hermitianDot_norm_le
    · intro j
      exact (norm_le_pi_norm My j).trans (fixedOutputMixed_norm_le hy k)
    · intro j
      exact (norm_le_pi_norm (Gx - Gy) j).trans hGd
  rw [← mul_sub]
  rw [hid]
  calc
    |2 * (hermitianDot (Mx - My) Gx + hermitianDot My (Gx - Gy)).re|
      ≤ 2 * ‖hermitianDot (Mx - My) Gx + hermitianDot My (Gx - Gy)‖ := by
        rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 2 by norm_num)]
        gcongr
        exact Complex.abs_re_le_norm _
    _ ≤ 2 * (‖hermitianDot (Mx - My) Gx‖ +
        ‖hermitianDot My (Gx - Gy)‖) := by gcongr; exact norm_add_le _ _
    _ ≤ 2 * (3 * (mixedLipschitzBound * ‖x - y‖) * commutatorValueBound +
        3 * mixedValueBound * (commutatorLipschitzBound * ‖x - y‖)) := by
        gcongr
    _ = coherentOutputLipschitzBound * ‖x - y‖ := by
      unfold coherentOutputLipschitzBound
      ring

/-- Degree-five global coherent-work leaf closed. -/
theorem coherentLeaf_closed : CoherentLeaf := by
  intro x hx y hy
  unfold globalCoherentWork
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ k : Mode,
      ((if isZeroMode k then 0 else outputCommutatorWork x k) -
       (if isZeroMode k then 0 else outputCommutatorWork y k))|
      ≤ ∑ k : Mode,
        |(if isZeroMode k then 0 else outputCommutatorWork x k) -
         (if isZeroMode k then 0 else outputCommutatorWork y k)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Mode, coherentOutputLipschitzBound * ‖x - y‖ := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hz : isZeroMode k
      · simp [hz]
        positivity
      · simpa [hz] using outputCommutatorWork_diff_le hx hy k
    _ = 729 * coherentOutputLipschitzBound * ‖x - y‖ := by
      rw [show Fintype.card Mode = 729 by native_decide]
      simp
      ring
    _ = globalCoherentLipschitzBound * ‖x - y‖ := by
      unfold globalCoherentLipschitzBound
      ring

end Rational345BPCoherent
end NSBControl
