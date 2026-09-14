/-
# A far-shell quantitative tail bound with an explicit cutoff `J`

`ProjectedZeroTailSummability` proves that the shell-grouped quadratic zero
weight

    ρ ↦ m_ρ / (Im ρ − t)²        (on |Im ρ − t| ≥ 1)

is summable on the literal zeta carrier.  Summability alone is qualitative: it
says the far tail converges, not how large it is.  This module upgrades it to an
**explicit inequality with a cutoff**: for every natural cutoff `J ≥ 1`,

    ∑_{|Im ρ − t| ≥ J} m_ρ / (Im ρ − t)²
        ≤ 18 A log(|t| + 4) / J + 72 A / √J ,

where `A` is the constant of the proved unconditional local zero count
`Zeta23.RvM.zetaZeroConfig_local_count`.  The right-hand side is
`farShellBound A |t| J`; it is monotone in the cutoff and tends to `0` as
`J → ∞`, so the far part of the carrier can be paid mechanically at any
prescribed accuracy, with only the finitely many near shells `|Im ρ − t| < J`
left for signed analysis.

The proof is a pair of telescoping estimates: after the shell reduction of
`ProjectedZeroTailSummability` the majorant of shell `n` splits as

    9 A log(a+4)/(n+1)²  +  18 A / ((n+1)√(n+1)) ,

and both pieces are dominated termwise by the decrements of the explicit
antitone majorant `x ↦ 9 A log(a+4)/x + 36 A/√x`.  Nothing here is asymptotic:
each inequality holds for every cutoff.

No `sorry`, no `axiom`, no Boolean receipt, no numerical evidence.
-/
import Zeta23Bridge.ProjectedZeroTailSummability

noncomputable section

open scoped Real
open Zeta23

namespace Zeta23Bridge
namespace FarShellCutoffTailBound

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOtherZerosChannel
open Zeta23Bridge.LiteralWeilOffOrdinateProjectiveTail
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair
open Zeta23Bridge.ReflectionPairKernelDecay
open Zeta23Bridge.ReflectionPairCurvatureBound
open Zeta23Bridge.ProjectedZeroTailSummability

/-! ## 1. Two telescoping inequalities -/

/-- `1/(m+1)² ≤ 1/m − 1/(m+1)` for `m ≥ 1`. -/
theorem inv_sq_le_telescope {m : ℝ} (hm : 1 ≤ m) :
    1 / (m + 1) ^ 2 ≤ 1 / m - 1 / (m + 1) := by
  have h0 : (0:ℝ) < m := lt_of_lt_of_le zero_lt_one hm
  have h1 : (0:ℝ) < m + 1 := by linarith
  rw [div_sub_div _ _ (ne_of_gt h0) (ne_of_gt h1), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `1/((m+1)√(m+1)) ≤ 2 (1/√m − 1/√(m+1))` for `m ≥ 1`. -/
theorem inv_sqrt_cube_le_telescope {m : ℝ} (hm : 1 ≤ m) :
    1 / ((m + 1) * Real.sqrt (m + 1)) ≤ 2 * (1 / Real.sqrt m - 1 / Real.sqrt (m + 1)) := by
  have h0 : (0:ℝ) < m := lt_of_lt_of_le zero_lt_one hm
  set s : ℝ := Real.sqrt m with hs_def
  set r : ℝ := Real.sqrt (m + 1) with hr_def
  have hs : 0 < s := Real.sqrt_pos.2 h0
  have hr : 0 < r := Real.sqrt_pos.2 (by linarith)
  have hs2 : s ^ 2 = m := Real.sq_sqrt h0.le
  have hr2 : r ^ 2 = m + 1 := Real.sq_sqrt (by linarith)
  have hsr : s ≤ r := by
    rw [hs_def, hr_def]; exact Real.sqrt_le_sqrt (by linarith)
  have hprod : (r - s) * (r + s) = 1 := by nlinarith [hs2, hr2]
  have hsum : 0 < r + s := by linarith
  have hrewrite : (m + 1) * r = r ^ 2 * r := by rw [hr2]
  rw [hrewrite]
  have hrhs : 2 * (1 / s - 1 / r) = 2 * (r - s) / (s * r) := by field_simp
  rw [hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
  have hkey : (1 * (s * r)) * (r + s) ≤ (2 * (r - s) * (r ^ 2 * r)) * (r + s) := by
    have h1 : (2 * (r - s) * (r ^ 2 * r)) * (r + s) = 2 * r ^ 3 * ((r - s) * (r + s)) := by ring
    rw [h1, hprod, mul_one]
    nlinarith [hs, hr, hsr]
  exact le_of_mul_le_mul_right hkey hsum

/-! ## 2. The shell majorant splits into two telescoping pieces -/

/-- `log (a + m + 4) ≤ log (a + 4) + 2 √(m+1)` — the `√`-form of `log_shift_le`. -/
theorem log_shift_sqrt_le {a m : ℝ} (ha : 0 ≤ a) (hm : 0 ≤ m) :
    Real.log (a + m + 4) ≤ Real.log (a + 4) + 2 * Real.sqrt (m + 1) := by
  have hle : a + m + 4 ≤ (a + 4) * (m + 1) := by nlinarith
  have h1 : Real.log (a + m + 4) ≤ Real.log (a + 4) + Real.log (m + 1) := by
    calc Real.log (a + m + 4) ≤ Real.log ((a + 4) * (m + 1)) :=
          Real.log_le_log (by linarith) hle
      _ = Real.log (a + 4) + Real.log (m + 1) := Real.log_mul (by linarith) (by linarith)
  have hsq : Real.log (m + 1) = 2 * Real.log (Real.sqrt (m + 1)) := by
    rw [Real.log_sqrt (by linarith)]; ring
  have hlog : Real.log (Real.sqrt (m + 1)) ≤ Real.sqrt (m + 1) - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (by linarith))
  have : Real.log (m + 1) ≤ 2 * Real.sqrt (m + 1) := by rw [hsq]; linarith
  linarith

/-- The explicit antitone majorant whose decrements dominate the shell weights. -/
def tailMajorant (A a x : ℝ) : ℝ := 9 * A * Real.log (a + 4) / x + 36 * A / Real.sqrt x

theorem tailMajorant_nonneg {A a x : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    0 ≤ tailMajorant A a x := by
  have hlog : 0 ≤ Real.log (a + 4) := Real.log_nonneg (by linarith)
  unfold tailMajorant
  have h1 : 0 ≤ 9 * A * Real.log (a + 4) / x := by positivity
  have h2 : 0 ≤ 36 * A / Real.sqrt x := by positivity
  linarith

/-- The shell majorant, split into an inverse-square and an inverse-`3/2` piece. -/
theorem shellWeightNat_split_le (A a : ℝ) (hA : 0 ≤ A) (ha : 0 ≤ a) (n : ℕ) :
    shellWeightNat A a n
      ≤ 9 * A * Real.log (a + 4) / ((n : ℝ) + 1) ^ 2
        + 18 * A / (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1)) := by
  have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hx1base : (1:ℝ) ≤ (n : ℝ) + 1 := by linarith
  set x : ℝ := (n : ℝ) + 1 with hx_def
  have hx1 : (1:ℝ) ≤ x := hx1base
  have hx0 : (0:ℝ) < x := by linarith
  have hD : x / 3 ≤ max 1 ((n : ℝ) - 1) := den_lower n
  have hD0 : (0:ℝ) < x / 3 := by positivity
  have hlognn : 0 ≤ Real.log (a + n + 4) := Real.log_nonneg (by linarith)
  have hloga : 0 ≤ Real.log (a + 4) := Real.log_nonneg (by linarith)
  have step1 : shellWeightNat A a n ≤ A * Real.log (a + n + 4) / (x / 3) ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ hD0.le hD 2
  have step2 : A * Real.log (a + n + 4) / (x / 3) ^ 2
      ≤ A * (Real.log (a + 4) + 2 * Real.sqrt x) / (x / 3) ^ 2 := by
    apply div_le_div_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left (log_shift_sqrt_le ha hn) hA
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsx2 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have expand : A * (Real.log (a + 4) + 2 * Real.sqrt x) / (x / 3) ^ 2
      = 9 * A * Real.log (a + 4) / x ^ 2 + 18 * A / (x * Real.sqrt x) := by
    field_simp
    linear_combination (18 * A) * hsx2
  calc shellWeightNat A a n ≤ A * Real.log (a + n + 4) / (x / 3) ^ 2 := step1
    _ ≤ A * (Real.log (a + 4) + 2 * Real.sqrt x) / (x / 3) ^ 2 := step2
    _ = _ := expand

/-- **The telescoping shell estimate.**  For every shell index `m ≥ 1`, the shell
majorant is at most the decrement of the explicit majorant `tailMajorant`. -/
theorem shellWeightNat_le_tailMajorant_sub (A a : ℝ) (hA : 0 ≤ A) (ha : 0 ≤ a)
    (m : ℕ) (hm : 1 ≤ m) :
    shellWeightNat A a m ≤ tailMajorant A a m - tailMajorant A a ((m : ℝ) + 1) := by
  have hm1 : (1:ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hloga : 0 ≤ Real.log (a + 4) := Real.log_nonneg (by linarith)
  have hsplit := shellWeightNat_split_le A a hA ha m
  have t1 : 9 * A * Real.log (a + 4) / ((m : ℝ) + 1) ^ 2
      ≤ 9 * A * Real.log (a + 4) / (m : ℝ) - 9 * A * Real.log (a + 4) / ((m : ℝ) + 1) := by
    have h := inv_sq_le_telescope hm1
    have hc : 0 ≤ 9 * A * Real.log (a + 4) := by positivity
    have := mul_le_mul_of_nonneg_left h hc
    calc 9 * A * Real.log (a + 4) / ((m : ℝ) + 1) ^ 2
        = 9 * A * Real.log (a + 4) * (1 / ((m : ℝ) + 1) ^ 2) := by ring
      _ ≤ 9 * A * Real.log (a + 4) * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)) := this
      _ = _ := by ring
  have t2 : 18 * A / (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))
      ≤ 36 * A / Real.sqrt (m : ℝ) - 36 * A / Real.sqrt ((m : ℝ) + 1) := by
    have h := inv_sqrt_cube_le_telescope hm1
    have hc : (0:ℝ) ≤ 18 * A := by positivity
    have := mul_le_mul_of_nonneg_left h hc
    calc 18 * A / (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))
        = 18 * A * (1 / (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))) := by ring
      _ ≤ 18 * A * (2 * (1 / Real.sqrt (m : ℝ) - 1 / Real.sqrt ((m : ℝ) + 1))) := this
      _ = _ := by ring
  unfold tailMajorant
  linarith

/-! ## 3. The natural-index tail sum -/

/-- The shell majorant truncated below the cutoff `J`. -/
def natTail (A a : ℝ) (J n : ℕ) : ℝ := if J ≤ n then shellWeightNat A a n else 0

theorem natTail_nonneg (A a : ℝ) (hA : 0 ≤ A) (ha : 0 ≤ a) (J n : ℕ) :
    0 ≤ natTail A a J n := by
  unfold natTail
  split
  · exact shellWeightNat_nonneg A a hA ha n
  · exact le_rfl

theorem summable_natTail (A a : ℝ) (hA : 0 ≤ A) (ha : 0 ≤ a) (J : ℕ) :
    Summable (natTail A a J) := by
  refine Summable.of_nonneg_of_le (fun n => natTail_nonneg A a hA ha J n) (fun n => ?_)
    (summable_shellWeightNat A a hA ha)
  unfold natTail
  split
  · exact le_rfl
  · exact shellWeightNat_nonneg A a hA ha n

/-- **The shifted shell tail is bounded by the explicit majorant.** -/
theorem tsum_shellWeightNat_shift_le (A a : ℝ) (hA : 0 ≤ A) (ha : 0 ≤ a)
    (J : ℕ) (hJ : 1 ≤ J) :
    ∑' k : ℕ, shellWeightNat A a (k + J) ≤ tailMajorant A a J := by
  refine Real.tsum_le_of_sum_range_le (fun k => shellWeightNat_nonneg A a hA ha _) (fun N => ?_)
  have hstep : ∀ k : ℕ, shellWeightNat A a (k + J)
      ≤ tailMajorant A a ((k : ℝ) + J) - tailMajorant A a ((k : ℝ) + J + 1) := by
    intro k
    have h := shellWeightNat_le_tailMajorant_sub A a hA ha (k + J) (le_trans hJ (Nat.le_add_left _ _))
    have hc : ((k + J : ℕ) : ℝ) = (k : ℝ) + J := by push_cast; ring
    rwa [hc] at h
  have htel : ∑ k ∈ Finset.range N,
      (tailMajorant A a ((k : ℝ) + J) - tailMajorant A a (((k : ℝ) + 1) + J))
      = tailMajorant A a ((0 : ℝ) + J) - tailMajorant A a ((N : ℝ) + J) := by
    have := Finset.sum_range_sub' (f := fun k : ℕ => tailMajorant A a ((k : ℝ) + J)) N
    simpa using this
  have hsum : ∑ k ∈ Finset.range N, shellWeightNat A a (k + J)
      ≤ ∑ k ∈ Finset.range N,
          (tailMajorant A a ((k : ℝ) + J) - tailMajorant A a (((k : ℝ) + 1) + J)) := by
    refine Finset.sum_le_sum (fun k _ => ?_)
    have := hstep k
    have hc : (k : ℝ) + J + 1 = ((k : ℝ) + 1) + J := by ring
    rwa [hc] at this
  have hnn : 0 ≤ tailMajorant A a ((N : ℝ) + J) :=
    tailMajorant_nonneg hA ha (by positivity)
  have hz : tailMajorant A a ((0 : ℝ) + J) = tailMajorant A a J := by norm_num
  calc ∑ k ∈ Finset.range N, shellWeightNat A a (k + J) ≤ _ := hsum
    _ = tailMajorant A a ((0 : ℝ) + J) - tailMajorant A a ((N : ℝ) + J) := htel
    _ ≤ tailMajorant A a ((0 : ℝ) + J) := by linarith
    _ = tailMajorant A a J := hz

theorem tsum_natTail_le (A a : ℝ) (hA : 0 ≤ A) (ha : 0 ≤ a) (J : ℕ) (hJ : 1 ≤ J) :
    ∑' n : ℕ, natTail A a J n ≤ tailMajorant A a J := by
  have hsum := summable_natTail A a hA ha J
  have hsplit := hsum.sum_add_tsum_nat_add J
  have hzero : ∑ i ∈ Finset.range J, natTail A a J i = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have : i < J := Finset.mem_range.1 hi
    unfold natTail
    rw [if_neg (by omega)]
  have hshift : ∀ k : ℕ, natTail A a J (k + J) = shellWeightNat A a (k + J) := by
    intro k
    unfold natTail
    rw [if_pos (Nat.le_add_left _ _)]
  have : ∑' n : ℕ, natTail A a J n = ∑' k : ℕ, shellWeightNat A a (k + J) := by
    rw [← hsplit, hzero, zero_add]
    exact tsum_congr hshift
  rw [this]
  exact tsum_shellWeightNat_shift_le A a hA ha J hJ

/-! ## 4. The integer-index tail sum -/

/-- The far-shell bound: an explicit function of the cutoff `J`. -/
def farShellBound (A a : ℝ) (J : ℕ) : ℝ := 2 * tailMajorant A a J

theorem farShellBound_eq (A a : ℝ) (J : ℕ) :
    farShellBound A a J = 18 * A * Real.log (a + 4) / J + 72 * A / Real.sqrt J := by
  unfold farShellBound tailMajorant
  ring

theorem shellWeight_eq_shellWeightNat (A a : ℝ) (j : ℤ) :
    shellWeight A a j = shellWeightNat A a j.natAbs := by
  unfold shellWeight shellWeightNat
  have h : |(j : ℝ)| = (j.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    simp
  rw [h]

/-- **The truncated shell sum over the integer shells, for any finite set of
shells.** -/
theorem sum_truncShellWeight_le (A a : ℝ) (hA : 0 ≤ A) (ha : 0 ≤ a) (J : ℕ) (hJ : 1 ≤ J)
    (K : Finset ℤ) :
    ∑ j ∈ K, (if (J : ℤ) ≤ |j| then shellWeight A a j else 0) ≤ farShellBound A a J := by
  classical
  have hsum := summable_natTail A a hA ha J
  have hnn := natTail_nonneg A a hA ha J
  have hpoint : ∀ j : ℤ, (if (J : ℤ) ≤ |j| then shellWeight A a j else 0)
      = natTail A a J j.natAbs := by
    intro j
    have habs : |j| = (j.natAbs : ℤ) := Int.abs_eq_natAbs j
    by_cases h : (J : ℤ) ≤ |j|
    · have h' : J ≤ j.natAbs := by
        have h2 := h
        rw [habs] at h2
        exact_mod_cast h2
      rw [if_pos h]
      unfold natTail
      rw [if_pos h']
      exact shellWeight_eq_shellWeightNat A a j
    · have h' : ¬ J ≤ j.natAbs := by
        intro hc
        exact h (by rw [habs]; exact_mod_cast hc)
      rw [if_neg h]
      unfold natTail
      rw [if_neg h']
  simp only [hpoint]
  set F : ℕ → ℝ := natTail A a J with hF
  have hpos : ∑ j ∈ K.filter (fun j : ℤ => 0 ≤ j), F j.natAbs ≤ ∑' n : ℕ, F n := by
    have hinj : ∀ x ∈ K.filter (fun j : ℤ => 0 ≤ j), ∀ y ∈ K.filter (fun j : ℤ => 0 ≤ j),
        x.natAbs = y.natAbs → x = y := by
      intro x hx y hy h
      have hx0 : 0 ≤ x := (Finset.mem_filter.1 hx).2
      have hy0 : 0 ≤ y := (Finset.mem_filter.1 hy).2
      have : (x.natAbs : ℤ) = (y.natAbs : ℤ) := by exact_mod_cast h
      rwa [Int.natAbs_of_nonneg hx0, Int.natAbs_of_nonneg hy0] at this
    rw [← Finset.sum_image hinj]
    exact hsum.sum_le_tsum _ (fun n _ => hnn n)
  have hneg : ∑ j ∈ K.filter (fun j : ℤ => ¬ 0 ≤ j), F j.natAbs ≤ ∑' n : ℕ, F n := by
    have hinj : ∀ x ∈ K.filter (fun j : ℤ => ¬ 0 ≤ j), ∀ y ∈ K.filter (fun j : ℤ => ¬ 0 ≤ j),
        x.natAbs = y.natAbs → x = y := by
      intro x hx y hy h
      have hx0 : x ≤ 0 := le_of_lt (not_le.1 (Finset.mem_filter.1 hx).2)
      have hy0 : y ≤ 0 := le_of_lt (not_le.1 (Finset.mem_filter.1 hy).2)
      have : (x.natAbs : ℤ) = (y.natAbs : ℤ) := by exact_mod_cast h
      rw [Int.ofNat_natAbs_of_nonpos hx0, Int.ofNat_natAbs_of_nonpos hy0] at this
      linarith
    rw [← Finset.sum_image hinj]
    exact hsum.sum_le_tsum _ (fun n _ => hnn n)
  have hsplit : ∑ j ∈ K, F j.natAbs
      = ∑ j ∈ K.filter (fun j : ℤ => 0 ≤ j), F j.natAbs
        + ∑ j ∈ K.filter (fun j : ℤ => ¬ 0 ≤ j), F j.natAbs :=
    (Finset.sum_filter_add_sum_filter_not K _ _).symm
  have hle := tsum_natTail_le A a hA ha J hJ
  rw [hsplit]
  unfold farShellBound
  linarith

/-! ## 5. The quantitative far tail on the literal zeta carrier -/

/-- The quadratic zero weight truncated below the cutoff `J`. -/
def tailTermFrom (t : ℝ) (J : ℕ) (ρ : Zeros) : ℝ :=
  if (J : ℝ) ≤ |(ρ : ℂ).im - t| then
    ((zetaZeroConfig).mult (ρ : ℂ) : ℝ) / ((ρ : ℂ).im - t) ^ 2 else 0

theorem tailTermFrom_nonneg (t : ℝ) (J : ℕ) (ρ : Zeros) : 0 ≤ tailTermFrom t J ρ := by
  unfold tailTermFrom
  split
  · positivity
  · exact le_rfl

theorem tailTermFrom_le_tailTerm {J : ℕ} (hJ : 1 ≤ J) (t : ℝ) (ρ : Zeros) :
    tailTermFrom t J ρ ≤ tailTerm t ρ := by
  unfold tailTermFrom tailTerm
  split
  · rename_i h
    have h1 : (1:ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
    rw [if_pos (le_trans h1 h)]
  · positivity

theorem summable_tailTermFrom {J : ℕ} (hJ : 1 ≤ J) (t : ℝ) : Summable (tailTermFrom t J) :=
  Summable.of_nonneg_of_le (fun ρ => tailTermFrom_nonneg t J ρ)
    (fun ρ => tailTermFrom_le_tailTerm hJ t ρ) (summable_tailTerm t)

/-- **The far-shell quantitative tail bound with an explicit cutoff.**

For every sample ordinate `t` and every natural cutoff `J ≥ 1`, the quadratic
zero weight of the literal carrier beyond the cutoff is bounded by the explicit
quantity `farShellBound A |t| J = 18 A log(|t|+4)/J + 72 A/√J`, where `A` is the
constant of the unconditional local zero count. -/
theorem tsum_tailTermFrom_le {A : ℝ} (hA1 : 1 ≤ A)
    (hloc : ∀ τ : ℝ, ((zetaZeroConfig).N τ (τ + 1) : ℝ) ≤ A * Real.log (|τ| + 3))
    (t : ℝ) (J : ℕ) (hJ : 1 ≤ J) :
    ∑' ρ : Zeros, tailTermFrom t J ρ ≤ farShellBound A |t| J := by
  classical
  have hA : (0:ℝ) ≤ A := le_trans zero_le_one hA1
  refine Real.tsum_le_of_sum_le (fun ρ => tailTermFrom_nonneg t J ρ) (fun s => ?_)
  set K : Finset ℤ := s.image (fun x : Zeros => shellIdx t (x : ℂ)) with hK
  have hmaps : ∀ x ∈ s, shellIdx t (x : ℂ) ∈ K := fun x hx => Finset.mem_image_of_mem _ hx
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (tailTermFrom t J)]
  have hfib : ∀ j ∈ K,
      (∑ x ∈ s with shellIdx t x.1 = j, tailTermFrom t J x)
        ≤ (if (J : ℤ) ≤ |j| then shellWeight A |t| j else 0) := by
    intro j _
    set F : Finset Zeros := s.filter (fun x => shellIdx t (x : ℂ) = j) with hF
    by_cases hjJ : (J : ℤ) ≤ |j|
    · rw [if_pos hjJ]
      set d : ℝ := max 1 (|(j : ℝ)| - 1) with hd
      have hd0 : (0:ℝ) < d := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      have step1 : (∑ x ∈ F, tailTermFrom t J x)
          ≤ ∑ x ∈ F, ((zetaZeroConfig).mult (x : ℂ) : ℝ) / d ^ 2 := by
        refine Finset.sum_le_sum ?_
        intro x hx
        have hxj : shellIdx t (x : ℂ) = j := (Finset.mem_filter.1 hx).2
        unfold tailTermFrom
        split
        · rename_i hge
          have hJ1 : (1:ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
          have hge1 : (1:ℝ) ≤ |(x : ℂ).im - t| := le_trans hJ1 hge
          have hgap : d ≤ |(x : ℂ).im - t| := by
            rw [hd, ← hxj]; exact shell_gap_lower _ hge1
          have hsq : d ^ 2 ≤ ((x : ℂ).im - t) ^ 2 := by
            have := pow_le_pow_left₀ hd0.le hgap 2
            simpa [sq_abs] using this
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
        · positivity
      have hinj : ∀ x ∈ F, ∀ y ∈ F, (x : ℂ) = (y : ℂ) → x = y :=
        fun x _ y _ h => Subtype.ext h
      have step2 : (∑ x ∈ F, ((zetaZeroConfig).mult (x : ℂ) : ℝ))
          = ((∑ ρ ∈ F.image (fun x : Zeros => (x : ℂ)), (zetaZeroConfig).mult ρ : ℕ) : ℝ) := by
        rw [Finset.sum_image hinj]
        push_cast
        rfl
      have hsub : ↑(F.image (fun x : Zeros => (x : ℂ)))
          ⊆ (zetaZeroConfig).window (t + (j : ℝ) - 1) (t + (j : ℝ)) := by
        intro ρ hρ
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hρ
        obtain ⟨x, hxF, rfl⟩ := hρ
        have hxj : shellIdx t (x : ℂ) = j := (Finset.mem_filter.1 hxF).2
        have := mem_window_shell t (x : ℂ) x.2
        rwa [hxj] at this
      have step3 : ((∑ ρ ∈ F.image (fun x : Zeros => (x : ℂ)), (zetaZeroConfig).mult ρ : ℕ) : ℝ)
          ≤ ((zetaZeroConfig).N (t + (j : ℝ) - 1) (t + (j : ℝ)) : ℝ) := by
        exact_mod_cast sum_mult_le_N _ _ _ hsub
      have hlocj := hloc (t + (j : ℝ) - 1)
      have hwin : t + (j : ℝ) - 1 + 1 = t + (j : ℝ) := by ring
      rw [hwin] at hlocj
      have hlog : Real.log (|t + (j : ℝ) - 1| + 3) ≤ Real.log (|t| + |(j : ℝ)| + 4) := by
        apply Real.log_le_log (by positivity)
        have hb := abs_add_le (t + (j : ℝ)) (-1)
        simp only [abs_neg, abs_one] at hb
        have ha := abs_add_le t ((j : ℝ))
        have hrw : t + (j : ℝ) - 1 = t + (j : ℝ) + (-1) := by ring
        rw [hrw]
        linarith
      have step4 : ((zetaZeroConfig).N (t + (j : ℝ) - 1) (t + (j : ℝ)) : ℝ)
          ≤ A * Real.log (|t| + |(j : ℝ)| + 4) := by
        refine le_trans hlocj ?_
        exact mul_le_mul_of_nonneg_left hlog hA
      calc (∑ x ∈ F, tailTermFrom t J x)
          ≤ ∑ x ∈ F, ((zetaZeroConfig).mult (x : ℂ) : ℝ) / d ^ 2 := step1
        _ = (∑ x ∈ F, ((zetaZeroConfig).mult (x : ℂ) : ℝ)) / d ^ 2 := by rw [Finset.sum_div]
        _ ≤ (A * Real.log (|t| + |(j : ℝ)| + 4)) / d ^ 2 := by
            apply div_le_div_of_nonneg_right ?_ (by positivity)
            rw [step2]; exact le_trans step3 step4
        _ = shellWeight A |t| j := by rw [shellWeight, hd]
    · rw [if_neg hjJ]
      refine le_of_eq (Finset.sum_eq_zero (fun x hx => ?_))
      have hxj : shellIdx t (x : ℂ) = j := (Finset.mem_filter.1 hx).2
      unfold tailTermFrom
      rw [if_neg]
      intro hge
      -- a zero at distance ≥ J lies in a shell of index of absolute value ≥ J
      apply hjJ
      rw [← hxj]
      unfold shellIdx
      set y : ℝ := (x : ℂ).im - t with hy
      rcases le_or_gt (J : ℝ) y with hcase | hcase
      · have : (J : ℤ) ≤ ⌈y⌉ := by
          have : (J : ℤ) ≤ ⌈y⌉ := Int.le_ceil_iff.2 (by push_cast; linarith [Int.le_ceil y])
          exact this
        exact le_trans this (le_abs_self _)
      · have hneg : y ≤ -(J : ℝ) := by
          have habs : (J : ℝ) ≤ |y| := hge
          rcases abs_cases y with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exfalso; rw [h1] at habs; linarith
          · rw [h1] at habs; linarith
        have hc : ⌈y⌉ ≤ -(J : ℤ) := by
          apply Int.ceil_le.2
          push_cast
          linarith
        have : (J : ℤ) ≤ -⌈y⌉ := by omega
        exact le_trans this (neg_le_abs _)
  calc (∑ j ∈ K, ∑ x ∈ s with shellIdx t x.1 = j, tailTermFrom t J x)
      ≤ ∑ j ∈ K, (if (J : ℤ) ≤ |j| then shellWeight A |t| j else 0) := Finset.sum_le_sum hfib
    _ ≤ farShellBound A |t| J := sum_truncShellWeight_le A |t| hA (abs_nonneg t) J hJ K

/-- **The far-shell tail bound, with the constant supplied by the unconditional
local zero count.** -/
theorem exists_uniform_farShellBound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (t : ℝ) (J : ℕ), 1 ≤ J →
      ∑' ρ : Zeros, tailTermFrom t J ρ ≤ farShellBound A |t| J := by
  obtain ⟨A, hA1, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  exact ⟨A, hA1, fun t J hJ => tsum_tailTermFrom_le hA1 hloc t J hJ⟩

/-! ## 6. The cutoff can be chosen to make the far tail arbitrarily small -/

theorem tailMajorant_tendsto_zero (A a : ℝ) :
    Filter.Tendsto (fun J : ℕ => tailMajorant A a J) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun J : ℕ => 9 * A * Real.log (a + 4) / (J : ℝ))
      Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.const_mul
        (9 * A * Real.log (a + 4))
  have h2 : Filter.Tendsto (fun J : ℕ => 36 * A / Real.sqrt (J : ℝ))
      Filter.atTop (nhds 0) := by
    have hs : Filter.Tendsto (fun J : ℕ => Real.sqrt (J : ℝ)) Filter.atTop Filter.atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [div_eq_mul_inv] using hs.inv_tendsto_atTop.const_mul (36 * A)
  have := h1.add h2
  simpa [tailMajorant] using this

theorem farShellBound_tendsto_zero (A a : ℝ) :
    Filter.Tendsto (fun J : ℕ => farShellBound A a J) Filter.atTop (nhds 0) := by
  have := (tailMajorant_tendsto_zero A a).const_mul 2
  simpa [farShellBound] using this

/-- **Explicit cutoff selection.**  Given any accuracy `ε > 0`, there is a cutoff
`J` beyond which the literal quadratic far tail is below `ε`. -/
theorem exists_cutoff_tail_lt {A : ℝ} (hA1 : 1 ≤ A)
    (hloc : ∀ τ : ℝ, ((zetaZeroConfig).N τ (τ + 1) : ℝ) ≤ A * Real.log (|τ| + 3))
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, 1 ≤ J ∧ ∑' ρ : Zeros, tailTermFrom t J ρ < ε := by
  have hlim := farShellBound_tendsto_zero A |t|
  have hev : ∀ᶠ J : ℕ in Filter.atTop, farShellBound A |t| J < ε := by
    have := hlim.eventually (eventually_lt_nhds hε)
    simpa using this
  obtain ⟨J, hJ⟩ := (hev.and (Filter.eventually_ge_atTop 1)).exists
  exact ⟨J, hJ.2, lt_of_le_of_lt (tsum_tailTermFrom_le hA1 hloc t J hJ.2) hJ.1⟩

end FarShellCutoffTailBound
end Zeta23Bridge
