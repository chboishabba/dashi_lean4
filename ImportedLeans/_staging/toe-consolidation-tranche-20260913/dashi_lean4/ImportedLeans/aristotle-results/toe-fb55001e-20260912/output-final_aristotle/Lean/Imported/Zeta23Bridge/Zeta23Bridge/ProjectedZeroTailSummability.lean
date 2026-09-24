/-
# Summability of the projected far zero tail on the literal zeta carrier

`ReflectionPairKernelDecay` bounds the two-sample cone response of a single
functional-equation pair of zeros by

    m_ρ · (curvature constant) / (Im ρ − t)² .

To turn that per-pair estimate into an estimate for the whole projected tail one
must sum it over the *infinite* literal zero carrier.  This module supplies the
missing aggregation: on the actual carrier of `Zeta23.zetaZeroConfig`, the
family

    ρ ↦ m_ρ / (Im ρ − t)²      (restricted to |Im ρ − t| ≥ 1)

is summable, with an explicit majorant.

The only input about ζ is the *proved, unconditional* local zero count
`Zeta23.RvM.zetaZeroConfig_local_count`:

    N(τ, τ+1] ≤ A₀ · log (|τ| + 3)   for all real τ.

The argument groups the carrier into the unit ordinate shells
`Im ρ ∈ (t + j − 1, t + j]`, `j : ℤ`, indexed by `⌈Im ρ − t⌉`; each shell is a
single counting window, its total multiplicity is `≤ A₀ log(|t| + |j| + 4)`,
and every zero in it has `|Im ρ − t| ≥ max 1 (|j| − 1)`.  The resulting
majorant `A₀ log(|t| + |j| + 4) / max 1 (|j| − 1)²` is summable over `ℤ`
because `log (a + n + 4) ≤ log (a + 4) + 2 √(n+1)`.

No `sorry`, no `axiom`, no Boolean receipt, no numerical evidence.
-/
import Zeta23Bridge.ReflectionPairCurvatureBound
import Zeta23.RvM.LocalCount

noncomputable section

open scoped Real
open Zeta23

namespace Zeta23Bridge
namespace ProjectedZeroTailSummability

open MeasureTheory
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOtherZerosChannel
open Zeta23Bridge.LiteralWeilOffOrdinateProjectiveTail
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair
open Zeta23Bridge.ReflectionPairKernelDecay
open Zeta23Bridge.ReflectionPairCurvatureBound

/-! ## 1. The scalar shell majorant -/

/-- The shell majorant, as a function of the (natural) shell index. -/
def shellWeightNat (A a : ℝ) (n : ℕ) : ℝ :=
  A * Real.log (a + n + 4) / (max 1 ((n : ℝ) - 1)) ^ 2

/-- `(n+1)/3 ≤ max 1 (n−1)` for every natural `n`. -/
theorem den_lower (n : ℕ) : ((n : ℝ) + 1) / 3 ≤ max 1 ((n : ℝ) - 1) := by
  rcases le_or_gt (n : ℝ) 2 with h | h
  · exact le_trans (by linarith) (le_max_left _ _)
  · exact le_trans (by linarith) (le_max_right _ _)

/-- `log (a + n + 4) ≤ log (a + 4) + 2 (n+1)^{1/2}`. -/
theorem log_shift_le (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    Real.log (a + n + 4) ≤ Real.log (a + 4) + 2 * ((n : ℝ) + 1) ^ ((1:ℝ)/2) := by
  have hle : a + n + 4 ≤ (a + 4) * ((n : ℝ) + 1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have h1 : Real.log (a + n + 4) ≤ Real.log (a + 4) + Real.log ((n : ℝ) + 1) := by
    calc Real.log (a + n + 4) ≤ Real.log ((a + 4) * ((n : ℝ) + 1)) :=
          Real.log_le_log (by positivity) hle
      _ = Real.log (a + 4) + Real.log ((n : ℝ) + 1) := Real.log_mul (by linarith) (by positivity)
  have h2 := Real.log_le_rpow_div (x := (n:ℝ)+1) (ε := (1:ℝ)/2) (by positivity) (by norm_num)
  have h3 : Real.log ((n:ℝ)+1) ≤ 2 * ((n:ℝ)+1) ^ ((1:ℝ)/2) := by
    simpa using by linarith [h2]
  linarith

/-- The shell majorant is `O(n^{-3/2})`. -/
theorem shellWeightNat_le (A a : ℝ) (hA : 0 ≤ A) (ha : 0 ≤ a) (n : ℕ) :
    shellWeightNat A a n
      ≤ (9 * A * Real.log (a + 4) + 18 * A) / ((n : ℝ) + 1) ^ ((3:ℝ)/2) := by
  set x : ℝ := (n : ℝ) + 1 with hxdef
  have hx1 : (1:ℝ) ≤ x := by simp [hxdef]
  have hx0 : (0:ℝ) < x := by linarith
  have hD : x / 3 ≤ max 1 ((n : ℝ) - 1) := den_lower n
  have hD0 : (0:ℝ) < x / 3 := by positivity
  have hlognn : 0 ≤ Real.log (a + n + 4) := Real.log_nonneg (by
    have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith)
  have hloga : 0 ≤ Real.log (a + 4) := Real.log_nonneg (by linarith)
  have step1 : shellWeightNat A a n ≤ A * Real.log (a + n + 4) / (x / 3) ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ (le_of_lt hD0) hD 2
  have step2 : A * Real.log (a + n + 4) / (x / 3) ^ 2
      ≤ A * (Real.log (a + 4) + 2 * x ^ ((1:ℝ)/2)) / (x / 3) ^ 2 := by
    apply div_le_div_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left (log_shift_le a ha n) hA
  have hxr2 : x ^ ((2:ℝ)) = x ^ (2:ℕ) := by
    rw [← Real.rpow_natCast x 2]; norm_num
  have hhalf : x ^ ((1:ℝ)/2) * x ^ ((3:ℝ)/2) = x ^ (2:ℕ) := by
    rw [← Real.rpow_add hx0, ← hxr2]; norm_num
  have hmono : x ^ ((3:ℝ)/2) ≤ x ^ (2:ℕ) := by
    rw [← hxr2]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hp0 : (0:ℝ) < x ^ ((3:ℝ)/2) := Real.rpow_pos_of_pos hx0 _
  have hx20 : (0:ℝ) < x ^ (2:ℕ) := by positivity
  have e1 : (1:ℝ) / x ^ (2:ℕ) ≤ 1 / x ^ ((3:ℝ)/2) := one_div_le_one_div_of_le hp0 hmono
  have e2 : x ^ ((1:ℝ)/2) / x ^ (2:ℕ) = 1 / x ^ ((3:ℝ)/2) := by
    field_simp
    linarith [hhalf]
  have expand : A * (Real.log (a + 4) + 2 * x ^ ((1:ℝ)/2)) / (x / 3) ^ 2
      = 9 * A * Real.log (a + 4) * (1 / x ^ (2:ℕ))
        + 18 * A * (x ^ ((1:ℝ)/2) / x ^ (2:ℕ)) := by
    field_simp
    ring
  have final : 9 * A * Real.log (a + 4) * (1 / x ^ (2:ℕ))
        + 18 * A * (x ^ ((1:ℝ)/2) / x ^ (2:ℕ))
      ≤ (9 * A * Real.log (a + 4) + 18 * A) / x ^ ((3:ℝ)/2) := by
    rw [e2]
    have h1 : 9 * A * Real.log (a + 4) * (1 / x ^ (2:ℕ))
        ≤ 9 * A * Real.log (a + 4) * (1 / x ^ ((3:ℝ)/2)) :=
      mul_le_mul_of_nonneg_left e1 (by positivity)
    have hsplit : (9 * A * Real.log (a + 4) + 18 * A) / x ^ ((3:ℝ)/2)
        = 9 * A * Real.log (a + 4) * (1 / x ^ ((3:ℝ)/2)) + 18 * A * (1 / x ^ ((3:ℝ)/2)) := by
      field_simp
    rw [hsplit]
    linarith
  calc shellWeightNat A a n ≤ A * Real.log (a + n + 4) / (x / 3) ^ 2 := step1
    _ ≤ A * (Real.log (a + 4) + 2 * x ^ ((1:ℝ)/2)) / (x / 3) ^ 2 := step2
    _ = _ := expand
    _ ≤ _ := final

theorem shellWeightNat_nonneg (A a : ℝ) (hA : 0 ≤ A) (ha : 0 ≤ a) (n : ℕ) :
    0 ≤ shellWeightNat A a n := by
  unfold shellWeightNat
  have : (0:ℝ) ≤ Real.log (a + n + 4) := Real.log_nonneg (by
    have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith)
  positivity

theorem summable_shellWeightNat (A a : ℝ) (hA : 0 ≤ A) (ha : 0 ≤ a) :
    Summable (shellWeightNat A a) := by
  have hmaj : Summable (fun n : ℕ =>
      (9 * A * Real.log (a + 4) + 18 * A) / ((n : ℝ) + 1) ^ ((3:ℝ)/2)) := by
    have h := (Real.summable_one_div_nat_rpow (p := (3:ℝ)/2)).2 (by norm_num)
    have h2 := (summable_nat_add_iff 1).2 h
    have h3 : Summable (fun n : ℕ => 1 / ((n:ℝ)+1) ^ ((3:ℝ)/2)) := by simpa using h2
    simpa [div_eq_mul_inv, mul_comm] using h3.mul_left (9 * A * Real.log (a + 4) + 18 * A)
  exact Summable.of_nonneg_of_le (fun n => shellWeightNat_nonneg A a hA ha n)
    (fun n => shellWeightNat_le A a hA ha n) hmaj

/-- The shell majorant on the integer shell index. -/
def shellWeight (A a : ℝ) (j : ℤ) : ℝ :=
  A * Real.log (a + |(j : ℝ)| + 4) / (max 1 (|(j : ℝ)| - 1)) ^ 2

theorem shellWeight_nonneg (A a : ℝ) (hA : 0 ≤ A) (ha : 0 ≤ a) (j : ℤ) :
    0 ≤ shellWeight A a j := by
  unfold shellWeight
  have : (0:ℝ) ≤ Real.log (a + |(j:ℝ)| + 4) := Real.log_nonneg (by
    have := abs_nonneg ((j : ℝ)); linarith)
  positivity

theorem summable_shellWeight (A a : ℝ) (hA : 0 ≤ A) (ha : 0 ≤ a) :
    Summable (shellWeight A a) := by
  refine Summable.of_nat_of_neg ?_ ?_
  · have : (fun n : ℕ => shellWeight A a (n : ℤ)) = shellWeightNat A a := by
      funext n
      simp [shellWeight, shellWeightNat, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
    rw [this]; exact summable_shellWeightNat A a hA ha
  · have : (fun n : ℕ => shellWeight A a (-(n : ℤ))) = shellWeightNat A a := by
      funext n
      simp [shellWeight, shellWeightNat, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
    rw [this]; exact summable_shellWeightNat A a hA ha

/-! ## 2. Shell geometry on the literal carrier -/

/-- The shell index of a point of the carrier relative to the sample ordinate `t`. -/
def shellIdx (t : ℝ) (ρ : ℂ) : ℤ := ⌈ρ.im - t⌉

/-- Every carrier point lies in the single counting window determined by its shell. -/
theorem mem_window_shell (t : ℝ) (ρ : ℂ) (hρ : ρ ∈ (zetaZeroConfig).carrier) :
    ρ ∈ (zetaZeroConfig).window (t + (shellIdx t ρ : ℝ) - 1) (t + (shellIdx t ρ : ℝ)) := by
  refine ⟨hρ, ?_, ?_⟩
  · have := Int.ceil_lt_add_one (ρ.im - t); simp only [shellIdx]; linarith
  · have := Int.le_ceil (ρ.im - t); simp only [shellIdx]; linarith

/-- A point of shell `j` at distance at least `1` from `t` has
`|Im ρ − t| ≥ max 1 (|j| − 1)`. -/
theorem shell_gap_lower (x : ℝ) (hx : 1 ≤ |x|) :
    max 1 (|(⌈x⌉ : ℝ)| - 1) ≤ |x| := by
  have h1 : (⌈x⌉ : ℝ) - 1 < x := by have := Int.ceil_lt_add_one x; linarith
  have h2 : x ≤ (⌈x⌉ : ℝ) := Int.le_ceil x
  refine max_le hx ?_
  rcases le_or_gt 0 x with hpos | hneg
  · have hj : 0 ≤ (⌈x⌉ : ℝ) := le_trans hpos h2
    rw [abs_of_nonneg hj, abs_of_nonneg hpos]; linarith
  · have hj0 : ⌈x⌉ ≤ 0 := Int.ceil_nonpos.2 hneg.le
    have hj : (⌈x⌉ : ℝ) ≤ 0 := by exact_mod_cast hj0
    rw [abs_of_nonpos hj, abs_of_neg hneg]; linarith

/-- A finite set of carrier points inside a counting window carries at most the
window's total multiplicity. -/
theorem sum_mult_le_N (T₁ T₂ : ℝ) (F : Finset ℂ)
    (hF : ↑F ⊆ (zetaZeroConfig).window T₁ T₂) :
    ∑ ρ ∈ F, (zetaZeroConfig).mult ρ ≤ (zetaZeroConfig).N T₁ T₂ := by
  classical
  have hfin : ((zetaZeroConfig).window T₁ T₂).Finite := zetaZeroConfig.finite_window T₁ T₂
  have h2 := finsum_mem_coe_finset (zetaZeroConfig.mult) hfin.toFinset
  rw [hfin.coe_toFinset] at h2
  have hNW : (zetaZeroConfig).N T₁ T₂ = ∑ ρ ∈ hfin.toFinset, (zetaZeroConfig).mult ρ := h2
  rw [hNW]
  exact Finset.sum_le_sum_of_subset (fun x hx => hfin.mem_toFinset.2 (hF hx))

/-! ## 3. The projected tail is summable -/

/-- The far part of the literal quadratic zero-tail weight at the sample
ordinate `t`: `m_ρ / (Im ρ − t)²`, truncated to the zeros at ordinate distance
at least `1`. -/
def tailTerm (t : ℝ) (ρ : Zeros) : ℝ :=
  if 1 ≤ |(ρ : ℂ).im - t| then ((zetaZeroConfig).mult (ρ : ℂ) : ℝ) / ((ρ : ℂ).im - t) ^ 2 else 0

theorem tailTerm_nonneg (t : ℝ) (ρ : Zeros) : 0 ≤ tailTerm t ρ := by
  unfold tailTerm
  split
  · positivity
  · exact le_refl 0

/-- **The far zero tail is summable on the literal carrier.**

For every sample ordinate `t`, the family `ρ ↦ m_ρ / (Im ρ − t)²` over the
actual nontrivial zeros of `ζ` at ordinate distance at least `1` from `t` is
summable.  Combined with `ReflectionPairKernelDecay.abs_zeroConeValue_add_reflect_le`
this makes the reflection-symmetrized far tail of the literal explicit formula
an absolutely convergent object. -/
theorem summable_tailTerm (t : ℝ) : Summable (tailTerm t) := by
  classical
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  have hA0 : (0:ℝ) ≤ A₀ := le_trans zero_le_one hA₀
  have hsum := summable_shellWeight A₀ |t| hA0 (abs_nonneg t)
  have hwnn : ∀ j : ℤ, 0 ≤ shellWeight A₀ |t| j :=
    fun j => shellWeight_nonneg A₀ |t| hA0 (abs_nonneg t) j
  refine summable_of_sum_le (c := ∑' j : ℤ, shellWeight A₀ |t| j)
    (fun ρ => tailTerm_nonneg t ρ) (fun s => ?_)
  set K : Finset ℤ := s.image (fun x : Zeros => shellIdx t (x : ℂ)) with hK
  have hmaps : ∀ x ∈ s, shellIdx t (x : ℂ) ∈ K := fun x hx => Finset.mem_image_of_mem _ hx
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (tailTerm t)]
  have hfib : ∀ j ∈ K,
      (∑ x ∈ s with shellIdx t x.1 = j, tailTerm t x) ≤ shellWeight A₀ |t| j := by
    intro j _
    set F : Finset Zeros := s.filter (fun x => shellIdx t (x : ℂ) = j) with hF
    set d : ℝ := max 1 (|(j : ℝ)| - 1) with hd
    have hd0 : (0:ℝ) < d := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    -- (a) pointwise: replace the true gap by the shell lower bound
    have step1 : (∑ x ∈ F, tailTerm t x)
        ≤ ∑ x ∈ F, ((zetaZeroConfig).mult (x : ℂ) : ℝ) / d ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro x hx
      have hxj : shellIdx t (x : ℂ) = j := (Finset.mem_filter.1 hx).2
      unfold tailTerm
      split
      · rename_i hge
        have hgap : d ≤ |(x : ℂ).im - t| := by
          rw [hd, ← hxj]; exact shell_gap_lower _ hge
        have hsq : d ^ 2 ≤ ((x : ℂ).im - t) ^ 2 := by
          have := pow_le_pow_left₀ hd0.le hgap 2
          simpa [sq_abs] using this
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
      · positivity
    -- (b) the multiplicity sum is a window count
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
    -- (c) the local zero count
    have hlocj := hloc (t + (j : ℝ) - 1)
    have hwin : t + (j : ℝ) - 1 + 1 = t + (j : ℝ) := by ring
    rw [hwin] at hlocj
    have hlog : Real.log (|t + (j : ℝ) - 1| + 3) ≤ Real.log (|t| + |(j : ℝ)| + 4) := by
      apply Real.log_le_log (by positivity)
      have ha := abs_add_le t ((j : ℝ))
      have hb := abs_add_le (t + (j : ℝ)) (-1)
      simp only [abs_neg, abs_one] at hb
      have hrw : t + (j : ℝ) - 1 = t + (j : ℝ) + (-1) := by ring
      rw [hrw]
      linarith
    have step4 : ((zetaZeroConfig).N (t + (j : ℝ) - 1) (t + (j : ℝ)) : ℝ)
        ≤ A₀ * Real.log (|t| + |(j : ℝ)| + 4) := by
      refine le_trans hlocj ?_
      exact mul_le_mul_of_nonneg_left hlog hA0
    calc (∑ x ∈ F, tailTerm t x)
        ≤ ∑ x ∈ F, ((zetaZeroConfig).mult (x : ℂ) : ℝ) / d ^ 2 := step1
      _ = (∑ x ∈ F, ((zetaZeroConfig).mult (x : ℂ) : ℝ)) / d ^ 2 := by
          rw [Finset.sum_div]
      _ ≤ (A₀ * Real.log (|t| + |(j : ℝ)| + 4)) / d ^ 2 := by
          apply div_le_div_of_nonneg_right ?_ (by positivity)
          rw [step2]; exact le_trans step3 step4
      _ = shellWeight A₀ |t| j := by rw [shellWeight, hd]
  calc (∑ j ∈ K, ∑ x ∈ s with shellIdx t x.1 = j, tailTerm t x)
      ≤ ∑ j ∈ K, shellWeight A₀ |t| j := Finset.sum_le_sum hfib
    _ ≤ ∑' j : ℤ, shellWeight A₀ |t| j := hsum.sum_le_tsum K (fun i _ => hwnn i)

/-! ## 4. Absolute convergence of the signed reflection-symmetrized far tail -/

/-- **The reflection-symmetrized far tail converges absolutely.**

Given a real-even compactly supported `C²` taper `g` whose reflection-pair
curvature constants are uniformly bounded over the carrier by `C`, the family of
signed two-sample cone responses of the functional-equation pairs, restricted to
the zeros at ordinate distance at least `1` from the sample point `t`, is
absolutely summable.

This is the aggregation step: `abs_zeroConeValue_add_reflect_le` gives the
`δ^{-2}` decay of a single pair, and `summable_tailTerm` sums it over the actual
infinite zero carrier of `ζ` using the unconditional local zero count. -/
theorem summable_reflection_far_tail {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u)
    (t : ℝ) (C : ℝ) (hC : ∀ ρ : Zeros, pairWeightCurvature g (heightOf ρ) ≤ C) :
    Summable (fun ρ : Zeros =>
      if 1 ≤ |(ρ : ℂ).im - t| then
        |zeroConeValue g t 0 ρ + zeroConeValue g t 0 (reflectZero ρ)| else 0) := by
  classical
  refine Summable.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_)
    ((summable_tailTerm t).mul_left C)
  · split
    · exact abs_nonneg _
    · exact le_refl 0
  · by_cases hρ : 1 ≤ |(ρ : ℂ).im - t|
    · have hδ : ((ρ : ℂ).im - t) ≠ 0 := by
        intro h; rw [h] at hρ; simp at hρ; linarith
      have h1 := abs_zeroConeValue_add_reflect_le hg hgc heven t ρ hδ
      have hsq : (0:ℝ) < ((ρ : ℂ).im - t) ^ 2 := by positivity
      have hmul : ((zetaZeroConfig).mult (ρ : ℂ) : ℝ)
            * (pairWeightCurvature g (heightOf ρ) / ((ρ : ℂ).im - t) ^ 2)
          ≤ C * tailTerm t ρ := by
        unfold tailTerm
        rw [if_pos hρ]
        have hm : (0:ℝ) ≤ ((zetaZeroConfig).mult (ρ : ℂ) : ℝ) := Nat.cast_nonneg _
        have hnum : ((zetaZeroConfig).mult (ρ : ℂ) : ℝ) * pairWeightCurvature g (heightOf ρ)
            ≤ C * ((zetaZeroConfig).mult (ρ : ℂ) : ℝ) := by
          nlinarith [hC ρ]
        have e1 : ((zetaZeroConfig).mult (ρ : ℂ) : ℝ)
              * (pairWeightCurvature g (heightOf ρ) / ((ρ : ℂ).im - t) ^ 2)
            = (((zetaZeroConfig).mult (ρ : ℂ) : ℝ) * pairWeightCurvature g (heightOf ρ))
              / ((ρ : ℂ).im - t) ^ 2 := by ring
        have e2 : C * (((zetaZeroConfig).mult (ρ : ℂ) : ℝ) / ((ρ : ℂ).im - t) ^ 2)
            = (C * ((zetaZeroConfig).mult (ρ : ℂ) : ℝ)) / ((ρ : ℂ).im - t) ^ 2 := by ring
        rw [e1, e2]
        exact div_le_div_of_nonneg_right hnum hsq.le
      simp only [if_pos hρ]
      exact le_trans h1 hmul
    · simp only [if_neg hρ]
      unfold tailTerm
      rw [if_neg hρ, mul_zero]

/-- **Unconditional absolute convergence of the signed reflection-symmetrized
far tail.**

For *any* compactly supported `C²` real-even taper `g`, the signed two-sample
cone responses of the functional-equation pairs of the actual nontrivial zeros
of `ζ`, restricted to the zeros at ordinate distance at least `1` from the
sample point `t`, form an absolutely summable family.  The uniform curvature
constant is supplied by
`ReflectionPairCurvatureBound.exists_uniform_carrier_curvature_bound`, using only
that every zero of the strip has horizontal height at most `1/2`. -/
theorem summable_reflection_far_tail_uniform {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u)
    (t : ℝ) :
    Summable (fun ρ : Zeros =>
      if 1 ≤ |(ρ : ℂ).im - t| then
        |zeroConeValue g t 0 ρ + zeroConeValue g t 0 (reflectZero ρ)| else 0) := by
  obtain ⟨C, hC⟩ := exists_uniform_carrier_curvature_bound hg hgc
  exact summable_reflection_far_tail hg hgc heven t C hC

end ProjectedZeroTailSummability
end Zeta23Bridge
