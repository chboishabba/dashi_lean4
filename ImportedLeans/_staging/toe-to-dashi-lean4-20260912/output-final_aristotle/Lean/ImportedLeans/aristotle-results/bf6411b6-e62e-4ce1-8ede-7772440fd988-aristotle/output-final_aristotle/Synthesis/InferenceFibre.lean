import Synthesis.StatisticsFibre
import AgdaMirror.Vec15Descriptive
import AgdaMirror.Vec15Inference
import AgdaMirror.Vec15Robust

/-!
# Synthesis layer 2''''': the descriptive / inference / robust layers land in the mask fibre

`Synthesis.StatisticsFibre` showed that the *order* layer on the 15-lane carrier
(`AgdaMirror.Vec15Order`) is the fibre over the supersingular prime base and that
its threshold masks are Monster masks.  Three further 15-lane layers were left
unexamined in the dependency map (obligation 9):

* `AgdaMirror.Vec15Descriptive` — total mass `sum15`, the non-zero count
  `countNonZero15`, extrema and spread;
* `AgdaMirror.Vec15Inference` — a Boolean decision surface (`baselineDecision`,
  `pairDecision`) built from `sum15` and `countNonZero15`;
* `AgdaMirror.Vec15Robust` — fence masks, winsorisation and the robust summaries.

Proved here (all of it a genuine transport, none of it numerology):

* `sum15_eq_sum_base` — the descriptive total mass is the sum over the prime base;
* `supportMask`, `countNonZero15_eq_card` — the non-zero count is the cardinality
  of the support mask, an element of `MaskSSP`;
* `supportMask_eq_not_thresholdMask_zero`, `countNonZero15_add_rank15_zero` — the
  support mask is exactly the complement of the order layer's threshold mask at
  `0`, so support and rank partition the fifteen primes;
* `baselineDecision_failToReject_iff` — **the inference layer's decision surface
  is a mask detector**: the baseline test fails to reject exactly when the
  carrier *is* a Boolean mask over the base, i.e. `v = maskCarrier (supportMask v)`;
  `pairDecision_failToReject_iff` says the paired test fails to reject exactly
  when both carriers are masks;
* `supportMask_mono`, `supportMask_dvd`, `supportMask_dSSP_empty_mono` — the
  support mask is monotone in the carrier, hence a divisibility chain in the mask
  arithmetic of `Synthesis.MoonshineBase` and a monotone path away from the
  collapse mask in the supplied ultrametric;
* `outsideFenceMask15_fibre`, `winsorize15_eq_off_outlierMask` — the robust
  layer's fence masks are Monster masks, and winsorisation is the identity off
  the outlier mask.

Boundary: the statistical vocabulary (test, p-value, quartile, outlier) is the
source material's naming for operations on a 15-tuple of naturals.  No
statistical or physical claim is made or used; every statement below is a
statement about finite carriers.
-/

namespace Synthesis.InferenceFibre

open AgdaMirror.MonsterOntos (SSP)
open AgdaMirror.GodelLattice (Vec15)
open AgdaMirror.Vec15Order (PrimeCarrier15 countMask15 countBool natLeqBool rank15 clampNat)
open AgdaMirror.Vec15Descriptive (sum15 countNonZero15 countNonZeroNat)
open AgdaMirror.Vec15Inference (Decision leqNat leqNat_iff baselineDecision pairDecision
  pairStatistic pairPValue)
open AgdaMirror.Vec15Robust (outsideFenceMask15 notBool andBool leqNatBool winsorize15
  tukeyOutlierMask15)
open Synthesis.MonsterFibre
open Synthesis.Vec15Fibre
open Synthesis.MoonshineBase
open Synthesis.StatisticsFibre

/-! ## The descriptive layer -/

/-- The descriptive total mass is the sum over the prime base. -/
theorem sum15_eq_sum_base (v : PrimeCarrier15) :
    sum15 v = ∑ p : SSP, vec15Equiv v p :=
  vec15Equiv_sum v

/-- The **support mask** of a carrier: the primes whose lane is non-zero. -/
def supportMask (v : PrimeCarrier15) : MaskSSP := fun p => decide (vec15Equiv v p ≠ 0)

@[simp] theorem supportMask_apply (v : PrimeCarrier15) (p : SSP) :
    supportMask v p = decide (vec15Equiv v p ≠ 0) := rfl

/-- The support mask is the record-level indicator vector, transported. -/
theorem supportMask_eq_map (v : PrimeCarrier15) :
    supportMask v =
      vec15Equiv (AgdaMirror.GodelLattice.map (fun n => decide (n ≠ 0)) v) := by
  rw [vec15Equiv_map]
  rfl

theorem countBool_decide (n : Nat) : countBool (decide (n ≠ 0)) = countNonZeroNat n := by
  cases n <;> simp [countBool, countNonZeroNat]

/-- The non-zero count is the lane count of the indicator vector. -/
theorem countMask15_map_eq_countNonZero15 (v : PrimeCarrier15) :
    countMask15 (AgdaMirror.GodelLattice.map (fun n => decide (n ≠ 0)) v) =
      countNonZero15 v := by
  simp only [countMask15, countNonZero15, AgdaMirror.GodelLattice.map, countBool_decide]

/-- The non-zero count is the cardinality of the support mask. -/
theorem countNonZero15_eq_card (v : PrimeCarrier15) :
    countNonZero15 v = (Finset.univ.filter (fun p : SSP => supportMask v p = true)).card := by
  rw [← countMask15_map_eq_countNonZero15, countMask15_eq_card, supportMask_eq_map]

/-- The support mask is the complement of the order layer's threshold mask at `0`. -/
theorem supportMask_eq_not_thresholdMask_zero (v : PrimeCarrier15) (p : SSP) :
    supportMask v p = ! thresholdMask 0 v p := by
  rw [selectMask15_fibre]
  simp only [supportMask_apply, Nat.le_zero_eq]
  cases h : vec15Equiv v p <;> simp

theorem countNonZeroNat_add_countBool (n : Nat) :
    countNonZeroNat n + countBool (natLeqBool n 0) = 1 := by
  cases n <;> simp [countNonZeroNat, countBool, natLeqBool]

/-- Support and rank partition the fifteen primes. -/
theorem countNonZero15_add_rank15_zero (v : PrimeCarrier15) :
    countNonZero15 v + rank15 0 v = 15 := by
  simp only [countNonZero15, rank15, AgdaMirror.Vec15Order.selectMask15, countMask15]
  have a2 := countNonZeroNat_add_countBool v.e2
  have a3 := countNonZeroNat_add_countBool v.e3
  have a5 := countNonZeroNat_add_countBool v.e5
  have a7 := countNonZeroNat_add_countBool v.e7
  have a11 := countNonZeroNat_add_countBool v.e11
  have a13 := countNonZeroNat_add_countBool v.e13
  have a17 := countNonZeroNat_add_countBool v.e17
  have a19 := countNonZeroNat_add_countBool v.e19
  have a23 := countNonZeroNat_add_countBool v.e23
  have a29 := countNonZeroNat_add_countBool v.e29
  have a31 := countNonZeroNat_add_countBool v.e31
  have a41 := countNonZeroNat_add_countBool v.e41
  have a47 := countNonZeroNat_add_countBool v.e47
  have a59 := countNonZeroNat_add_countBool v.e59
  have a71 := countNonZeroNat_add_countBool v.e71
  omega

/-! ## The inference layer is a mask detector -/

/-- The carrier built from a mask: lane `1` on the mask, `0` off it. -/
def maskCarrier (m : MaskSSP) : PrimeCarrier15 :=
  vec15Equiv.symm (fun p => if m p then 1 else 0)

@[simp] theorem vec15Equiv_maskCarrier_apply (m : MaskSSP) (p : SSP) :
    vec15Equiv (maskCarrier m) p = if m p then 1 else 0 :=
  congrFun (vec15Equiv.apply_symm_apply _) p

/-- A carrier is the indicator of its own support exactly when every lane is
`0` or `1`. -/
theorem eq_maskCarrier_iff (v : PrimeCarrier15) :
    v = maskCarrier (supportMask v) ↔ ∀ p, vec15Equiv v p ≤ 1 := by
  constructor
  · intro h p
    have hv : vec15Equiv v p = vec15Equiv (maskCarrier (supportMask v)) p := by rw [← h]
    rw [vec15Equiv_maskCarrier_apply] at hv
    simp only [supportMask_apply, decide_eq_true_eq, ne_eq] at hv
    split_ifs at hv <;> omega
  · intro h
    apply vec15Equiv.injective
    funext p
    have hp := h p
    rw [vec15Equiv_maskCarrier_apply]
    simp only [supportMask_apply, decide_eq_true_eq, ne_eq]
    split_ifs with hz <;> omega

/-- The total mass is bounded by the non-zero count exactly when every lane is
`0` or `1`. -/
theorem sum_le_count_iff (v : PrimeCarrier15) :
    sum15 v ≤ countNonZero15 v ↔ ∀ p, vec15Equiv v p ≤ 1 := by
  have hs := AgdaMirror.Vec15Descriptive.countNonZeroNat_le_self
  have h1 := AgdaMirror.Vec15Descriptive.countNonZeroNat_le_one
  constructor
  · intro hle p
    simp only [sum15, AgdaMirror.GodelLattice.sum, countNonZero15] at hle
    have s2 := hs v.e2; have s3 := hs v.e3; have s5 := hs v.e5; have s7 := hs v.e7
    have s11 := hs v.e11; have s13 := hs v.e13; have s17 := hs v.e17; have s19 := hs v.e19
    have s23 := hs v.e23; have s29 := hs v.e29; have s31 := hs v.e31; have s41 := hs v.e41
    have s47 := hs v.e47; have s59 := hs v.e59; have s71 := hs v.e71
    have o2 := h1 v.e2; have o3 := h1 v.e3; have o5 := h1 v.e5; have o7 := h1 v.e7
    have o11 := h1 v.e11; have o13 := h1 v.e13; have o17 := h1 v.e17; have o19 := h1 v.e19
    have o23 := h1 v.e23; have o29 := h1 v.e29; have o31 := h1 v.e31; have o41 := h1 v.e41
    have o47 := h1 v.e47; have o59 := h1 v.e59; have o71 := h1 v.e71
    cases p <;> simp only [vec15Equiv_apply, vec15At] <;> omega
  · intro h
    have key : ∀ n : Nat, n ≤ 1 → n ≤ countNonZeroNat n := by
      intro n hn
      interval_cases n <;> simp [countNonZeroNat]
    have k2 := key _ (h .p2); have k3 := key _ (h .p3); have k5 := key _ (h .p5)
    have k7 := key _ (h .p7); have k11 := key _ (h .p11); have k13 := key _ (h .p13)
    have k17 := key _ (h .p17); have k19 := key _ (h .p19); have k23 := key _ (h .p23)
    have k29 := key _ (h .p29); have k31 := key _ (h .p31); have k41 := key _ (h .p41)
    have k47 := key _ (h .p47); have k59 := key _ (h .p59); have k71 := key _ (h .p71)
    simp only [vec15Equiv_apply, vec15At] at *
    simp only [sum15, AgdaMirror.GodelLattice.sum, countNonZero15]
    omega

/-- **The baseline test is a mask detector.**  It fails to reject exactly when the
carrier is the indicator of its own support, i.e. a Boolean mask over the base. -/
theorem baselineDecision_failToReject_iff (v : PrimeCarrier15) :
    baselineDecision v = Decision.failToReject ↔ v = maskCarrier (supportMask v) := by
  rw [eq_maskCarrier_iff, ← sum_le_count_iff]
  unfold baselineDecision
  by_cases h : leqNat (sum15 v) (countNonZero15 v) = true
  · rw [if_pos h]
    simpa using (leqNat_iff _ _).mp h
  · rw [if_neg (by simpa using h)]
    simp only [reduceCtorEq, false_iff]
    intro hle
    exact h ((leqNat_iff _ _).mpr hle)

/-- Consequently the baseline test rejects exactly when some lane exceeds `1`. -/
theorem baselineDecision_reject_iff (v : PrimeCarrier15) :
    baselineDecision v = Decision.reject ↔ ∃ p, 1 < vec15Equiv v p := by
  have h := baselineDecision_failToReject_iff v
  rw [eq_maskCarrier_iff] at h
  constructor
  · intro hr
    by_contra hc
    push_neg at hc
    have hft : baselineDecision v = Decision.failToReject := h.mpr fun p => by
      have := hc p; omega
    rw [hr] at hft
    exact absurd hft (by simp)
  · rintro ⟨p, hp⟩
    cases hd : baselineDecision v with
    | reject => rfl
    | failToReject =>
        have := h.mp hd p
        omega

/-- **The paired test is a mask detector on both arguments.** -/
theorem pairDecision_failToReject_iff (xs ys : PrimeCarrier15) :
    pairDecision xs ys = Decision.failToReject ↔
      xs = maskCarrier (supportMask xs) ∧ ys = maskCarrier (supportMask ys) := by
  have hx : countNonZero15 xs ≤ sum15 xs :=
    AgdaMirror.Vec15Descriptive.countNonZero15_le_sum15 xs
  have hy : countNonZero15 ys ≤ sum15 ys :=
    AgdaMirror.Vec15Descriptive.countNonZero15_le_sum15 ys
  have hsplit : pairStatistic xs ys ≤ pairPValue xs ys ↔
      (sum15 xs ≤ countNonZero15 xs ∧ sum15 ys ≤ countNonZero15 ys) := by
    unfold pairStatistic pairPValue
    constructor
    · intro h; omega
    · intro h; omega
  rw [eq_maskCarrier_iff, eq_maskCarrier_iff, ← sum_le_count_iff, ← sum_le_count_iff, ← hsplit]
  unfold pairDecision
  by_cases h : leqNat (pairStatistic xs ys) (pairPValue xs ys) = true
  · rw [if_pos h]
    simpa using (leqNat_iff _ _).mp h
  · rw [if_neg (by simpa using h)]
    simp only [reduceCtorEq, false_iff]
    intro hle
    exact h ((leqNat_iff _ _).mpr hle)

/-! ## The support mask in the mask arithmetic and geometry -/

/-- The support mask is monotone in the carrier. -/
theorem supportMask_mono {v w : PrimeCarrier15}
    (h : ∀ p, vec15Equiv v p ≤ vec15Equiv w p) (p : SSP) :
    supportMask v p = true → supportMask w p = true := by
  simp only [supportMask_apply, decide_eq_true_eq, ne_eq]
  have := h p
  omega

/-- Hence the support products form a divisibility chain (`maskProduct_dvd_iff`). -/
theorem supportMask_dvd {v w : PrimeCarrier15} (h : ∀ p, vec15Equiv v p ≤ vec15Equiv w p) :
    maskProduct (supportMask v) ∣ maskProduct (supportMask w) :=
  (maskProduct_dvd_iff _ _).mpr (supportMask_mono h)

/-- And growing a carrier never moves its support mask closer to the collapse
mask in the supplied ultrametric. -/
theorem supportMask_dSSP_empty_mono {v w : PrimeCarrier15}
    (h : ∀ p, vec15Equiv v p ≤ vec15Equiv w p) :
    dSSP (supportMask v) emptyMaskSSP ≤ dSSP (supportMask w) emptyMaskSSP :=
  dSSP_empty_mono (supportMask_mono h)

/-! ## The robust layer's fences are Monster masks -/

theorem outsideFence_lane (lo hi n : Nat) :
    notBool (andBool (leqNatBool lo n) (leqNatBool n hi)) = decide ¬ (lo ≤ n ∧ n ≤ hi) := by
  by_cases h1 : lo ≤ n <;> by_cases h2 : n ≤ hi <;>
    simp [notBool, andBool, leqNatBool, h1, h2]

/-- The fence mask, read over the prime base: it keeps exactly the lanes that
fall outside `[lo, hi]`. -/
theorem outsideFenceMask15_fibre (lo hi : Nat) (v : PrimeCarrier15) :
    vec15Equiv (outsideFenceMask15 lo hi v) =
      fun p => decide ¬ (lo ≤ vec15Equiv v p ∧ vec15Equiv v p ≤ hi) := by
  funext p
  cases p <;> exact outsideFence_lane lo hi _

theorem clampNat_eq_self {lo hi n : Nat} (h1 : lo ≤ n) (h2 : n ≤ hi) : clampNat lo hi n = n := by
  simp [clampNat, h1, h2]

/-- Winsorisation is the identity off the Tukey outlier mask: a lane inside the
fence is untouched. -/
theorem winsorize15_eq_off_outlierMask (v : PrimeCarrier15) (p : SSP)
    (h : vec15Equiv (tukeyOutlierMask15 v) p = false) :
    vec15Equiv (winsorize15 v) p = vec15Equiv v p := by
  rw [tukeyOutlierMask15, outsideFenceMask15_fibre] at h
  simp only [decide_eq_false_iff_not, Decidable.not_not] at h
  simp only [winsorize15, AgdaMirror.Vec15Order.map15, vec15Equiv_map]
  exact clampNat_eq_self h.1 h.2

/-- The Tukey outlier mask of a carrier, as a point of the Monster mask fibre. -/
def tukeyMask (v : PrimeCarrier15) : MaskSSP := vec15Equiv (tukeyOutlierMask15 v)

/-- Winsorisation only changes lanes selected by the Tukey mask. -/
theorem winsorize15_agrees_off_tukeyMask (v : PrimeCarrier15) (p : SSP)
    (h : tukeyMask v p = false) : vec15Equiv (winsorize15 v) p = vec15Equiv v p :=
  winsorize15_eq_off_outlierMask v p h

end Synthesis.InferenceFibre
