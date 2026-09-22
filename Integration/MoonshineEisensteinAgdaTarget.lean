import Integration.MoonshineEisensteinAnalytic

/-!
# Canonical Lean target for the actual Agda finite Eisenstein recurrences

This module mirrors the definitions in
DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact
without changing their indexing, signs, or coefficient scales.

The purpose is not to create a second analytic definition of E4/E6. It gives
the Agda extraction compiler one canonical Lean target:

  q(tau)    = exp(2*pi*i*tau)
  E4_0      = 1
  E4_(n+1)  = E4_n + (240 * sigma_3(n+1)) q^(n+1)
  E6_0      = 1
  E6_(n+1)  = E6_n - (504 * sigma_5(n+1)) q^(n+1)

The converged Mathlib modular forms remain in
Integration.MoonshineEisensteinAnalytic.
-/

namespace Integration.MoonshineEisensteinAgdaTarget

open Complex Real
open UpperHalfPlane hiding I
open ArithmeticFunction
open scoped Real Nat ArithmeticFunction.sigma BigOperators

noncomputable section

/-- Literal target for Agda qOf. Multiplication is parenthesized to match the
Agda source before ring normalization. -/
def qOfTarget (τ : ℍ) : ℂ :=
  Complex.exp (((2 : ℂ) * (I * π)) * (τ : ℂ))

/-- The literal target q is the Mathlib analytic q parameter. -/
theorem qOfTarget_eq_qParam (τ : ℍ) :
    qOfTarget τ = Integration.MoonshineEisensteinAnalytic.qParam τ := by
  unfold qOfTarget Integration.MoonshineEisensteinAnalytic.qParam
  congr 1
  ring

/-- Lean target of the Agda repeated-addition natural scaling. -/
def scaleNatTarget (n : ℕ) (z : ℂ) : ℂ :=
  (n : ℂ) * z

@[simp]
theorem scaleNatTarget_zero (z : ℂ) :
    scaleNatTarget 0 z = 0 := by
  simp [scaleNatTarget]

@[simp]
theorem scaleNatTarget_succ (n : ℕ) (z : ℂ) :
    scaleNatTarget (n + 1) z = z + scaleNatTarget n z := by
  simp [scaleNatTarget]
  ring

/-- Canonical Lean target of Agda e4Truncated, parameterized by q so that the
recurrence itself is independent of the upper-half-plane packaging. -/
def e4TruncatedTarget : ℕ → ℂ → ℂ
  | 0, _ => 1
  | n + 1, q =>
      e4TruncatedTarget n q +
        scaleNatTarget (240 * σ 3 (n + 1)) (q ^ (n + 1))

/-- Canonical Lean target of Agda e6Truncated. -/
def e6TruncatedTarget : ℕ → ℂ → ℂ
  | 0, _ => 1
  | n + 1, q =>
      e6TruncatedTarget n q -
        scaleNatTarget (504 * σ 5 (n + 1)) (q ^ (n + 1))

@[simp]
theorem e4TruncatedTarget_zero (q : ℂ) :
    e4TruncatedTarget 0 q = 1 := rfl

@[simp]
theorem e4TruncatedTarget_succ (n : ℕ) (q : ℂ) :
    e4TruncatedTarget (n + 1) q =
      e4TruncatedTarget n q +
        scaleNatTarget (240 * σ 3 (n + 1)) (q ^ (n + 1)) := rfl

@[simp]
theorem e6TruncatedTarget_zero (q : ℂ) :
    e6TruncatedTarget 0 q = 1 := rfl

@[simp]
theorem e6TruncatedTarget_succ (n : ℕ) (q : ℂ) :
    e6TruncatedTarget (n + 1) q =
      e6TruncatedTarget n q -
        scaleNatTarget (504 * σ 5 (n + 1)) (q ^ (n + 1)) := rfl

/-- Closed finite-sum form of the literal Agda E4 recurrence. -/
theorem e4TruncatedTarget_eq_sum (N : ℕ) (q : ℂ) :
    e4TruncatedTarget N q =
      1 + ∑ n ∈ Finset.range N,
        scaleNatTarget (240 * σ 3 (n + 1)) (q ^ (n + 1)) := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [e4TruncatedTarget_succ, ih]
      simp only [Finset.sum_range_succ]
      ring

/-- Closed finite-sum form of the literal Agda E6 recurrence. -/
theorem e6TruncatedTarget_eq_sum (N : ℕ) (q : ℂ) :
    e6TruncatedTarget N q =
      1 - ∑ n ∈ Finset.range N,
        scaleNatTarget (504 * σ 5 (n + 1)) (q ^ (n + 1)) := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [e6TruncatedTarget_succ, ih]
      simp only [Finset.sum_range_succ]
      ring

/-- The exact target recurrence evaluated at the canonical q parameter. -/
def e4At (N : ℕ) (τ : ℍ) : ℂ :=
  e4TruncatedTarget N (qOfTarget τ)

/-- The exact target recurrence evaluated at the canonical q parameter. -/
def e6At (N : ℕ) (τ : ℍ) : ℂ :=
  e6TruncatedTarget N (qOfTarget τ)

/-- Literal shifted E4 term used by the Agda recurrence. -/
def e4Term (τ : ℍ) (n : ℕ) : ℂ :=
  scaleNatTarget (240 * σ 3 (n + 1)) (qOfTarget τ ^ (n + 1))

/-- Literal shifted E6 term used by the Agda recurrence. -/
def e6Term (τ : ℍ) (n : ℕ) : ℂ :=
  scaleNatTarget (504 * σ 5 (n + 1)) (qOfTarget τ ^ (n + 1))

/-- The exact shifted E4 term family is summable. -/
theorem summable_e4Term (τ : ℍ) :
    Summable (e4Term τ) := by
  have hs :=
    (summable_nat_add_iff 1).mpr
      (Integration.MoonshineEisensteinAnalytic.summable_240_sigma3_q τ)
  simpa [e4Term, scaleNatTarget,
    qOfTarget_eq_qParam, Nat.cast_mul, mul_assoc] using hs

/-- The exact shifted E6 term family is summable. -/
theorem summable_e6Term (τ : ℍ) :
    Summable (e6Term τ) := by
  have hs :=
    (summable_nat_add_iff 1).mpr
      (Integration.MoonshineEisensteinAnalytic.summable_504_sigma5_q τ)
  simpa [e6Term, scaleNatTarget,
    qOfTarget_eq_qParam, Nat.cast_mul, mul_assoc] using hs

/-- The literal Agda E4 truncations converge to their canonical infinite sum. -/
theorem e4At_tendsto (τ : ℍ) :
    Tendsto (fun N => e4At N τ) atTop
      (𝓝 (1 + ∑' n : ℕ, e4Term τ n)) := by
  have hs := summable_e4Term τ
  have ht := hs.hasSum.tendsto_sum_nat
  simpa [e4At, e4TruncatedTarget_eq_sum, e4Term] using
    tendsto_const_nhds.add ht

/-- The literal Agda E6 truncations converge to their canonical infinite sum. -/
theorem e6At_tendsto (τ : ℍ) :
    Tendsto (fun N => e6At N τ) atTop
      (𝓝 (1 - ∑' n : ℕ, e6Term τ n)) := by
  have hs := summable_e6Term τ
  have ht := hs.hasSum.tendsto_sum_nat
  simpa [e6At, e6TruncatedTarget_eq_sum, e6Term] using
    tendsto_const_nhds.sub ht

/-- Canonical infinite targets selected by the actual Agda recurrences. -/
def e4Limit (τ : ℍ) : ℂ :=
  1 + ∑' n : ℕ, e4Term τ n

def e6Limit (τ : ℍ) : ℂ :=
  1 - ∑' n : ℕ, e6Term τ n

theorem e4At_tendsto_limit (τ : ℍ) :
    Tendsto (fun N => e4At N τ) atTop (𝓝 (e4Limit τ)) := by
  simpa [e4Limit] using e4At_tendsto τ

theorem e6At_tendsto_limit (τ : ℍ) :
    Tendsto (fun N => e6At N τ) atTop (𝓝 (e6Limit τ)) := by
  simpa [e6Limit] using e6At_tendsto τ

/-- The canonical infinite target of the literal Agda E4 recurrence is
exactly Mathlib's normalized weight-four Eisenstein series. -/
theorem e4Limit_eq_mathlib_E4 (τ : ℍ) :
    e4Limit τ = Integration.MoonshineEisensteinAnalytic.E4 τ := by
  rw [Integration.MoonshineEisensteinAnalytic.E4_qExpansion,
    tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ =>
        (σ 3 n : ℂ) *
          Integration.MoonshineEisensteinAnalytic.qParam τ ^ n)]
  simp_rw [← qOfTarget_eq_qParam τ]
  unfold e4Limit e4Term scaleNatTarget
  norm_num [show bernoulli 4 = -1 / 30 by decide +kernel]
  ring

/-- The canonical infinite target of the literal Agda E6 recurrence is
exactly Mathlib's normalized weight-six Eisenstein series. -/
theorem e6Limit_eq_mathlib_E6 (τ : ℍ) :
    e6Limit τ = Integration.MoonshineEisensteinAnalytic.E6 τ := by
  rw [Integration.MoonshineEisensteinAnalytic.E6_qExpansion,
    tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ =>
        (σ 5 n : ℂ) *
          Integration.MoonshineEisensteinAnalytic.qParam τ ^ n)]
  simp_rw [← qOfTarget_eq_qParam τ]
  unfold e6Limit e6Term scaleNatTarget
  norm_num [show bernoulli 6 = 1 / 42 by decide +kernel]
  ring

/-- Therefore the exact Agda-shaped finite E4 recurrence converges to Mathlib E4. -/
theorem e4At_tendsto_mathlib_E4 (τ : ℍ) :
    Tendsto (fun N => e4At N τ) atTop
      (𝓝 (Integration.MoonshineEisensteinAnalytic.E4 τ)) := by
  simpa [e4Limit_eq_mathlib_E4 τ] using e4At_tendsto_limit τ

/-- Therefore the exact Agda-shaped finite E6 recurrence converges to Mathlib E6. -/
theorem e6At_tendsto_mathlib_E6 (τ : ℍ) :
    Tendsto (fun N => e6At N τ) atTop
      (𝓝 (Integration.MoonshineEisensteinAnalytic.E6 τ)) := by
  simpa [e6Limit_eq_mathlib_E6 τ] using e6At_tendsto_limit τ

/-- Machine-readable seam. -/
structure AgdaTargetBoundary where
  literalQTargetOwned : Bool
  literalE4RecurrenceOwned : Bool
  literalE6RecurrenceOwned : Bool
  finiteSumNormalFormsOwned : Bool
  qTargetIdentifiedWithMathlibQ : Bool
  agdaPrimitiveExtractionInhabited : Bool
  finiteRecurrenceBoundToExtractedAgdaObject : Bool
  finiteToInfiniteLimitTransportPaid : Bool
  infiniteLimitIdentifiedWithMathlibE4E6 : Bool

def agdaTargetBoundary : AgdaTargetBoundary where
  literalQTargetOwned := true
  literalE4RecurrenceOwned := true
  literalE6RecurrenceOwned := true
  finiteSumNormalFormsOwned := true
  qTargetIdentifiedWithMathlibQ := true
  agdaPrimitiveExtractionInhabited := false
  finiteRecurrenceBoundToExtractedAgdaObject := false
  finiteToInfiniteLimitTransportPaid := true
  infiniteLimitIdentifiedWithMathlibE4E6 := true

end

end Integration.MoonshineEisensteinAgdaTarget
