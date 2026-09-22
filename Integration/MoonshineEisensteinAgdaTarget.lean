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
  finiteToInfiniteLimitTransportPaid := false
  infiniteLimitIdentifiedWithMathlibE4E6 := false

end

end Integration.MoonshineEisensteinAgdaTarget
