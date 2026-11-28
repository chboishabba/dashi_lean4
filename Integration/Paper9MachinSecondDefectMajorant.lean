import Mathlib

/-!
Original Machin finite second-quotient radius budget.

Every finite original signed atan quotient defect has coefficient
(-1)^k/(2k+1) times its source power second quotient. On
|x|,|y| ≤ 1/2 the latter has (2k+1)*k monomials counted with
multiplicity and degree 2k-1. The resulting radius bound is

  Σ_{k<N} 2*k/4^k = 8/9*(1-(3*N+1)/4^N) ≤ 8/9.

This file proves the EXACT all-N rational budget, not the
cross-carrier Bishop triangle/embedding theorem. Source-written,
kernel execution pending. No axioms or numerical approximations.
-/

namespace Integration.Paper9MachinSecondDefectMajorant

open Finset

def radiusTerm (k : ℕ) : ℚ :=
  2 * (k : ℚ) / (4 : ℚ) ^ k

def radiusBudget (N : ℕ) : ℚ :=
  ∑ k ∈ Finset.range N, radiusTerm k

def closedBudget (N : ℕ) : ℚ :=
  (8/9 : ℚ) * (1 - (3*(N : ℚ)+1)/(4:ℚ)^N)

theorem closedBudget_zero : closedBudget 0 = 0 := by
  norm_num [closedBudget]

theorem closedBudget_step (N : ℕ) :
    closedBudget (N+1) = closedBudget N + radiusTerm N := by
  have hn : (4:ℚ)^N ≠ 0 := pow_ne_zero _ (by norm_num)
  unfold closedBudget radiusTerm
  push_cast
  rw [pow_succ]
  field_simp
  ring

theorem radiusBudget_eq_closedBudget (N : ℕ) :
    radiusBudget N = closedBudget N := by
  induction N with
  | zero => simp [radiusBudget, closedBudget_zero]
  | succ n ih =>
    rw [radiusBudget, Finset.sum_range_succ]
    change radiusBudget n + radiusTerm n = closedBudget (n+1)
    rw [ih, closedBudget_step]

theorem closedBudget_le_eightNinths (N : ℕ) :
    closedBudget N ≤ (8/9 : ℚ) := by
  have hn : (0:ℚ) < (4:ℚ)^N := pow_pos (by norm_num) _
  have hq : (0:ℚ) ≤ (3*(N:ℚ)+1)/(4:ℚ)^N :=
    div_nonneg (by positivity) hn.le
  unfold closedBudget
  nlinarith

theorem radiusBudget_le_eightNinths (N : ℕ) :
    radiusBudget N ≤ (8/9 : ℚ) := by
  rw [radiusBudget_eq_closedBudget]
  exact closedBudget_le_eightNinths N

theorem radiusTerm_nonneg (k : ℕ) : 0 ≤ radiusTerm k := by
  unfold radiusTerm
  positivity

theorem radiusBudget_nonneg (N : ℕ) : 0 ≤ radiusBudget N := by
  unfold radiusBudget
  exact Finset.sum_nonneg (fun k hk => radiusTerm_nonneg k)

theorem radiusBudget_monotone (N : ℕ) :
    radiusBudget N ≤ radiusBudget (N+1) := by
  rw [radiusBudget, Finset.sum_range_succ]
  change radiusBudget N ≤ radiusBudget N + radiusTerm N
  linarith [radiusTerm_nonneg N]

-- Full coefficient combinatorics behind the majorant:
-- for m>=2, T_m(x,y)=sum_{j=0}^{m-2}(j+1)x^j*y^(m-2-j).
-- This is exactly the existing original power-second quotient
-- expressed in x and y=x+h. No speculative mean-value theorem.
def secondMonomial (m j : ℕ) (x y : ℚ) : ℚ :=
  (j+1 : ℕ) * x^j * y^(m-2-j)

def secondPolynomial (m : ℕ) (x y : ℚ) : ℚ :=
  ∑ j ∈ Finset.range (m-1), secondMonomial m j x y

theorem coefficientCount (n : ℕ) :
    ∑ j ∈ Finset.range n, (j+1 : ℕ) = n*(n+1)/2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    omega

end Integration.Paper9MachinSecondDefectMajorant
