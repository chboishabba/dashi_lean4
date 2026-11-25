import Integration.Paper9Hecke41ChartGeometry
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative

/-! SOURCE-WRITTEN, UNCOMPILED.
Exact finite coefficient reflection on the normalized cusp unit J.
No bivariate polynomial table or floating recognition. Connecting the
actual analytic jUnit Taylor coefficients and actual Hecke product
to these formal series is still a separate proof obligation. -/
namespace Integration.Paper9LaurentTriangularReflection

open PowerSeries
open scoped BigOperators

-- Reverse degree order is the actual descending extraction order.
-- Column k corresponds to j^(d-k), after multiplying by q^d.
def column (J : PowerSeries ℂ) (d k : ℕ) : PowerSeries ℂ :=
  PowerSeries.X^k*J^(d-k)

theorem columnAbove (J : PowerSeries ℂ) (d k n : ℕ) (h : n<k) :
    PowerSeries.coeff n (column J d k)=0 := by
  simp [column,PowerSeries.coeff_X_pow_mul',not_le.mpr h]

theorem columnDiagonal (J : PowerSeries ℂ) (hJ : PowerSeries.constantCoeff J=1)
    (d k : ℕ) : PowerSeries.coeff k (column J d k)=1 := by
  simp [column,PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_zero_eq_constantCoeff_apply,hJ]

def coefficient (J : PowerSeries ℂ) (d n k : ℕ) : ℂ :=
  PowerSeries.coeff n (column J d k)

def normalized (J : PowerSeries ℂ) (d : ℕ) (c : ℕ → ℂ) :
    PowerSeries ℂ :=
  ∑ k ∈ Finset.range (d+1), PowerSeries.C (c k)*column J d k

theorem normalizedCoeff (J : PowerSeries ℂ) (d n : ℕ) (c : ℕ → ℂ)
    (hn : n≤d) :
    PowerSeries.coeff n (normalized J d c) =
      ∑ k ∈ Finset.range (n+1), c k*coefficient J d n k := by
  unfold normalized coefficient
  simp only [map_sum,PowerSeries.coeff_C_mul]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k hk hkn
  have h : n<k := by
    simp only [Finset.mem_range] at hk hkn
    omega
  rw [columnAbove J d k n h,mul_zero]

-- All-index finite triangular elimination, not an invertible matrix
-- assumption. This is the exact uniqueness used by the forward replay.
theorem triangularUnique (J : PowerSeries ℂ)
    (hJ : PowerSeries.constantCoeff J=1) (d : ℕ) (c e : ℕ → ℂ)
    (h : ∀ n ≤ d, PowerSeries.coeff n (normalized J d c) =
      PowerSeries.coeff n (normalized J d e)) :
    ∀ n ≤ d, c n=e n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have he := h n hn
    rw [normalizedCoeff J d n c hn,normalizedCoeff J d n e hn,
      Finset.sum_range_succ,Finset.sum_range_succ] at he
    have hp : (∑ k ∈ Finset.range n, c k*coefficient J d n k) =
        ∑ k ∈ Finset.range n, e k*coefficient J d n k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [ih k (Finset.mem_range.mp hk) (by omega)]
    have hdiag : coefficient J d n n=1 := columnDiagonal J hJ d n
    rw [hp,hdiag,mul_one,mul_one] at he
    exact add_left_cancel he

-- Original log-derivative recurrence. H*L=q H' is an exact formal
-- identity, and no division by an unknown coefficient is used.
theorem eulerCoeff (H : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n
      (PowerSeries.X*PowerSeries.derivative ℂ H)=
      (n : ℂ)*PowerSeries.coeff n H := by
  cases n with
  | zero => simp
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_derivative]
    push_cast
    ring

theorem logRecurrence (H L : PowerSeries ℂ)
    (h : H*L=PowerSeries.X*PowerSeries.derivative ℂ H) (n : ℕ) :
    (∑ ij ∈ Finset.antidiagonal n,
      PowerSeries.coeff ij.1 H*PowerSeries.coeff ij.2 L) =
      (n : ℂ)*PowerSeries.coeff n H := by
  rw [← PowerSeries.coeff_mul,h,eulerCoeff]

-- N is the true cyclotomic norm after descent, V the p-filtered
-- log derivative. The finite producer divides by n only at n>0.
theorem normRecurrence (N V : PowerSeries ℂ)
    (h : V*N=PowerSeries.X*PowerSeries.derivative ℂ N) (n : ℕ) :
    (∑ ij ∈ Finset.antidiagonal n,
      PowerSeries.coeff ij.1 V*PowerSeries.coeff ij.2 N) =
      (n : ℂ)*PowerSeries.coeff n N :=
  logRecurrence V N h n

-- Exact degree frontiers for the original p=41 coefficient producers.
theorem diagonalFrontier : 41*82=3362 ∧ 41*82-41+1=3322 := by decide
theorem sliceFrontier : 41*42=1722 := by decide

end Integration.Paper9LaurentTriangularReflection
