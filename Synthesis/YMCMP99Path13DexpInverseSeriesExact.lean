import Synthesis.YMCMP99Path13NonflatRowBudgetExact
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed

/-! Original Path13 D/J small-ball differential kernel.
For a left-trivialized exponential derivative the analytic operator
is D(X)=sum_{n>=0} (±ad_X)^n/(n+1)! (sign selected by the source).
We prove the quantitative series and its actual two-sided inverse
enclosure in a complete submultiplicative real normed algebra.
No assumption that an arbitrary operator called D is the derivative.
Identifying the actual SU(2) source derivative and principal-log chart
with this series, and the nonflat selected row with H(s(Y0)), remains
a separate geometric attachment.
-/
namespace CMP99Pivot.Path13
open DASHI.YM.SelectedInverseEnclosure
open scoped BigOperators
noncomputable section
variable {R : Type*} [NormedRing R] [NormOneClass R] [NormedAlgebra ℝ R]
  [CompleteSpace R] [HasSummableGeomSeries R]

def dexpTail (A : R) (n : ℕ) : R :=
  (1/((n+2).factorial:ℝ)) • A^(n+1)

def dexpSeries (A : R) : R := 1+∑' n : ℕ,dexpTail A n

theorem factorial_ge_two_pow (n : ℕ) : 2^(n+1)≤(n+2).factorial := by
  induction n with
  | zero => decide
  | succ n ih =>
    change 2^(n+1+1)≤(n+1+2).factorial
    rw [show n+1+2=n+2+1 by omega,Nat.factorial_succ,pow_succ]
    calc
      2^(n+1)*2 = 2*2^(n+1) := Nat.mul_comm _ _
      _ ≤ (n+2+1)*(n+2).factorial := Nat.mul_le_mul (by omega) ih

theorem dexpTail_bound (A : R) (n : ℕ) :
    ‖dexpTail A n‖≤(‖A‖/2)^(n+1) := by
  unfold dexpTail
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hf : (2:ℝ)^(n+1)≤((n+2).factorial:ℝ) := by
    exact_mod_cast factorial_ge_two_pow n
  have hp := norm_pow_le A (n+1)
  calc
    _ ≤ (1/((n+2).factorial:ℝ))*‖A‖^(n+1) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ (1/(2:ℝ)^(n+1))*‖A‖^(n+1) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact one_div_le_one_div_of_le (by positivity) hf
    _ = _ := by rw [div_pow]; ring

theorem dexpTail_summable (A : R) (hA : ‖A‖≤1) :
    Summable (dexpTail A) := by
  have hr : ‖‖A‖/2‖<1 := by rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]; linarith
  have hg : Summable (fun n : ℕ=>(‖A‖/2)^n) := summable_geometric_of_norm_lt_one hr
  have hs : Summable (fun n : ℕ=>(‖A‖/2)^(n+1)) := by
    simpa [pow_succ,mul_comm] using hg.mul_left (‖A‖/2)
  exact hs.of_norm_bounded (dexpTail_bound A)

theorem dexpSeries_small (A : R) (hA : ‖A‖≤1) :
    ‖dexpSeries A-1‖≤‖A‖ := by
  let r := ‖A‖/2
  have hr0 : 0≤r := by dsimp [r]; positivity
  have hr : r<1 := by dsimp [r]; linarith
  have hs : HasSum (fun n : ℕ=>r^n) (1-r)⁻¹ := hasSum_geometric_of_lt_one hr0 hr
  have hs' : HasSum (fun n : ℕ=>r^(n+1)) (r*(1-r)⁻¹) := by
    simpa [pow_succ,mul_comm] using hs.mul_left r
  have h := tsum_of_norm_bounded hs' (dexpTail_bound A)
  have he : dexpSeries A-1=∑' n : ℕ,dexpTail A n := by unfold dexpSeries; abel
  rw [he]
  apply h.trans
  change r*(1-r)⁻¹≤‖A‖
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (sub_pos.mpr hr)).mpr
  dsimp [r]
  nlinarith [mul_nonneg (norm_nonneg A) (sub_nonneg.mpr hA)]

/-- The literal D/J norm slots from sourceRow_nonflat_bound follow
for this exponential kernel at the original 148e commutator radius.
The inverse is two-sided; there is no separately assumed J. -/
theorem dexpSeries_logInverse_enclosure (A : R) (e : ℝ)
    (he : 0≤e) (hA : ‖A‖≤148*e) (hr : 148*e≤1/2) :
    ∃ J : R,dexpSeries A*J=1 ∧ J*dexpSeries A=1 ∧
      ‖dexpSeries A-1‖≤148*e ∧ ‖J‖≤2 ∧ ‖J-1‖≤296*e := by
  have hsmall := dexpSeries_small A (by linarith)
  have hD : ‖dexpSeries A-1‖≤148*e := hsmall.trans hA
  obtain ⟨J,h1,h2,h3,h4⟩ := selected_inverse_ball (1:Rˣ) (dexpSeries A) 1
    (by norm_num) (by simp) (by simpa using hD.trans hr)
  refine ⟨J,h1,h2,hD,by simpa using h3,?_⟩
  have hh : ‖J-1‖≤2*‖dexpSeries A-1‖ := by simpa using h4
  linarith

end
end CMP99Pivot.Path13
