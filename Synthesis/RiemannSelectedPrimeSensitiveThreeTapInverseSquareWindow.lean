import Synthesis.RiemannSelectedPrimeSensitiveThreeTapInverseSquareTail
import Synthesis.RiemannZetaMuExactAbelAC

/-!
# Literal zero-window inverse-square bounds

This is the carrier-to-shell bridge for the inverse-square max-cut.

For any literal half-open zero window `(A,B]` separated by distance `d>0` from
the sample height `t`, every summand satisfies

  m_rho / (gamma_rho-t)^2 <= m_rho / d^2.

Summing on the exact finite `Zeta23` window turns the multiplicity sum back into
`Ncount A B`.  The arbitrary-endpoint RvM count theorem then gives an explicit
positive-height shell estimate.  The unconditional local zero-count theorem is
also consumed directly on all real unit windows, so negative ordinates remain
on the same literal carrier and require no conjugation/reflection rewrite.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set
open scoped Real BigOperators
open Zeta23

/-- Inverse-square mass on the literal half-open zeta window `(A,B]`. -/
def zetaWindowInverseSquareMass (t A B : ℝ) : ℝ :=
  ∑ rho ∈ (zetaZeroConfig.finite_window A B).toFinset,
    (zetaZeroConfig.mult rho : ℝ) / (rho.im - t)^2

theorem zetaWindowInverseSquareMass_nonneg
    (t A B : ℝ) :
    0 <= zetaWindowInverseSquareMass t A B := by
  unfold zetaWindowInverseSquareMass
  positivity

/-- A separated literal zero window is bounded by its exact multiplicity count
multiplied by the inverse-square separation cost. -/
theorem zetaWindowInverseSquareMass_le_count_div_sq
    {t A B d : ℝ}
    (hd : 0 < d)
    (hsep : ∀ rho ∈ zetaZeroConfig.window A B,
      d <= |rho.im - t|) :
    zetaWindowInverseSquareMass t A B
      <= (Ncount A B : ℝ) / d^2 := by
  classical
  let hfin : (zetaZeroConfig.window A B).Finite :=
    zetaZeroConfig.finite_window A B
  let F : Finset ℂ := hfin.toFinset
  have hN :
      (Ncount A B : ℝ)
        = ∑ rho ∈ F, (zetaZeroConfig.mult rho : ℝ) := by
    rw [← zetaZeroConfig_N]
    unfold ZeroConfig.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    push_cast
    rfl
  have hterm :
      ∀ rho ∈ F,
        (zetaZeroConfig.mult rho : ℝ) / (rho.im - t)^2
          <= (zetaZeroConfig.mult rho : ℝ) / d^2 := by
    intro rho hrho
    have hrhoSet : rho ∈ zetaZeroConfig.window A B := by
      simpa [F, hfin] using hrho
    have hdist := hsep rho hrhoSet
    have hprod :
        0 <= (|rho.im - t| - d) * (|rho.im - t| + d) :=
      mul_nonneg (sub_nonneg.mpr hdist)
        (add_nonneg (abs_nonneg _) hd.le)
    have hden : d^2 <= (rho.im - t)^2 := by
      rw [← sq_abs (rho.im - t)]
      nlinarith
    have hd2 : 0 < d^2 := by positivity
    have hx2 : 0 < (rho.im - t)^2 := lt_of_lt_of_le hd2 hden
    apply (div_le_div_iff₀ hx2 hd2).2
    exact mul_le_mul_of_nonneg_left hden (by positivity)
  unfold zetaWindowInverseSquareMass
  change (∑ rho ∈ F,
    (zetaZeroConfig.mult rho : ℝ) / (rho.im - t)^2) <= _
  calc
    (∑ rho ∈ F,
      (zetaZeroConfig.mult rho : ℝ) / (rho.im - t)^2)
      <= ∑ rho ∈ F, (zetaZeroConfig.mult rho : ℝ) / d^2 := by
        exact Finset.sum_le_sum hterm
    _ = (∑ rho ∈ F, (zetaZeroConfig.mult rho : ℝ)) / d^2 := by
        rw [Finset.sum_div]
    _ = (Ncount A B : ℝ) / d^2 := by rw [hN]

/-- RvM count + separation gives an explicit inverse-square window bound for
arbitrary positive endpoints. -/
theorem exists_zetaWindowInverseSquareMass_rvm_bound :
    ∃ C : ℝ, 0 <= C ∧
      ∀ {t A B d : ℝ},
        5 <= A ->
        A < B ->
        0 < d ->
        (∀ rho ∈ zetaZeroConfig.window A B,
          d <= |rho.im - t|) ->
        zetaWindowInverseSquareMass t A B
          <=
        C * ((B-A)+1) * Real.log (B+4) / d^2 := by
  obtain ⟨C, hC0, hcount⟩ := exists_zetaZeroCount_arbitrary_bound_at_five
  refine ⟨C, hC0, ?_⟩
  intro t A B d hA hAB hd hsep
  have hbase := zetaWindowInverseSquareMass_le_count_div_sq hd hsep
  have hN := hcount A B hA hAB
  have hd2 : 0 < d^2 := by positivity
  exact hbase.trans (div_le_div_of_nonneg_right hN hd2.le)

/-- The right dyadic shell `(t+R,t+2R]` has the expected count-over-R^2
bound.  Iterating this shell is the remaining summation step. -/
theorem exists_zetaWindowInverseSquareMass_right_shell_rvm_bound :
    ∃ C : ℝ, 0 <= C ∧
      ∀ {t R : ℝ},
        200 <= t ->
        0 < R ->
        zetaWindowInverseSquareMass t (t+R) (t+2*R)
          <=
        C * (R+1) * Real.log (t+2*R+4) / R^2 := by
  obtain ⟨C, hC0, hwin⟩ := exists_zetaWindowInverseSquareMass_rvm_bound
  refine ⟨C, hC0, ?_⟩
  intro t R ht hR
  have hA : 5 <= t+R := by linarith
  have hAB : t+R < t+2*R := by linarith
  have hsep :
      ∀ rho ∈ zetaZeroConfig.window (t+R) (t+2*R),
        R <= |rho.im-t| := by
    intro rho hrho
    have hpos : 0 < rho.im - t := by linarith [hrho.2.1]
    rw [abs_of_pos hpos]
    linarith [hrho.2.1]
  have h := hwin (t:=t) (A:=t+R) (B:=t+2*R) (d:=R)
    hA hAB hR hsep
  convert h using 1 <;> ring

/-- Boundary-safe first right shell.

The ordinary right dyadic chart is `(3t/2,2t]` at `R=t/2`, so the literal
complement boundary `gamma=3t/2` is not owned by that half-open window.  Rather
than introduce a separate boundary fibre, enlarge only the first source window
to `(3t/2-1,2t]`.  This contains the entire literal first far block
`[3t/2,2t]`, while every point of the enlarged window remains at distance at
least `t/2-1` from `t`.  For `t>=200` this costs only a harmless constant in the
same `O(log t/t)` shell scale. -/
theorem exists_zetaWindowInverseSquareMass_right_first_boundary_rvm_bound :
    ∃ C : ℝ, 0 <= C ∧
      ∀ {t : ℝ},
        200 <= t ->
        zetaWindowInverseSquareMass t (3*t/2-1) (2*t)
          <=
        C * (t/2 + 2) * Real.log (2*t+4) / (t/2-1)^2 := by
  obtain ⟨C, hC0, hwin⟩ := exists_zetaWindowInverseSquareMass_rvm_bound
  refine ⟨C, hC0, ?_⟩
  intro t ht
  have hA : 5 <= 3*t/2-1 := by linarith
  have hAB : 3*t/2-1 < 2*t := by linarith
  have hd : 0 < t/2-1 := by linarith
  have hsep :
      ∀ rho ∈ zetaZeroConfig.window (3*t/2-1) (2*t),
        t/2-1 <= |rho.im-t| := by
    intro rho hrho
    have hpos : 0 < rho.im-t := by linarith [hrho.2.1]
    rw [abs_of_pos hpos]
    linarith [hrho.2.1]
  have h := hwin (t:=t) (A:=3*t/2-1) (B:=2*t) (d:=t/2-1)
    hA hAB hd hsep
  convert h using 1 <;> ring

/-- The left shell `(t-2R,t-R]` obeys the same estimate as long as it remains in
the positive-height RvM range.  Once `t-2R < 5`, the proof switches to the
all-real local zero-count theorem below; no positivity assumption is hidden. -/
theorem exists_zetaWindowInverseSquareMass_left_shell_rvm_bound :
    ∃ C : ℝ, 0 <= C ∧
      ∀ {t R : ℝ},
        200 <= t ->
        0 < R ->
        5 <= t-2*R ->
        zetaWindowInverseSquareMass t (t-2*R) (t-R)
          <=
        C * (R+1) * Real.log (t-R+4) / R^2 := by
  obtain ⟨C, hC0, hwin⟩ := exists_zetaWindowInverseSquareMass_rvm_bound
  refine ⟨C, hC0, ?_⟩
  intro t R ht hR hleft
  have hAB : t-2*R < t-R := by linarith
  have hsep :
      ∀ rho ∈ zetaZeroConfig.window (t-2*R) (t-R),
        R <= |rho.im-t| := by
    intro rho hrho
    have hneg : rho.im - t < 0 := by linarith [hrho.2.2]
    rw [abs_of_neg hneg]
    linarith [hrho.2.2]
  have h := hwin (t:=t) (A:=t-2*R) (B:=t-R) (d:=R)
    hleft hAB hR hsep
  convert h using 1 <;> ring

/-- Unconditional all-real unit-window inverse-square estimate.  This is the
literal negative-ordinate bridge: `T` is arbitrary, and the local zero count
already pays the window by `log (|T|+3)`. -/
theorem exists_zetaWindowInverseSquareMass_unit_local_bound :
    ∃ A0 : ℝ, 0 <= A0 ∧
      ∀ {t T d : ℝ},
        0 < d ->
        (∀ rho ∈ zetaZeroConfig.window T (T+1),
          d <= |rho.im-t|) ->
        zetaWindowInverseSquareMass t T (T+1)
          <= A0 * Real.log (|T|+3) / d^2 := by
  obtain ⟨A0, hA01, hlocal⟩ := Zeta23.RvM.zeta_local_zero_count
  have hA00 : 0 <= A0 := by linarith
  refine ⟨A0, hA00, ?_⟩
  intro t T d hd hsep
  have hbase := zetaWindowInverseSquareMass_le_count_div_sq hd hsep
  have hN :
      (Ncount T (T+1) : ℝ) <= A0 * Real.log (|T|+3) := by
    simpa only [Zeta23.zetaZeroConfig_N] using hlocal T
  have hd2 : 0 < d^2 := by positivity
  exact hbase.trans (div_le_div_of_nonneg_right hN hd2.le)

/-- Every all-real unit window strictly to the left of `t` has an explicit
inverse-square bound with distance measured from its right endpoint. -/
theorem exists_zetaWindowInverseSquareMass_left_unit_local_bound :
    ∃ A0 : ℝ, 0 <= A0 ∧
      ∀ {t T : ℝ},
        T+1 < t ->
        zetaWindowInverseSquareMass t T (T+1)
          <= A0 * Real.log (|T|+3) / (t-(T+1))^2 := by
  obtain ⟨A0, hA00, hunit⟩ :=
    exists_zetaWindowInverseSquareMass_unit_local_bound
  refine ⟨A0, hA00, ?_⟩
  intro t T hT
  have hd : 0 < t-(T+1) := by linarith
  have hsep :
      ∀ rho ∈ zetaZeroConfig.window T (T+1),
        t-(T+1) <= |rho.im-t| := by
    intro rho hrho
    have hneg : rho.im-t < 0 := by linarith [hrho.2.2]
    rw [abs_of_neg hneg]
    linarith [hrho.2.2]
  exact hunit hd hsep

/-- Every all-real unit window strictly to the right of `t` has an explicit
inverse-square bound with distance measured from its left endpoint. -/
theorem exists_zetaWindowInverseSquareMass_right_unit_local_bound :
    ∃ A0 : ℝ, 0 <= A0 ∧
      ∀ {t T : ℝ},
        t < T ->
        zetaWindowInverseSquareMass t T (T+1)
          <= A0 * Real.log (|T|+3) / (T-t)^2 := by
  obtain ⟨A0, hA00, hunit⟩ :=
    exists_zetaWindowInverseSquareMass_unit_local_bound
  refine ⟨A0, hA00, ?_⟩
  intro t T hT
  have hd : 0 < T-t := by linarith
  have hsep :
      ∀ rho ∈ zetaZeroConfig.window T (T+1),
        T-t <= |rho.im-t| := by
    intro rho hrho
    have hpos : 0 < rho.im-t := by linarith [hrho.2.1]
    rw [abs_of_pos hpos]
    linarith [hrho.2.1]
  exact hunit hd hsep

end Synthesis