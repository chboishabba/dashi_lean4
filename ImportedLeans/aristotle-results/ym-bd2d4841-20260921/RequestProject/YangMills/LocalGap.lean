/-
# Row A1 — assembling the positive lower bound on the shell beta coefficient

Row A1 of the Balaban small-field survival argument needs a *positive* lower
bound for the one-shell beta coefficient in the form

    β_j  ≥  (11/24) C_A(G)  −  r_local  −  L_β γ B  =:  b₋(G),

where

* `(11/24) C_A` is the universal one-loop coefficient of the shell,
* `r_local` bounds the local (momentum-cell) remainder from below — supplied by
  `ShellBudget.A1a_shell_bound_at_two_fifths` from the near/far pointwise
  estimates,
* `L_β γ B` bounds the history remainder — supplied by
  `BetaObserver.historyRemainder_bound`.

This file performs the assembly and evaluates it with the constants actually
proved in this development.  The decomposition of `β_j` into the universal term
plus the two remainders is the input from the source, and appears explicitly as
a hypothesis; everything else is proved.
-/
import RequestProject.YangMills.ShellBudget
import RequestProject.YangMills.BetaObserver

namespace YangMills

/-- Adjoint Casimir of `SU(N)` in the normalisation `C_A = N`. -/
def casimirAdjointSU (N : ℕ) : ℝ := (N : ℝ)

/-- The Row A1 gap functional `b₋(G) = (11/24) C_A − r_local − hist`. -/
noncomputable def bMinus (CA rlocal hist : ℝ) : ℝ :=
  11 / 24 * CA - rlocal - hist

/-- **Row A1 assembly.**  Given the shell decomposition
`β = (11/24) C_A + R_local + R_hist`, a lower bound `R_local ≥ −r` and a
history budget `|R_hist| ≤ h`, the shell coefficient is bounded below by
`b₋ = (11/24) C_A − r − h`. -/
theorem beta_lower_bound {beta CA Rlocal Rhist r h : ℝ}
    (hdecomp : beta = 11 / 24 * CA + Rlocal + Rhist)
    (hloc : -r ≤ Rlocal) (hhist : |Rhist| ≤ h) :
    bMinus CA r h ≤ beta := by
  have h1 : -h ≤ Rhist := neg_le_of_abs_le hhist
  unfold bMinus
  rw [hdecomp]
  linarith

/-- The exact value of the near/far split cost at the working radius. -/
theorem splitCost_two_fifths_value : splitCost (2 / 5) = 236679 / 640000 := by
  unfold splitCost combinedOfPerOrbit perOrbitNearBound perOrbitFarBound
  norm_num

/-- **Positive gap for `SU(2)`.**  With the local remainder controlled by the
near/far split cost proved in `ShellBudget` and any history budget at most
`1/2`, the Row A1 gap functional is strictly positive. -/
theorem bMinus_pos_SU2 {r h : ℝ} (hr : r ≤ splitCost (2 / 5)) (hh : h ≤ 1 / 2) :
    0 < bMinus (casimirAdjointSU 2) r h := by
  rw [splitCost_two_fifths_value] at hr
  unfold bMinus casimirAdjointSU
  norm_num
  norm_num at hr hh
  linarith

/-- **Positive gap for every `SU(N)`, `N ≥ 2`,** under the same two budgets: the
universal term grows linearly in `N` while the two remainders do not. -/
theorem bMinus_pos_SU {N : ℕ} (hN : 2 ≤ N) {r h : ℝ}
    (hr : r ≤ splitCost (2 / 5)) (hh : h ≤ 1 / 2) :
    0 < bMinus (casimirAdjointSU N) r h := by
  have hcast : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h2 := bMinus_pos_SU2 hr hh
  unfold bMinus casimirAdjointSU at h2 ⊢
  nlinarith

/-- The end-to-end Row A1 statement, with both remainder inputs in the form the
two analysis files deliver them: a shell bound with local budget `r` and a
history budget `L γ B`. -/
theorem beta_pos_of_budgets {N : ℕ} (hN : 2 ≤ N)
    {beta Rlocal Rhist r L gam B : ℝ}
    (hdecomp : beta = 11 / 24 * casimirAdjointSU N + Rlocal + Rhist)
    (hloc : -r ≤ Rlocal) (hr : r ≤ splitCost (2 / 5))
    (hhist : |Rhist| ≤ L * gam * B) (hbudget : L * gam * B ≤ 1 / 2) :
    0 < beta :=
  lt_of_lt_of_le (bMinus_pos_SU hN hr hbudget)
    (beta_lower_bound hdecomp hloc hhist)

end YangMills
