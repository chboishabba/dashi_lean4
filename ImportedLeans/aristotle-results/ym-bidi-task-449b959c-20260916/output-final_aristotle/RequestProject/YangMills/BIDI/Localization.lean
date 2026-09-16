/-
# §3 / §9 of the BIDI note: CMP116 differentiated localization

The differentiated boundary contribution is a finite double sum

    B = Σ_Y B_Y,     B_Y = Σ_{γ ∈ Γ_Y} T_{Y,γ}.

This module proves the two finite summation layers, R404 and R405, and the
composite statement (30).  Nothing here is a schema: the sums are ordinary
`Finset` sums and the estimates are ordinary triangle inequalities, so the two
layers really are "compiler owned" — the only analytic content is the termwise
input (26).

* `abs_sum_le_of_termwise_le` (R404) — `|T_{Y,γ}| ≤ M_{Y,γ}` and
  `Σ_γ M_{Y,γ} ≤ M_Y` give `|B_Y| ≤ M_Y`;
* `abs_double_sum_le` (R405) — together with `Σ_Y M_Y ≤ M_shell` this gives
  `|B| ≤ M_shell`;
* `abs_double_sum_le_of_termwise` — the two layers composed, i.e. exactly the
  implication (27)(28)(29) ⟹ (30) of the note.
-/
import Mathlib

namespace RequestProject.YangMills.BIDI

open Finset

variable {ι κ : Type*}

/-- **R404**: termwise majorants plus a shell budget for their sum bound the
sum itself. -/
theorem abs_sum_le_of_termwise_le (Γ : Finset ι) (T M : ι → ℝ) {MY : ℝ}
    (hterm : ∀ γ ∈ Γ, |T γ| ≤ M γ) (hsum : ∑ γ ∈ Γ, M γ ≤ MY) :
    |∑ γ ∈ Γ, T γ| ≤ MY :=
  le_trans (le_trans (Finset.abs_sum_le_sum_abs _ _)
    (Finset.sum_le_sum hterm)) hsum

/-- **R405**: the outer layer.  Shellwise bounds plus a budget for their sum
bound the whole differentiated boundary contribution. -/
theorem abs_double_sum_le (Ys : Finset κ) (B MY : κ → ℝ) {Mshell : ℝ}
    (hshell : ∀ Y ∈ Ys, |B Y| ≤ MY Y) (hsum : ∑ Y ∈ Ys, MY Y ≤ Mshell) :
    |∑ Y ∈ Ys, B Y| ≤ Mshell :=
  abs_sum_le_of_termwise_le Ys B MY hshell hsum

/-- **The composite CMP116 localization**, (27)(28)(29) ⟹ (30): from termwise
bounds on the differentiated terms, the shell sums and the shell budget, the
full differentiated boundary contribution is bounded by `M_shell`. -/
theorem abs_double_sum_le_of_termwise (Ys : Finset κ) (Γ : κ → Finset ι)
    (T : κ → ι → ℝ) (M : κ → ι → ℝ) (MY : κ → ℝ) {Mshell : ℝ}
    (hterm : ∀ Y ∈ Ys, ∀ γ ∈ Γ Y, |T Y γ| ≤ M Y γ)
    (hrow : ∀ Y ∈ Ys, ∑ γ ∈ Γ Y, M Y γ ≤ MY Y)
    (hshell : ∑ Y ∈ Ys, MY Y ≤ Mshell) :
    |∑ Y ∈ Ys, ∑ γ ∈ Γ Y, T Y γ| ≤ Mshell :=
  abs_double_sum_le Ys (fun Y => ∑ γ ∈ Γ Y, T Y γ) MY
    (fun Y hY => abs_sum_le_of_termwise_le (Γ Y) (T Y) (M Y) (hterm Y hY) (hrow Y hY))
    hshell

/-- The same statement with the operator-norm form of the termwise input, which
is how R406 delivers it: each scalar differentiated term is the norm of a
noncommutative operator-product difference. -/
theorem abs_double_sum_le_of_norm_termwise {R : Type*} [NormedRing R]
    (Ys : Finset κ) (Γ : κ → Finset ι) (T : κ → ι → ℝ)
    (P Q : κ → ι → R) (M : κ → ι → ℝ) (MY : κ → ℝ) {Mshell : ℝ}
    (hscalar : ∀ Y ∈ Ys, ∀ γ ∈ Γ Y, |T Y γ| = ‖P Y γ - Q Y γ‖)
    (hprod : ∀ Y ∈ Ys, ∀ γ ∈ Γ Y, ‖P Y γ - Q Y γ‖ ≤ M Y γ)
    (hrow : ∀ Y ∈ Ys, ∑ γ ∈ Γ Y, M Y γ ≤ MY Y)
    (hshell : ∑ Y ∈ Ys, MY Y ≤ Mshell) :
    |∑ Y ∈ Ys, ∑ γ ∈ Γ Y, T Y γ| ≤ Mshell :=
  abs_double_sum_le_of_termwise Ys Γ T M MY
    (fun Y hY γ hγ => (hscalar Y hY γ hγ) ▸ hprod Y hY γ hγ) hrow hshell

end RequestProject.YangMills.BIDI
