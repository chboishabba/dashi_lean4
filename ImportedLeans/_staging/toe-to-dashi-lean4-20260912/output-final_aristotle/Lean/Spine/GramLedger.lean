/-
# The Gram ledger, owned once

A second **domain-neutral spine carrier** for the Navier–Stokes lane of this
corpus.  Three places in the tree state the same finite fact about a family of
vectors in a real inner-product space — that the squared norm of the sum splits
into the sum of the squared norms plus a signed cross term — each in its own
presentation:

* **Agda, list form.**  `DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact`
  defines `sumCells`, `cellMassSum`, `gramDebt` by recursion on a
  `List (Complex3 F)` over the exact rational carrier, and proves
  `‖sumCells cells‖² ≡ cellMassSum cells + gramDebt cells`, with the corollary
  that a nonpositive `gramDebt` bounds the aggregate by the cell masses.
* **Agda, R582.**  `…NSTriadKNClassNormBudgetToBonyGramPaymentRound582Exact`
  adds `0 ≤ cellMassSum`, hence `gramDebt cells ≤ ‖sumCells cells‖²`, and uses
  it to convert *any* independently proved class-norm budget into an R580
  Gram-residual payment.
* **Lean, Finset form.**  The archived DASHI Navier–Stokes worker file
  `Provenance/ns_worker_result/RequestProject/NavierStokes/RateBlockGramBound.lean`
  (namespace `ClayNS.RateBlocks`) states the same fact as
  `nsq_sum_eq_sum_sum_herm_re : ‖∑_p G_p‖² = ∑_{p,q} Re⟪G_p, G_q⟫` and uses it
  to locate the remaining obligation as square-root cancellation inside one
  dyadic rate block.  That file is not buildable in this checkout: it imports
  `RequestProject.NavierStokes.TransverseFrameSplit`, which no handoff has
  shipped.

This module proves both presentations over an arbitrary real inner-product
space and, in `ofFn_massSum_add_gramDebt_eq_double_sum`, the **transport**
identifying them: the list-recursive ledger of `List.ofFn G` equals the
`Finset` double sum of `G`.  So the two consumers do not merely use similar
statements; they use the same one.

## Scope

The OpenAI `NavierStokesAndEuler` proof (preserved under
`Provenance/openai-ns-20260912/`) has **no** consumer of this carrier: its
2659 delivered modules contain no Schur test, no Galerkin truncation, no
Littlewood–Paley/Bony decomposition and no Gram ledger of this shape.  This
carrier is therefore a DASHI-internal Agda↔Lean bridge only, and nothing here
bears on finite-time blowup or on global regularity.
-/
import Mathlib

noncomputable section

namespace Spine
namespace GramLedger

open Finset

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ## 1.  The list presentation (the Agda R180 shape) -/

/-- `cellMassSum` of the Agda ledger: the sum of the squared norms of the cells. -/
def massSum (cells : List V) : ℝ := (cells.map (fun v => ‖v‖ ^ 2)).sum

/-- `gramDebt` of the Agda ledger: the signed cross term, accumulated by the
same recursion, `2 ⟪u, ∑ us⟫ + gramDebt us`. -/
def gramDebt : List V → ℝ
  | [] => 0
  | u :: us => 2 * (inner ℝ u us.sum) + gramDebt us

omit [InnerProductSpace ℝ V] in
@[simp] theorem massSum_nil : massSum ([] : List V) = 0 := by simp [massSum]

@[simp] theorem gramDebt_nil : gramDebt ([] : List V) = 0 := rfl

omit [InnerProductSpace ℝ V] in
/-- Every cell mass is nonnegative, so the mass sum is (Agda R582's
`cellMassSumNonnegative582`). -/
theorem massSum_nonneg (cells : List V) : 0 ≤ massSum cells := by
  induction cells with
  | nil => simp
  | cons u us ih =>
      simp only [massSum, List.map_cons, List.sum_cons] at *
      positivity

/-- **The ledger identity** (Agda R180): the squared norm of the aggregate is
the cell-mass sum plus the Gram debt. -/
theorem sq_norm_sum_eq_massSum_add_gramDebt (cells : List V) :
    ‖cells.sum‖ ^ 2 = massSum cells + gramDebt cells := by
  induction cells with
  | nil => simp
  | cons u us ih =>
      rw [List.sum_cons, norm_add_sq_real, ih]
      simp only [massSum, gramDebt, List.map_cons, List.sum_cons]
      ring

/-- **Agda R582's payment lemma**: any bound on the aggregate is automatically a
bound on the Gram debt. -/
theorem gramDebt_le_sq_norm_sum (cells : List V) :
    gramDebt cells ≤ ‖cells.sum‖ ^ 2 := by
  have h := sq_norm_sum_eq_massSum_add_gramDebt cells
  have hm := massSum_nonneg cells
  linarith

/-- **Agda R180's `nonpositiveGramDebtClosesFibre`**: a nonpositive Gram debt
bounds the aggregate by the cell masses. -/
theorem sq_norm_sum_le_massSum_of_gramDebt_nonpos {cells : List V}
    (h : gramDebt cells ≤ 0) : ‖cells.sum‖ ^ 2 ≤ massSum cells := by
  have := sq_norm_sum_eq_massSum_add_gramDebt cells
  linarith

/-! ## 2.  The `Finset` presentation (the DASHI `ClayNS.RateBlocks` shape) -/

/-- `ClayNS.RateBlocks.nsq_sum_eq_sum_sum_herm_re`: the squared norm of a finite
sum is the full signed double sum of real inner products. -/
theorem sq_norm_sum_eq_double_sum {ι : Type*} (s : Finset ι) (G : ι → V) :
    ‖∑ p ∈ s, G p‖ ^ 2 = ∑ p ∈ s, ∑ q ∈ s, (inner ℝ (G p) (G q) : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  exact Finset.sum_congr rfl fun p _ => inner_sum _ _ _

/-! ## 3.  The transport between the two presentations -/

/-- **Carrier equality.**  For a finite family `G : Fin n → V`, the Agda-side
list ledger of `List.ofFn G` and the DASHI-Lean-side `Finset` double sum are
the same real number.  Both consumers factor through one carrier. -/
theorem ofFn_massSum_add_gramDebt_eq_double_sum {n : ℕ} (G : Fin n → V) :
    massSum (List.ofFn G) + gramDebt (List.ofFn G)
      = ∑ p, ∑ q, (inner ℝ (G p) (G q) : ℝ) := by
  rw [← sq_norm_sum_eq_massSum_add_gramDebt, ← sq_norm_sum_eq_double_sum, List.sum_ofFn]

/-- The Gram debt of a finite family, in the `Finset` presentation: the double
sum minus the diagonal. -/
theorem ofFn_gramDebt_eq {n : ℕ} (G : Fin n → V) :
    gramDebt (List.ofFn G) = (∑ p, ∑ q, (inner ℝ (G p) (G q) : ℝ)) - ∑ p, ‖G p‖ ^ 2 := by
  have h := ofFn_massSum_add_gramDebt_eq_double_sum G
  have hm : massSum (List.ofFn G) = ∑ p, ‖G p‖ ^ 2 := by
    simp [massSum, List.map_ofFn, List.sum_ofFn, Function.comp]
  rw [hm] at h
  linarith

end GramLedger
end Spine
