/-
# Row A1.1 — the constructed averaging map *is* the flat/main specialisation
Eq. (125) of the Bałaban averaging paper (CMP 98)

## Source data used here

The literal source formula that this file consumes is the flat/main
specialisation of the averaging operator, in the form supplied with the task:

    (Q₀ A)_c = Σ_{x ∈ B(c₋)} L^{-(d+1)} (R_{0,c₋} A)([x,x']) .              (125)

Reading of the symbols, fixed once and used consistently below:

* `c` is a coarse bond in direction `μ` over the coarse site `y`; `c₋` is its
  initial coarse site and `B(c₋) = { L·y + r : r ∈ [0,L)^d }` is the block of
  fine sites over it (`L^d` of them);
* `x' = x + L e_μ` is the fine site of the *next* block matched with `x`, so
  that `[x,x']` is the axial fine path of `L` links joining them;
* `A([x,x'])` is the value of the fine Lie-algebra-valued one-form `A` on that
  path, i.e. the sum of its `L` link values;
* `R_{0,c₋}` is the parallel transport of the fine one-form to the base point of
  the block — a *colour* rotation, direction preserving;
* `L^{-(d+1)}` is the normalising weight: `L^d` paths of `L` links each.

In `d = 4`, `L^{-(d+1)} = L^{-5}`.

## What is proved

* `cmp98Q_eq_blockAverage` — the operator written literally in the shape of
  Eq. (125) (with the transport factor `R_{0,c₋}` kept general) **is** the
  block-averaging operator `blockAverage` that the rest of the Row A1 lane is
  built on.  Not an isomorphic analogue: an equality of the two functions.
* `cmp98Q_flat_eq_blockSum`, `cmp98Q_flat_const` — the flat specialisation
  `R_{0,c₋} = 1` is the plain normalised block sum and reproduces constants, so
  the weight `L^{-(d+1)}` is exactly the normalisation of Eq. (125).
* `cmp98Q_flat_eq_kernel`, `cmp98_index_displacement` — Eq. (125) in kernel
  form: the weights are `blockAveragingWeight L ≡ L^{-5}` and the displacements
  are `blockAveragingDispl L μ`, i.e. precisely the kernel data that
  `AveragingKernelNormalization` / `ZeroMassKernelVanishing` consume.  This is
  the same-object identification of the Row A1 kernel data with Eq. (125).

**Honest status.**  This closes the *flat/main specialisation* leg of A1.1 only.
The background-dependent adjoint factors of the general averaging formula are
treated in `CMP98BackgroundDerivative.lean`, where only the derivative of the
background family is needed; the analyticity/uniform-neighbourhood statement of
the source is not proved here and is not used here.
-/
import RequestProject.YangMills.AveragingKernelNormalization

namespace YangMills

open Finset

/-! ## 1. Eq. (125) written literally -/

/-- `(R_{0,c₋} A)([x,x'])` — the transported value of the fine one-form `A` on
the axial path `[x, x + L e_μ]`: the sum over its `L` links of the colour
rotation of the link value to the base point `x`. -/
noncomputable def cmp98PathVariable {color : Type*} [Fintype color] (L : ℕ)
    (T : TransportData color) (A : LinkField color) (x : Site) (mu : Fin 4)
    (a : color) : ℝ :=
  ∑ k : Fin L, ∑ b : color, T x mu k a b * A (shiftSite x mu k) mu b

/-- **Eq. (125), literally.**  `(Q A)_c = Σ_{x ∈ B(c₋)} L^{-(d+1)} (R A)([x,x'])`
with `d = 4`, the block `B(c₋)` enumerated by `r ∈ [0,L)^4` through
`x = L·y + r`. -/
noncomputable def cmp98Q {color : Type*} [Fintype color] (L : ℕ)
    (T : TransportData color) (A : LinkField color) :
    Site → Fin 4 → color → ℝ :=
  fun y mu a =>
    ∑ r : Fin 4 → Fin L,
      ((L : ℝ) ^ (4 + 1))⁻¹ * cmp98PathVariable L T A (blockSite L y r) mu a

/-- **The same-object identification.**  The operator of Eq. (125) and the
block-averaging operator used throughout the Row A1 lane are the same function
of `(L, T, A)` — for every background transport, not only the flat one. -/
theorem cmp98Q_eq_blockAverage {color : Type*} [Fintype color] (L : ℕ)
    (T : TransportData color) (A : LinkField color) :
    cmp98Q L T A = blockAverage L T A := by
  funext y mu a
  unfold cmp98Q blockAverage cmp98PathVariable
  rw [Finset.mul_sum]

/-! ## 2. The flat specialisation `R_{0,c₋} = 1` -/

/-- **Eq. (125) at the flat background is the plain normalised block sum.** -/
theorem cmp98Q_flat_eq_blockSum {color : Type*} [Fintype color] [DecidableEq color]
    (L : ℕ) (A : LinkField color) (y : Site) (mu : Fin 4) (a : color) :
    cmp98Q L (flatTransport color) A y mu a
      = ((L : ℝ) ^ 5)⁻¹ * ∑ r : Fin 4 → Fin L, ∑ k : Fin L,
          A (shiftSite (blockSite L y r) mu k) mu a := by
  rw [cmp98Q_eq_blockAverage, blockAverage_flatTransport]

/-- **The weight of Eq. (125) is the correct normalisation.**  `L^{-(d+1)}`
against `L^d` paths of `L` links reproduces a constant one-form exactly. -/
theorem cmp98Q_flat_const {color : Type*} [Fintype color] [DecidableEq color]
    {L : ℕ} (hL : L ≠ 0) (c : color → ℝ) (y : Site) (mu : Fin 4) (a : color) :
    cmp98Q L (flatTransport color) (fun _ _ b => c b) y mu a = c a := by
  rw [cmp98Q_eq_blockAverage]
  exact blockAverage_flatTransport_const hL c y mu a

/-! ## 3. Eq. (125) in kernel form -/

/-- The fine site carried by the kernel index `i = (r,k)`: the `k`-th site along
the axial `μ`-path starting at the block site `L·y + r`. -/
def cmp98IndexSite (L : ℕ) (y : Site) (mu : Fin 4) (i : BlockKernelIndex L) : Site :=
  shiftSite (blockSite L y i.1) mu i.2

/-- **The displacement attached to a kernel index is the one the Row A1 kernel
machinery uses.**  Relative to the block base point `L·y`, the fine site of the
index `(r,k)` sits at `r + k e_μ`, which is `blockAveragingDispl L μ`. -/
theorem cmp98_index_displacement (L : ℕ) (y : Site) (mu : Fin 4)
    (i : BlockKernelIndex L) :
    (fun nu : Fin 4 => ((cmp98IndexSite L y mu i nu : ℤ) : ℝ) - (L : ℝ) * ((y nu : ℤ) : ℝ))
      = blockAveragingDispl L mu i := by
  funext nu
  by_cases h : nu = mu
  · subst h
    simp [cmp98IndexSite, shiftSite, blockSite, blockAveragingDispl]
    ring
  · simp [cmp98IndexSite, shiftSite, blockSite, blockAveragingDispl, h]

/-- **Eq. (125) is the kernel `(blockAveragingWeight, blockAveragingDispl)`.**
At the flat background the coarse link is the kernel sum over the `L⁵` indices
with constant weight `L^{-(d+1)}`; combined with `cmp98_index_displacement` this
identifies the Row A1 averaging kernel data with the source operator, not with
an analogue of it. -/
theorem cmp98Q_flat_eq_kernel {color : Type*} [Fintype color] [DecidableEq color]
    (L : ℕ) (A : LinkField color) (y : Site) (mu : Fin 4) (a : color) :
    cmp98Q L (flatTransport color) A y mu a
      = ∑ i : BlockKernelIndex L,
          blockAveragingWeight L i * A (cmp98IndexSite L y mu i) mu a := by
  rw [cmp98Q_flat_eq_blockSum, Finset.mul_sum]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by
    simp [blockAveragingWeight, cmp98IndexSite]

end YangMills
