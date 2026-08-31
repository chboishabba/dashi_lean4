/-
# Row A1a — the averaging variation `Q` vanishes on mixed Lorentz components

The constrained first background variation of the fluctuation operator is a sum
of three pieces (`FirstVariationDecomposition`),

    V = W + Q + R,
      W = D_bg Δ(U),   Q = D_bg Q_j(U),   R = D_bg (gauge/constrained projection),

and the previous rounds treated `Q` as an *unknown* whose size had to be paid by
an absolute-value budget.  This file removes `Q` from the budget entirely on the
components that matter, by a structural — not numerical — argument.

The block-averaging operator of a lattice gauge theory is *literally written out
here*, with the background entering only through colour transports:

    (Q(T) A)_μ(y)^a
      = L^{-5} Σ_{r ∈ [0,L)^4} Σ_{k ∈ [0,L)} Σ_b
          T(x_r, μ, k)^{ab} · A_μ(x_r + k e_μ)^b,     x_r = L·y + r.

The coarse link in direction `μ` averages the fine links of the axial path in
direction `μ` inside its block; the background transports `T` rotate *colour*,
never direction.  Hence, for every background:

* `blockAverage_depends_only_on_same_direction` : `(QA)_μ` depends on `A` only
  through its `μ`-components;
* `averagingKernel_mixed_zero` : the kernel entry coupling a coarse `α`-link to
  a fine `β`-link vanishes whenever `α ≠ β`;
* `averagingKernel_mixed_const`, `deriv_averagingKernel_mixed_zero`,
  `iteratedDeriv_averagingKernel_mixed_zero` : consequently *every* background
  derivative of the mixed kernel entry vanishes — to all orders, for an
  arbitrary background family.

So on a mixed Lorentz component `α ≠ β` the piece `Q` of `V = W + Q + R` is
identically zero, and the Row A1a patch problem loses one of its two error
terms.  Nothing is assumed about the background: the argument is that the
averaging is block diagonal in the Lorentz index, which is a property of the
definition of block averaging itself.
-/
import Mathlib

namespace YangMills

/-! ## 1. The literal block-averaging operator -/

/-- Fine lattice sites. -/
abbrev Site : Type := Fin 4 → ℤ

/-- A Lie-algebra valued fluctuation field on the fine links, `A_μ(x)^a`. -/
abbrev LinkField (color : Type*) : Type _ := Site → Fin 4 → color → ℝ

/-- Background transport data: for every fine site, direction and step along the
axial path, a colour-space matrix.  A transport acts on the colour index only —
it cannot move a link from one direction to another. -/
abbrev TransportData (color : Type*) : Type _ := Site → Fin 4 → ℕ → Matrix color color ℝ

/-- The fine site `L·y + r` of the block over the coarse site `y`. -/
def blockSite (L : ℕ) (y : Site) (r : Fin 4 → Fin L) : Site :=
  fun mu => (L : ℤ) * y mu + (r mu : ℤ)

/-- The fine site obtained from `x` by `k` steps in direction `mu`. -/
def shiftSite (x : Site) (mu : Fin 4) (k : ℕ) : Site :=
  fun nu => if nu = mu then x nu + (k : ℤ) else x nu

/-- **The literal background-dependent block-averaging operator.**  The coarse
link variable in direction `μ` over the coarse site `y` is the block average, at
block size `L`, of the fine `μ`-links of the axial paths of the block, each
transported to the block base point by the background. -/
noncomputable def blockAverage {color : Type*} [Fintype color] (L : ℕ)
    (T : TransportData color) (A : LinkField color) :
    Site → Fin 4 → color → ℝ :=
  fun y mu a => ((L : ℝ) ^ 5)⁻¹ * ∑ r : Fin 4 → Fin L, ∑ k : Fin L, ∑ b : color,
    T (blockSite L y r) mu k a b * A (shiftSite (blockSite L y r) mu k) mu b

/-! ## 2. Lorentz block diagonality -/

/-- **The averaging of a coarse `μ`-link sees only the fine `μ`-links.**  Two
fluctuation fields that agree in direction `μ` have the same `μ`-average, for
every background. -/
theorem blockAverage_depends_only_on_same_direction {color : Type*} [Fintype color]
    (L : ℕ) (T : TransportData color) (A A' : LinkField color) (mu : Fin 4)
    (h : ∀ x b, A x mu b = A' x mu b) (y : Site) (a : color) :
    blockAverage L T A y mu a = blockAverage L T A' y mu a := by
  unfold blockAverage
  refine congrArg _ (Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun b _ => ?_)
  rw [h]

/-- Averaging is additive in the fluctuation field. -/
theorem blockAverage_add {color : Type*} [Fintype color] (L : ℕ)
    (T : TransportData color) (A A' : LinkField color) (y : Site) (mu : Fin 4) (a : color) :
    blockAverage L T (fun x nu b => A x nu b + A' x nu b) y mu a
      = blockAverage L T A y mu a + blockAverage L T A' y mu a := by
  unfold blockAverage
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- Averaging is homogeneous in the fluctuation field. -/
theorem blockAverage_smul {color : Type*} [Fintype color] (L : ℕ)
    (T : TransportData color) (A : LinkField color) (t : ℝ)
    (y : Site) (mu : Fin 4) (a : color) :
    blockAverage L T (fun x nu b => t * A x nu b) y mu a
      = t * blockAverage L T A y mu a := by
  have hS : (∑ r : Fin 4 → Fin L, ∑ k : Fin L, ∑ b : color,
        T (blockSite L y r) mu k a b * (t * A (shiftSite (blockSite L y r) mu k) mu b))
      = t * ∑ r : Fin 4 → Fin L, ∑ k : Fin L, ∑ b : color,
        T (blockSite L y r) mu k a b * A (shiftSite (blockSite L y r) mu k) mu b := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  simp only [blockAverage]
  rw [hS]
  ring

/-- The unit fluctuation field supported on the single fine link `(x₀, β)` with
colour `b₀`.  Evaluating the averaging on it extracts a kernel entry. -/
def unitLink {color : Type*} [DecidableEq color] (x0 : Site) (be : Fin 4) (b0 : color) :
    LinkField color :=
  fun x mu b => if x = x0 ∧ mu = be ∧ b = b0 then 1 else 0

/-- The kernel of the averaging operator: the coefficient with which the fine
link `(x, β, b)` enters the coarse average `(QA)_α(y)^a`. -/
noncomputable def averagingKernel {color : Type*} [Fintype color] [DecidableEq color]
    (L : ℕ) (T : TransportData color) (y : Site) (al : Fin 4) (a : color)
    (x : Site) (be : Fin 4) (b : color) : ℝ :=
  blockAverage L T (unitLink x be b) y al a

/-- **The averaging kernel is Lorentz diagonal.**  For `α ≠ β` the coefficient
of a fine `β`-link in a coarse `α`-average is zero, whatever the background. -/
theorem averagingKernel_mixed_zero {color : Type*} [Fintype color] [DecidableEq color]
    (L : ℕ) (T : TransportData color) (y : Site) (al : Fin 4) (a : color)
    (x : Site) (be : Fin 4) (b : color) (hne : al ≠ be) :
    averagingKernel L T y al a x be b = 0 := by
  have hz : blockAverage L T (unitLink x be b) y al a
      = blockAverage L T (fun _ _ _ => (0 : ℝ)) y al a := by
    refine blockAverage_depends_only_on_same_direction L T _ _ al (fun x' b' => ?_) y a
    simp [unitLink, hne]
  rw [averagingKernel, hz]
  simp [blockAverage]

/-! ## 3. Every background derivative of a mixed entry vanishes -/

/-- Along an arbitrary background family the mixed kernel entry is the constant
function `0`. -/
theorem averagingKernel_mixed_const {color : Type*} [Fintype color] [DecidableEq color]
    (L : ℕ) (T : ℝ → TransportData color) (y : Site) (al : Fin 4) (a : color)
    (x : Site) (be : Fin 4) (b : color) (hne : al ≠ be) :
    (fun t : ℝ => averagingKernel L (T t) y al a x be b) = fun _ => 0 :=
  funext fun t => averagingKernel_mixed_zero L (T t) y al a x be b hne

/-- **`Q = D_bg Q_j(U)` vanishes on mixed Lorentz components.**  The first
background variation of the averaging operator has no mixed entries, for an
arbitrary background family. -/
theorem deriv_averagingKernel_mixed_zero {color : Type*} [Fintype color] [DecidableEq color]
    (L : ℕ) (T : ℝ → TransportData color) (y : Site) (al : Fin 4) (a : color)
    (x : Site) (be : Fin 4) (b : color) (hne : al ≠ be) (t0 : ℝ) :
    deriv (fun t : ℝ => averagingKernel L (T t) y al a x be b) t0 = 0 := by
  rw [averagingKernel_mixed_const L T y al a x be b hne]
  simp

/-- The same to all orders: no background variation of any order produces a
mixed entry. -/
theorem iteratedDeriv_averagingKernel_mixed_zero {color : Type*} [Fintype color]
    [DecidableEq color] (L : ℕ) (T : ℝ → TransportData color) (y : Site)
    (al : Fin 4) (a : color) (x : Site) (be : Fin 4) (b : color) (hne : al ≠ be)
    (n : ℕ) (hn : 0 < n) (t0 : ℝ) :
    iteratedDeriv n (fun t : ℝ => averagingKernel L (T t) y al a x be b) t0 = 0 := by
  rw [averagingKernel_mixed_const L T y al a x be b hne, iteratedDeriv_const, if_neg hn.ne']

end YangMills
