/-
**Q9 — the anchored-minor observer: the consumer-minimal exterior observable.**

The exterior observable `e₂(G) = ∑_{i<j} det G[{i,j}]` sums *all* pair minors:
`O(q²)` of them for a window with `q` coordinates.  The zero-side coercivity
proof, however, only ever uses minors that involve the anchor coordinate — the
central grid point, where the taper sample is real, so that `b₀ = 0 < a₀`.  This
file isolates that smaller observable and proves it is enough.

* `anchorMinor v i j = ‖v i‖²‖v j‖² − ⟪v i, v j⟫²`, and
  `anchorMinor_eq_det_gram_pair`: it *is* the determinant of the `2 × 2` Gram
  minor `det Gram(v i, v j)`.
* `anchorMinorSum v i₀ = ∑_{j ≠ i₀} det Gram(v i₀, v j)` — only `q − 1` minors.
* `anchorMinorSum_le_e2`: the anchored observable is dominated by the full
  exterior observable, `∑_{j ≠ i₀} det Gram(v i₀, v j) ≤ e₂(G)`; so any
  arithmetic budget for `e₂` is a budget for it, while it may be far smaller.
* `pairDefect_le_anchorMinorSum`: the target's own transverse defect is one term
  of the anchored sum — the target signal survives the passage to the smaller
  observer.
* `gramDefect_ge_anchor_coord_sq_mul`: the coordinate form of the anchor
  argument at an *arbitrary* anchor index (not just the head of a `Fin (d+1)`
  window): if `b i₀ = 0`, then `a_{i₀}² ‖b‖² ≤ ΔGram(a, b)`.  This is what makes
  the anchored observable coercive for the target: the defect is at least the
  anchored two-coordinate minors alone.

Nothing here refers to `ζ`.
-/
import RiemannAnalytic.LocalWindow
import RiemannAnalytic.OneSidedGram

namespace RiemannAnalytic

open Finset

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The anchored minors -/

/-- The `2 × 2` Gram minor of the pair `(v i, v j)`. -/
def anchorMinor {n : Type*} (v : n → E) (i j : n) : ℝ :=
  ‖v i‖ ^ 2 * ‖v j‖ ^ 2 - ⟪v i, v j⟫_ℝ ^ 2

theorem anchorMinor_nonneg {n : Type*} (v : n → E) (i j : n) : 0 ≤ anchorMinor v i j := by
  have := sq_real_inner_le (v i) (v j)
  unfold anchorMinor
  linarith

theorem anchorMinor_comm {n : Type*} (v : n → E) (i j : n) :
    anchorMinor v i j = anchorMinor v j i := by
  unfold anchorMinor
  rw [real_inner_comm (v i) (v j)]
  ring

@[simp] theorem anchorMinor_self {n : Type*} (v : n → E) (i : n) : anchorMinor v i i = 0 := by
  simp [anchorMinor]
  ring

/-- The anchored minor is literally a `2 × 2` Gram determinant. -/
theorem anchorMinor_eq_det_gram_pair {n : Type*} (v : n → E) (i j : n) :
    anchorMinor v i j = (Matrix.gram ℝ ![v i, v j]).det := by
  rw [Matrix.det_fin_two]
  simp [Matrix.gram, anchorMinor, real_inner_comm (v i) (v j)]
  ring

/-- **The anchored observable**: the sum of the `q − 1` principal `2 × 2` minors
that contain the anchor coordinate `i₀`. -/
def anchorMinorSum {n : Type*} [Fintype n] [DecidableEq n] (v : n → E) (i₀ : n) : ℝ :=
  ∑ j ∈ Finset.univ.erase i₀, anchorMinor v i₀ j

theorem anchorMinorSum_nonneg {n : Type*} [Fintype n] [DecidableEq n] (v : n → E) (i₀ : n) :
    0 ≤ anchorMinorSum v i₀ :=
  Finset.sum_nonneg fun j _ => anchorMinor_nonneg v i₀ j

/-- **The target signal survives the passage to the anchored observer.**  The
transverse defect of the anchor against any other coordinate is one term of the
anchored sum. -/
theorem anchorMinor_le_anchorMinorSum {n : Type*} [Fintype n] [DecidableEq n] (v : n → E)
    {i₀ j : n} (hj : j ≠ i₀) : anchorMinor v i₀ j ≤ anchorMinorSum v i₀ :=
  Finset.single_le_sum (f := fun k => anchorMinor v i₀ k)
    (fun k _ => anchorMinor_nonneg v i₀ k) (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)

/-- **The anchored observable is dominated by the full exterior observable.**
Only `q − 1` of the `q(q−1)/2` pair minors are retained, and the retained part
is still under any budget for `e₂`. -/
theorem anchorMinorSum_le_e2 {n : Type*} [Fintype n] [DecidableEq n] (v : n → E) (i₀ : n) :
    anchorMinorSum v i₀
      ≤ e2OfTraces (Matrix.gram ℝ v).trace ((Matrix.gram ℝ v * Matrix.gram ℝ v).trace) := by
  classical
  rw [e2OfTraces_gram_eq v]
  set D : n → n → ℝ := fun p q => ‖v p‖ ^ 2 * ‖v q‖ ^ 2 - ⟪v p, v q⟫_ℝ ^ 2 with hD
  have hDnn : ∀ p q, 0 ≤ D p q := fun p q => anchorMinor_nonneg v p q
  have hrow : ∑ j : n, D i₀ j ≤ ∑ p : n, ∑ q : n, D p q :=
    Finset.single_le_sum (f := fun p => ∑ q : n, D p q)
      (fun p _ => Finset.sum_nonneg fun q _ => hDnn p q) (Finset.mem_univ i₀)
  -- the column through the anchor, dropping the anchor row itself
  have hcol : ∑ p ∈ Finset.univ.erase i₀, D p i₀
      ≤ ∑ p ∈ Finset.univ.erase i₀, ∑ q : n, D p q :=
    Finset.sum_le_sum fun p _ =>
      Finset.single_le_sum (f := fun q => D p q) (fun q _ => hDnn p q) (Finset.mem_univ i₀)
  have hsplit : ∑ p : n, ∑ q : n, D p q
      = (∑ q : n, D i₀ q) + ∑ p ∈ Finset.univ.erase i₀, ∑ q : n, D p q := by
    rw [← Finset.add_sum_erase _ (fun p => ∑ q : n, D p q) (Finset.mem_univ i₀)]
  have hrowsum : ∑ q : n, D i₀ q = anchorMinorSum v i₀ := by
    rw [← Finset.add_sum_erase _ (fun q => D i₀ q) (Finset.mem_univ i₀)]
    have : D i₀ i₀ = 0 := anchorMinor_self v i₀
    rw [this, zero_add]
    rfl
  have hcolsum : ∑ p ∈ Finset.univ.erase i₀, D p i₀ = anchorMinorSum v i₀ := by
    rw [← hrowsum, ← Finset.add_sum_erase _ (fun q => D i₀ q) (Finset.mem_univ i₀)]
    have h0 : D i₀ i₀ = 0 := anchorMinor_self v i₀
    rw [h0, zero_add]
    exact Finset.sum_congr rfl fun p _ => anchorMinor_comm v p i₀
  have hkey : 2 * anchorMinorSum v i₀ ≤ ∑ p : n, ∑ q : n, D p q := by
    rw [hsplit, hrowsum]
    have := hcolsum ▸ hcol
    linarith
  linarith

/-! ### Coercivity of the anchored observable for the target -/

/-- **The anchor argument at an arbitrary anchor coordinate.**  If the transverse
coordinate vector vanishes at the anchor index, the Gram defect is at least the
anchor's longitudinal weight times the whole transverse energy:

    `b_{i₀} = 0  ⟹  a_{i₀}² ‖b‖² ≤ ΔGram(a, b)`. -/
theorem gramDefect_ge_anchor_coord_sq_mul {n : Type*} [Fintype n] [DecidableEq n]
    (a b : n → ℝ) (i₀ : n) (hb : b i₀ = 0) :
    a i₀ ^ 2 * (b ⬝ᵥ b) ≤ gramDefect a b := by
  classical
  set s : Finset n := Finset.univ.erase i₀ with hs
  have haa : a ⬝ᵥ a = a i₀ ^ 2 + ∑ i ∈ s, a i ^ 2 := by
    have h1 : a ⬝ᵥ a = ∑ i : n, a i ^ 2 := by simp [dotProduct, sq]
    rw [h1, hs, ← Finset.add_sum_erase _ (fun i => a i ^ 2) (Finset.mem_univ i₀)]
  have hbb : b ⬝ᵥ b = ∑ i ∈ s, b i ^ 2 := by
    have h1 : b ⬝ᵥ b = ∑ i : n, b i ^ 2 := by simp [dotProduct, sq]
    rw [h1, hs, ← Finset.add_sum_erase _ (fun i => b i ^ 2) (Finset.mem_univ i₀), hb]
    ring
  have hab : a ⬝ᵥ b = ∑ i ∈ s, a i * b i := by
    have h1 : a ⬝ᵥ b = ∑ i : n, a i * b i := by simp [dotProduct]
    rw [h1, hs, ← Finset.add_sum_erase _ (fun i => a i * b i) (Finset.mem_univ i₀), hb]
    ring
  have hcs : (∑ i ∈ s, a i * b i) ^ 2 ≤ (∑ i ∈ s, a i ^ 2) * ∑ i ∈ s, b i ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq s a b
  unfold gramDefect
  rw [haa, hbb, hab]
  nlinarith [hcs]

/-- **The anchored observable is coercive for the target.**  Written in the pair
language of `GramBudgetTransport.lean`: the target's Gram defect — the quantity
the tube theorem consumes — is bounded above by the anchored observable of any
family that contains both of the target's vectors.  So the arithmetic side may
be compressed from all pair minors to the anchored ones. -/
theorem pairDefect_le_anchorMinorSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → E) (ρ : ι) :
    pairDefect a b ρ ≤ anchorMinorSum (pairFamily a b) (ρ, false) := by
  have hne : ((ρ, true) : ι × Bool) ≠ (ρ, false) := by simp
  have := anchorMinor_le_anchorMinorSum (pairFamily a b) hne
  simpa [anchorMinor, pairDefect] using this

/-! ### The anchored *coordinate* minors

The Cauchy–Binet expansion of the two-vector Gram defect is a sum of squared
`2 × 2` coordinate minors, one for each pair of coordinates.  Keeping only the
`q − 1` minors that involve the anchor coordinate gives a strictly smaller
observable, `coordAnchorMinorSum`, which is still dominated by the defect
(`coordAnchorMinorSum_le_gramDefect`) and which, at an anchor where the
transverse vector vanishes, is *exactly* the target signal
(`coordAnchorMinorSum_eq_of_anchor`).  So the reduction from all pairs to the
anchored row is lossless for the target and costs the arithmetic side only
`O(q)` minors instead of `O(q²)`. -/

/-- The sum of the squared `2 × 2` coordinate minors through the anchor `i₀`. -/
def coordAnchorMinorSum {n : Type*} [Fintype n] [DecidableEq n] (a b : n → ℝ) (i₀ : n) : ℝ :=
  ∑ j ∈ Finset.univ.erase i₀, (a i₀ * b j - a j * b i₀) ^ 2

theorem coordAnchorMinorSum_nonneg {n : Type*} [Fintype n] [DecidableEq n] (a b : n → ℝ)
    (i₀ : n) : 0 ≤ coordAnchorMinorSum a b i₀ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **The anchored coordinate observable is dominated by the Gram defect.**  The
difference is exactly the Cauchy–Schwarz slack of the two vectors off the
anchor. -/
theorem coordAnchorMinorSum_le_gramDefect {n : Type*} [Fintype n] [DecidableEq n]
    (a b : n → ℝ) (i₀ : n) : coordAnchorMinorSum a b i₀ ≤ gramDefect a b := by
  classical
  set s : Finset n := Finset.univ.erase i₀ with hs
  set A : ℝ := ∑ i ∈ s, a i ^ 2 with hA
  set B : ℝ := ∑ i ∈ s, b i ^ 2 with hB
  set C : ℝ := ∑ i ∈ s, a i * b i with hC
  have haa : a ⬝ᵥ a = a i₀ ^ 2 + A := by
    have h1 : a ⬝ᵥ a = ∑ i : n, a i ^ 2 := by simp [dotProduct, sq]
    rw [h1, hA, hs, ← Finset.add_sum_erase _ (fun i => a i ^ 2) (Finset.mem_univ i₀)]
  have hbb : b ⬝ᵥ b = b i₀ ^ 2 + B := by
    have h1 : b ⬝ᵥ b = ∑ i : n, b i ^ 2 := by simp [dotProduct, sq]
    rw [h1, hB, hs, ← Finset.add_sum_erase _ (fun i => b i ^ 2) (Finset.mem_univ i₀)]
  have hab : a ⬝ᵥ b = a i₀ * b i₀ + C := by
    have h1 : a ⬝ᵥ b = ∑ i : n, a i * b i := by simp [dotProduct]
    rw [h1, hC, hs, ← Finset.add_sum_erase _ (fun i => a i * b i) (Finset.mem_univ i₀)]
  have hexp : coordAnchorMinorSum a b i₀ = a i₀ ^ 2 * B + b i₀ ^ 2 * A - 2 * (a i₀ * b i₀) * C := by
    unfold coordAnchorMinorSum
    rw [← hs]
    have : ∀ j, (a i₀ * b j - a j * b i₀) ^ 2
        = a i₀ ^ 2 * b j ^ 2 + b i₀ ^ 2 * a j ^ 2 - 2 * (a i₀ * b i₀) * (a j * b j) := by
      intro j; ring
    simp only [this]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, ← hA, ← hB, ← hC]
  have hcs : C ^ 2 ≤ A * B := by
    rw [hA, hB, hC]
    exact Finset.sum_mul_sq_le_sq_mul_sq s a b
  unfold gramDefect
  rw [haa, hbb, hab, hexp]
  nlinarith [hcs]

/-- **Tightness at the anchor.**  If the transverse vector vanishes at the anchor
coordinate, the anchored coordinate observable is *exactly* the target signal
`a_{i₀}² ‖b‖²`, so nothing is lost by discarding the non-anchored minors. -/
theorem coordAnchorMinorSum_eq_of_anchor {n : Type*} [Fintype n] [DecidableEq n]
    (a b : n → ℝ) (i₀ : n) (hb : b i₀ = 0) :
    coordAnchorMinorSum a b i₀ = a i₀ ^ 2 * (b ⬝ᵥ b) := by
  classical
  unfold coordAnchorMinorSum
  have h1 : ∀ j, (a i₀ * b j - a j * b i₀) ^ 2 = a i₀ ^ 2 * b j ^ 2 := by
    intro j; rw [hb]; ring
  simp only [h1, ← Finset.mul_sum]
  have h2 : b ⬝ᵥ b = ∑ i ∈ Finset.univ.erase i₀, b i ^ 2 := by
    have h3 : b ⬝ᵥ b = ∑ i : n, b i ^ 2 := by simp [dotProduct, sq]
    rw [h3, ← Finset.add_sum_erase _ (fun i => b i ^ 2) (Finset.mem_univ i₀), hb]
    ring
  rw [h2]

end RiemannAnalytic
