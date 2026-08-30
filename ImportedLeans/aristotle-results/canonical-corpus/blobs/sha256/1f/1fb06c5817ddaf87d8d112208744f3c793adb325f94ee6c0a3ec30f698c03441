/-
**Hot/cold split of a Gram matrix around a bounded-height window.**

The localization programme asks that the exterior of the target window not be
*discarded* but *retained as residual*, so that the pair

    (hot state, cold residual)

reopens the full matrix exactly, and so that the target consumer — the anchored
minor sum of the window — is a function of the hot state alone.

Everything here is proved, not assumed: `reopen_hotBlock_coldResidual` is a
literal identity of matrices, `hotBlock_surjective` shows the hot state loses
nothing that a window-supported matrix could carry, and
`consumer_factors_through_hotBlock` is the universal property (existence *and*
uniqueness of the induced consumer) rather than a postulated field.

The final group specialises this to the anchored observable of
`AnchoredMinorConsumer.lean`: `windowAnchorSum` is by construction hot-determined,
which is the precise sense in which the bounded-height block is a *sufficient*
observer for "is the target zero transversally displaced?".
-/
import RiemannAnalytic.AnchoredMinorConsumer

namespace RiemannAnalytic

open Finset

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section HotCold

variable {n : Type*} [Fintype n] [DecidableEq n] (p : n → Prop) [DecidablePred p]

/-- The **hot state**: the principal block of `M` on the window `p`. -/
def hotBlock (M : Matrix n n ℝ) : Matrix {i // p i} {i // p i} ℝ :=
  M.submatrix Subtype.val Subtype.val

/-- The **cold residual**: everything outside the window block, with the window
block itself zeroed out. -/
def coldResidual (M : Matrix n n ℝ) : Matrix n n ℝ :=
  Matrix.of fun i j => if p i ∧ p j then 0 else M i j

/-- **Reopening**: recombine a hot state and a residual into a full matrix. -/
def reopen (H : Matrix {i // p i} {i // p i} ℝ) (R : Matrix n n ℝ) : Matrix n n ℝ :=
  Matrix.of fun i j => if h : p i ∧ p j then H ⟨i, h.1⟩ ⟨j, h.2⟩ else R i j

variable {p}

omit [Fintype n] [DecidableEq n] in
/-- Reopening the hot state against the cold residual returns the matrix
*exactly*. -/
theorem reopen_hotBlock_coldResidual (M : Matrix n n ℝ) :
    reopen p (hotBlock p M) (coldResidual p M) = M := by
  ext i j
  by_cases h : p i ∧ p j <;> simp [reopen, hotBlock, coldResidual, h]

omit [Fintype n] [DecidableEq n] in
/-- The hot state of a reopened pair is the given hot state. -/
theorem hotBlock_reopen (H : Matrix {i // p i} {i // p i} ℝ) (R : Matrix n n ℝ) :
    hotBlock p (reopen p H R) = H := by
  ext i j
  simp [hotBlock, reopen, i.2, j.2]

omit [Fintype n] [DecidableEq n] in
/-- The cold residual of a reopened pair only sees the residual. -/
theorem coldResidual_reopen (H : Matrix {i // p i} {i // p i} ℝ) (R : Matrix n n ℝ) :
    coldResidual p (reopen p H R) = coldResidual p R := by
  ext i j
  by_cases h : p i ∧ p j <;> simp [coldResidual, reopen, h]

omit [Fintype n] [DecidableEq n] in
/-- Every hot state is realised: the hot block map is surjective. -/
theorem hotBlock_surjective (H : Matrix {i // p i} {i // p i} ℝ) :
    ∃ M : Matrix n n ℝ, hotBlock p M = H :=
  ⟨reopen p H 0, hotBlock_reopen H 0⟩

omit [Fintype n] [DecidableEq n] in
/-- **Universal property of the hot state.**  A consumer that cannot distinguish
two matrices with the same window block factors uniquely through the hot block.
This is the literal form of "the window is a sufficient observer": no extra
information is retained, and the induced consumer is unique. -/
theorem consumer_factors_through_hotBlock (C : Matrix n n ℝ → ℝ)
    (hC : ∀ M M' : Matrix n n ℝ, hotBlock p M = hotBlock p M' → C M = C M') :
    ∃! C' : Matrix {i // p i} {i // p i} ℝ → ℝ, ∀ M, C M = C' (hotBlock p M) := by
  refine ⟨fun H => C (reopen p H 0), fun M => hC _ _ ?_, ?_⟩
  · rw [hotBlock_reopen]
  · intro C'' hC''
    funext H
    have := hC'' (reopen p H 0)
    rw [hotBlock_reopen] at this
    exact this.symm

end HotCold

/-! ### The anchored consumer is hot-determined -/

section AnchoredConsumer

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The anchored `2 × 2` minor read off the matrix entries. -/
def anchorMinorMat (M : Matrix n n ℝ) (i j : n) : ℝ :=
  M i i * M j j - M i j * M j i

omit [Fintype n] [DecidableEq n] in
/-- On a Gram matrix the entrywise anchored minor is the geometric one. -/
theorem anchorMinorMat_gram (v : n → E) (i j : n) :
    anchorMinorMat (Matrix.gram ℝ v) i j = anchorMinor v i j := by
  simp [anchorMinorMat, anchorMinor, Matrix.gram, real_inner_comm (v i) (v j)]
  ring

/-- The anchored observable of a matrix at an anchor coordinate. -/
def anchorMinorMatSum (M : Matrix n n ℝ) (i₀ : n) : ℝ :=
  ∑ j ∈ Finset.univ.erase i₀, anchorMinorMat M i₀ j

theorem anchorMinorMatSum_gram (v : n → E) (i₀ : n) :
    anchorMinorMatSum (Matrix.gram ℝ v) i₀ = anchorMinorSum v i₀ := by
  unfold anchorMinorMatSum anchorMinorSum
  exact Finset.sum_congr rfl fun j _ => anchorMinorMat_gram v i₀ j

variable (p : n → Prop) [DecidablePred p]

/-- The **local anchored consumer**: the anchored observable of the window block,
anchored at a coordinate of the window. -/
def windowAnchorSum (M : Matrix n n ℝ) (i₀ : {i // p i}) : ℝ :=
  anchorMinorMatSum (hotBlock p M) i₀

variable {p}

/-- **Consumer sufficiency of the bounded-height block.**  The local anchored
observable depends on the full matrix only through the hot state. -/
theorem windowAnchorSum_hot_determined {M M' : Matrix n n ℝ}
    (h : hotBlock p M = hotBlock p M') (i₀ : {i // p i}) :
    windowAnchorSum p M i₀ = windowAnchorSum p M' i₀ := by
  unfold windowAnchorSum
  rw [h]

/-- Consequently the local anchored consumer factors uniquely through the hot
state, by the universal property. -/
theorem windowAnchorSum_factors (i₀ : {i // p i}) :
    ∃! C' : Matrix {i // p i} {i // p i} ℝ → ℝ,
      ∀ M, windowAnchorSum p M i₀ = C' (hotBlock p M) :=
  consumer_factors_through_hotBlock (fun M => windowAnchorSum p M i₀)
    fun _ _ h => windowAnchorSum_hot_determined h i₀

omit [Fintype n] [DecidableEq n] [DecidablePred p] in
/-- The window block of a Gram matrix is the Gram matrix of the restricted
family, so the local anchored consumer is the anchored observable of the
compressed vectors. -/
theorem hotBlock_gram (v : n → E) :
    hotBlock p (Matrix.gram ℝ v) = Matrix.gram ℝ (fun i : {i // p i} => v i.1) := by
  ext i j
  simp [hotBlock, Matrix.gram]

theorem windowAnchorSum_gram (v : n → E) (i₀ : {i // p i}) :
    windowAnchorSum p (Matrix.gram ℝ v) i₀ = anchorMinorSum (fun i : {i // p i} => v i.1) i₀ := by
  unfold windowAnchorSum
  rw [hotBlock_gram, anchorMinorMatSum_gram]

end AnchoredConsumer

end RiemannAnalytic
