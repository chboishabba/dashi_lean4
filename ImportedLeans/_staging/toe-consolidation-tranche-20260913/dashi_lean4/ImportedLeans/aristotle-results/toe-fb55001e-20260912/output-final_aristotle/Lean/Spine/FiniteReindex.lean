import Mathlib
import Spine.TransverseGram
import Spine.MeanSplit

/-!
# Finite reindexing, owned once

Several independent lanes of this corpus need the same fact: *a finite weighted
total does not depend on the order in which the carrier is listed*.  It shows up

* as Galerkin-style presentation invariance of a finite spectral sum,
* as the reindexing step of a deletion/fibre argument in partition-style
  combinatorics,
* and as the presentation independence of the transverse Gram certificate
  attached to a structured observer (`Integration.EnumInvariance`).

Before this file each consumer owned its own copy.  Here the fact is proved once
for an arbitrary carrier and an arbitrary additive weight, and the consumers are
recovered as successive **layers**:

```
fold invariance            foldW w e = foldW w (e ∘ σ)
   ↓
mean invariance            meanW w e = meanW w (e ∘ σ)
   ↓
moment / Gram-entry        ∑ (w a)^k,  ∑ u a * v a
   ↓
determinant / certificate  det Gram(v ∘ τ) = det Gram v,  area2 (σ·a) (σ·b) = area2 a b
```

Contents.

* `foldW` and `foldW_perm` — the weighted fold of a list of carrier elements is
  invariant under permutation of the list;
* `perm_of_nodup_mem` and `foldW_of_nodup_mem` — the *exact* statement the
  consumers want: two duplicate-free enumerations with the same membership are
  promoted to a genuine permutation, and therefore give the same total.  This is
  the "presentation" form: no order is chosen, only the set of listed items;
* `foldW_eq_sum_univ` — a duplicate-free enumeration of the whole carrier folds
  to the `Finset.univ` sum, which is the canonical presentation;
* `sum_comp_equiv` — the indexed form: reindexing a family along a bijection of
  index sets leaves the sum unchanged;
* `foldW_fiberwise` — the combinatorial consumer: summing over a marked source
  set equals summing the same weight over the fibres of any classifying map, so
  a deletion/residual decomposition is an exact reindexing, not an estimate;
* `meanW_perm`, `moment_perm`, `gramEntry_perm` — layers two and three;
* `permVec`, `inner_permVec`, `avg_permVec`, `fluct_permVec`, `area2_permVec`
  and `det_gram_reindex` — layer four, on `EuclideanSpace ℝ (Fin n)`: the inner
  product, the mean, the fixed ⊕ transverse splitting, the anchored area and the
  Gram determinant are all reindexing invariant.  `Integration.EnumInvariance`
  now imports these instead of re-proving them.

Nothing here is domain specific, and nothing here is analytic: every statement is
a finite algebraic identity.
-/

namespace Spine.FiniteReindex

/-! ## Layer 0: the weighted fold -/

section Fold

variable {α R : Type*} [AddCommMonoid R]

/-- The weighted total of a listed (finite, ordered) presentation of part of a
carrier. -/
def foldW (w : α → R) (e : List α) : R := (e.map w).sum

@[simp] theorem foldW_nil (w : α → R) : foldW w [] = 0 := rfl

@[simp] theorem foldW_cons (w : α → R) (a : α) (e : List α) :
    foldW w (a :: e) = w a + foldW w e := rfl

theorem foldW_append (w : α → R) (e₁ e₂ : List α) :
    foldW w (e₁ ++ e₂) = foldW w e₁ + foldW w e₂ := by
  simp [foldW, List.sum_append]

/-- **Exact permutation invariance of a finite weighted fold.**  This is the
single fact every consumer below is an instance of. -/
theorem foldW_perm (w : α → R) {e₁ e₂ : List α} (h : e₁.Perm e₂) :
    foldW w e₁ = foldW w e₂ :=
  (h.map w).sum_eq

/-- Two duplicate-free presentations with the same membership *are* related by a
permutation.  The hypothesis is membership only — no order, and no chosen
bijection — and the conclusion is proof-relevant permutation data. -/
theorem perm_of_nodup_mem [DecidableEq α] {e₁ e₂ : List α} (h₁ : e₁.Nodup)
    (h₂ : e₂.Nodup) (hmem : ∀ a, a ∈ e₁ ↔ a ∈ e₂) : e₁.Perm e₂ :=
  (List.perm_ext_iff_of_nodup h₁ h₂).mpr hmem

/-- **`FiniteWeightedReindexExact`.**  Duplicate-free enumerations of the same
elements have the same weighted total. -/
theorem foldW_of_nodup_mem [DecidableEq α] (w : α → R) {e₁ e₂ : List α}
    (h₁ : e₁.Nodup) (h₂ : e₂.Nodup) (hmem : ∀ a, a ∈ e₁ ↔ a ∈ e₂) :
    foldW w e₁ = foldW w e₂ :=
  foldW_perm w (perm_of_nodup_mem h₁ h₂ hmem)

/-- A duplicate-free enumeration of the whole carrier folds to the canonical
`Finset.univ` sum, so the canonical presentation may always be used. -/
theorem foldW_eq_sum_univ [Fintype α] [DecidableEq α] (w : α → R) {e : List α}
    (hnd : e.Nodup) (hmem : ∀ a, a ∈ e) : foldW w e = ∑ a, w a := by
  have h : e.Perm (Finset.univ : Finset α).toList := by
    refine perm_of_nodup_mem hnd (Finset.nodup_toList _) ?_
    intro a; simp [hmem a]
  rw [foldW_perm w h]
  simp [foldW]

end Fold

/-! ## Layer 0′: the indexed form and the fibre form -/

section Indexed

variable {ι κ α R : Type*} [AddCommMonoid R]

/-- Reindexing a family along a bijection of index sets does not change its
sum. -/
theorem sum_comp_equiv [Fintype ι] [Fintype κ] (σ : ι ≃ κ) (f : κ → R) :
    ∑ i, f (σ i) = ∑ k, f k := Equiv.sum_comp σ f

/-- The special case of a permutation of one index set: the *presentation
independence* statement `C(e) = C(e ∘ σ)` for a weighted fold. -/
theorem sum_weight_comp_perm [Fintype ι] (w : α → R) (e : ι → α) (σ : Equiv.Perm ι) :
    ∑ i, w (e (σ i)) = ∑ i, w (e i) := Equiv.sum_comp σ (fun i => w (e i))

/-- **The combinatorial (deletion / fibre) consumer.**  Summing a weight over a
marked source set is the same as summing it over the fibres of any classifying
map into a residual index.  So a deletion decomposition is an exact reindexing
of the same total, never an estimate. -/
theorem foldW_fiberwise [DecidableEq κ] [Fintype κ] (s : Finset ι) (g : ι → κ)
    (f : ι → R) : ∑ k, ∑ i ∈ s with g i = k, f i = ∑ i ∈ s, f i :=
  Finset.sum_fiberwise s g f

end Indexed

/-! ## Layer 1: means -/

section Mean

variable {α R : Type*} [DivisionRing R]

/-- The mean of a weight over a listed presentation. -/
def meanW (w : α → R) (e : List α) : R := foldW w e / (e.length : R)

/-- **Mean invariance** — layer one. -/
theorem meanW_perm (w : α → R) {e₁ e₂ : List α} (h : e₁.Perm e₂) :
    meanW w e₁ = meanW w e₂ := by
  unfold meanW
  rw [foldW_perm w h, h.length_eq]

theorem meanW_of_nodup_mem [DecidableEq α] (w : α → R) {e₁ e₂ : List α}
    (h₁ : e₁.Nodup) (h₂ : e₂.Nodup) (hmem : ∀ a, a ∈ e₁ ↔ a ∈ e₂) :
    meanW w e₁ = meanW w e₂ :=
  meanW_perm w (perm_of_nodup_mem h₁ h₂ hmem)

end Mean

/-! ## Layer 2: moments and Gram entries -/

section Moments

variable {α : Type*}

/-- **Moment invariance** — layer two: every power moment of a weight is a fold
of a derived weight, hence presentation free. -/
theorem moment_perm (w : α → ℝ) (k : ℕ) {e₁ e₂ : List α} (h : e₁.Perm e₂) :
    foldW (fun a => w a ^ k) e₁ = foldW (fun a => w a ^ k) e₂ :=
  foldW_perm _ h

/-- **Gram-entry invariance** — layer three: the inner product of two coordinate
weights is a fold, hence presentation free. -/
theorem gramEntry_perm (u v : α → ℝ) {e₁ e₂ : List α} (h : e₁.Perm e₂) :
    foldW (fun a => u a * v a) e₁ = foldW (fun a => u a * v a) e₂ :=
  foldW_perm _ h

end Moments

/-! ## Layer 3: coordinate vectors, the transverse splitting, and determinants

The certificate layer.  These statements were previously owned by
`Integration.EnumInvariance`; they belong here, because they are the last layer
of the same reindexing calculus and have no observer content.
-/

section Coordinates

open RealInnerProductSpace
open Spine
open Spine.MeanSplit

variable {n : ℕ}

/-- Reindexing of a coordinate vector along a permutation of the index set. -/
noncomputable def permVec (σ : Equiv.Perm (Fin n)) (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => v (σ j))

@[simp] theorem permVec_apply (σ : Equiv.Perm (Fin n)) (v : EuclideanSpace ℝ (Fin n))
    (j : Fin n) : permVec σ v j = v (σ j) := rfl

/-- Reindexing is an isometry of the inner product. -/
theorem inner_permVec (σ : Equiv.Perm (Fin n)) (a b : EuclideanSpace ℝ (Fin n)) :
    ⟪permVec σ a, permVec σ b⟫ = ⟪a, b⟫ := by
  rw [inner_eq_sum, inner_eq_sum]
  simpa using Equiv.sum_comp σ (fun j => a j * b j)

theorem norm_sq_permVec (σ : Equiv.Perm (Fin n)) (a : EuclideanSpace ℝ (Fin n)) :
    ‖permVec σ a‖ ^ 2 = ‖a‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_permVec]

/-- The mean is permutation invariant (layer one, in coordinates). -/
theorem avg_permVec (σ : Equiv.Perm (Fin n)) (v : EuclideanSpace ℝ (Fin n)) :
    avg (permVec σ v) = avg v := by
  simp only [avg]
  congr 1
  simpa using Equiv.sum_comp σ (fun j => v j)

/-- Hence the fixed component is merely reindexed. -/
theorem meanPart_permVec (σ : Equiv.Perm (Fin n)) (v : EuclideanSpace ℝ (Fin n)) :
    meanPart (permVec σ v) = permVec σ (meanPart v) := by
  ext j; simp [avg_permVec]

/-- And so is the transverse component: reindexing permutes the transverse
coordinates without changing the splitting. -/
theorem fluct_permVec (σ : Equiv.Perm (Fin n)) (v : EuclideanSpace ℝ (Fin n)) :
    fluct (permVec σ v) = permVec σ (fluct v) := by
  ext j; simp [avg_permVec]

/-- **The anchored area is reindexing invariant** — the certificate layer. -/
theorem area2_permVec (σ : Equiv.Perm (Fin n)) (a b : EuclideanSpace ℝ (Fin n)) :
    area2 (permVec σ a) (permVec σ b) = area2 a b := by
  simp [area2, norm_sq_permVec, inner_permVec]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Permuting a family of vectors conjugates its Gram matrix by the
corresponding permutation matrix, in the form of a symmetric submatrix. -/
theorem gram_comp_perm {r : ℕ} (v : Fin r → V) (τ : Equiv.Perm (Fin r)) :
    Matrix.gram ℝ (v ∘ τ) = (Matrix.gram ℝ v).submatrix τ τ := by
  ext i j; rfl

/-- **The Gram determinant is invariant under reindexing of the family** — the
last layer: the determinant certificate is presentation free. -/
theorem det_gram_reindex {r : ℕ} (v : Fin r → V) (τ : Equiv.Perm (Fin r)) :
    (Matrix.gram ℝ (v ∘ τ)).det = (Matrix.gram ℝ v).det := by
  rw [gram_comp_perm, Matrix.det_submatrix_equiv_self]

end Coordinates

end Spine.FiniteReindex
