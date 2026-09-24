/-
# The exact bilinear form of the two-nuisance elimination, and the finite Gram ledger

`ThreeTaperSchurMargin` computes the *quadratic* form of the elimination operator,

    ‖elim2 n₁ n₂ x‖² = det3(n₁, n₂, x)² / wedgeSq(n₁, n₂).

Everything the finite near-core estimate needs is the *bilinear* companion of that
identity.  Polarization is legitimate here because `elim2 n₁ n₂ ·` is additive and
`det3 n₁ n₂ ·` is additive in its third slot, so

    ⟪elim2 n₁ n₂ x, elim2 n₁ n₂ y⟫
        = det3(n₁, n₂, x) · det3(n₁, n₂, y) / wedgeSq(n₁, n₂) .

Two exact consequences are recorded, both about a *finite* family `v : ι → (Fin 3 → ℝ)`
summed over a `Finset s`.

* **The Gram ledger.**  Writing `E = elim2 n₁ n₂`,

      ‖E (∑ i ∈ s, v i)‖² = ∑ i ∈ s, ‖E (v i)‖² + gramDebt n₁ n₂ s v,

  with `gramDebt` the completely *signed* sum of the off-diagonal pairings.  No
  absolute value and no cardinality factor is introduced anywhere.

* **The scalar collapse.**  Because each pairing is a product of two determinants
  divided by the same Gram determinant, the whole vector problem is one scalar:

      ‖E (∑ i ∈ s, v i)‖² = (∑ i ∈ s, det3(n₁, n₂, v i))² / wedgeSq(n₁, n₂),
      gramDebt          = ((∑ d)² − ∑ d²) / wedgeSq(n₁, n₂),  d i = det3(n₁,n₂,v i).

* **The duplicate no-go.**  If two members of the family are equal — which is exactly
  what happens for a reflection orbit once the stored cell is already the symmetrized
  pair response `Z_σ + Z_{Rσ}` — their cross pairing is `+‖E v‖² ≥ 0`.  So reflection
  symmetry, having already cancelled the odd channel, cannot be reused to manufacture
  negative Gram debt.

No `sorry`, no `axiom`, no Boolean receipt, no numerical evidence.
-/
import Zeta23Bridge.ThreeTaperSchurMargin

noncomputable section

namespace Zeta23Bridge
namespace ThreeTaperSchurGram

open Zeta23Bridge.MultiTaperSchurCore
open Zeta23Bridge.ThreeTaperSchurCore
open Zeta23Bridge.ThreeTaperSchurMargin

/-! ## 1. Additivity of the two ingredients -/

variable {ι : Type*} [Fintype ι]

theorem dotP_zero_right (n : ι → ℝ) : dotP n (0 : ι → ℝ) = 0 := by
  simp [dotP]

/-- `dotP` is additive in the right slot over a finite family. -/
theorem dotP_sum_right {κ : Type*} (n : ι → ℝ) (s : Finset κ) (f : κ → ι → ℝ) :
    dotP n (∑ i ∈ s, f i) = ∑ i ∈ s, dotP n (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [dotP_zero_right]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, dotP_add_right, ih, Finset.sum_insert ha]

/-- `dotP` is additive in the left slot over a finite family. -/
theorem dotP_sum_left {κ : Type*} (n : ι → ℝ) (s : Finset κ) (f : κ → ι → ℝ) :
    dotP (∑ i ∈ s, f i) n = ∑ i ∈ s, dotP (f i) n := by
  rw [dotP_comm, dotP_sum_right]
  exact Finset.sum_congr rfl (fun i _ => dotP_comm n (f i))

theorem transverseComp_zero (n : ι → ℝ) : transverseComp n (0 : ι → ℝ) = 0 := by
  unfold transverseComp
  simp [dotP_zero_right]

theorem elim2_zero (n₁ n₂ : ι → ℝ) : elim2 n₁ n₂ (0 : ι → ℝ) = 0 := by
  unfold elim2
  rw [transverseComp_zero, transverseComp_zero]

/-- The elimination operator commutes with finite sums. -/
theorem elim2_sum {κ : Type*} (n₁ n₂ : ι → ℝ) (s : Finset κ) (v : κ → ι → ℝ) :
    elim2 n₁ n₂ (∑ i ∈ s, v i) = ∑ i ∈ s, elim2 n₁ n₂ (v i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [elim2_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, elim2_add, ih, Finset.sum_insert ha]

theorem det3_add_right (u v x y : Fin 3 → ℝ) :
    det3 u v (x + y) = det3 u v x + det3 u v y := by
  simp [det3, Pi.add_apply]
  ring

theorem det3_zero_right (u v : Fin 3 → ℝ) : det3 u v (0 : Fin 3 → ℝ) = 0 := by
  simp [det3]

/-- `det3` is additive in the third slot over a finite family. -/
theorem det3_sum_right {κ : Type*} (u v : Fin 3 → ℝ) (s : Finset κ) (f : κ → Fin 3 → ℝ) :
    det3 u v (∑ i ∈ s, f i) = ∑ i ∈ s, det3 u v (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [det3_zero_right]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, det3_add_right, ih, Finset.sum_insert ha]

/-! ## 2. The exact bilinear form -/

/-- **Polarized surviving energy.**  The pairing of two eliminated channels is the
product of their determinants divided by the Gram determinant of the nuisance pair. -/
theorem dotP_elim2_mul_wedgeSq (n₁ n₂ x y : Fin 3 → ℝ) :
    dotP (elim2 n₁ n₂ x) (elim2 n₁ n₂ y) * wedgeSq n₁ n₂
      = det3 n₁ n₂ x * det3 n₁ n₂ y := by
  have hsum := normSqP_elim2_mul_wedgeSq n₁ n₂ (x + y)
  have hx := normSqP_elim2_mul_wedgeSq n₁ n₂ x
  have hy := normSqP_elim2_mul_wedgeSq n₁ n₂ y
  have hE : elim2 n₁ n₂ (x + y) = elim2 n₁ n₂ x + elim2 n₁ n₂ y := elim2_add n₁ n₂ x y
  have hnorm : normSqP (elim2 n₁ n₂ x + elim2 n₁ n₂ y)
      = normSqP (elim2 n₁ n₂ x) + 2 * dotP (elim2 n₁ n₂ x) (elim2 n₁ n₂ y)
        + normSqP (elim2 n₁ n₂ y) := by
    set u := elim2 n₁ n₂ x
    set w := elim2 n₁ n₂ y
    have h1 : dotP (u + w) (u + w) = dotP (u + w) u + dotP (u + w) w :=
      dotP_add_right _ _ _
    have h2 : dotP (u + w) u = dotP u u + dotP u w := by
      rw [dotP_comm, dotP_add_right]
    have h3 : dotP (u + w) w = dotP u w + dotP w w := by
      rw [dotP_comm, dotP_add_right, dotP_comm w u]
    unfold normSqP
    rw [h1, h2, h3]
    ring
  rw [hE, hnorm] at hsum
  rw [det3_add_right] at hsum
  nlinarith [hsum, hx, hy]

/-- The bilinear form in quotient shape. -/
theorem dotP_elim2_eq_det3_mul_det3_div (n₁ n₂ x y : Fin 3 → ℝ)
    (hn₁ : n₁ ≠ 0) (hn₂ : perp2 n₁ n₂ ≠ 0) :
    dotP (elim2 n₁ n₂ x) (elim2 n₁ n₂ y)
      = det3 n₁ n₂ x * det3 n₁ n₂ y / wedgeSq n₁ n₂ := by
  have hw : 0 < wedgeSq n₁ n₂ := by
    have h := wedgeSq_eq_normSqP_mul_transverse hn₁ n₂
    have h1 : 0 < normSqP n₁ := normSqP_pos_of_ne_zero hn₁
    have h2 : 0 < normSqP (perp2 n₁ n₂) := normSqP_pos_of_ne_zero hn₂
    rw [h]; exact mul_pos h1 h2
  field_simp
  exact dotP_elim2_mul_wedgeSq n₁ n₂ x y

/-! ## 3. The finite Gram ledger -/

variable {κ : Type*} [DecidableEq κ]

/-- The completely signed off-diagonal Gram payment of a finite family of channels. -/
def gramDebt (n₁ n₂ : Fin 3 → ℝ) (s : Finset κ) (v : κ → Fin 3 → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s.erase i, dotP (elim2 n₁ n₂ (v i)) (elim2 n₁ n₂ (v j))

/-- **The exact finite Gram ledger.**  The surviving energy of a finite signed family
is its diagonal mass plus the signed Gram debt — an identity, with no loss. -/
theorem normSqP_elim2_sum_eq_diag_add_gramDebt (n₁ n₂ : Fin 3 → ℝ)
    (s : Finset κ) (v : κ → Fin 3 → ℝ) :
    normSqP (elim2 n₁ n₂ (∑ i ∈ s, v i))
      = (∑ i ∈ s, normSqP (elim2 n₁ n₂ (v i))) + gramDebt n₁ n₂ s v := by
  rw [elim2_sum n₁ n₂ s v]
  unfold normSqP gramDebt
  rw [dotP_sum_left, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [dotP_sum_right]
  exact (Finset.add_sum_erase s
    (fun j => dotP (elim2 n₁ n₂ (v i)) (elim2 n₁ n₂ (v j))) hi).symm

/-! ## 4. The scalar collapse -/

/-- The scalar response of one channel cell: its `3 × 3` determinant against the
nuisance pair. -/
def cellDet (n₁ n₂ : Fin 3 → ℝ) (x : Fin 3 → ℝ) : ℝ := det3 n₁ n₂ x

omit [DecidableEq κ] in
/-- **The whole finite vector problem is one scalar.**  The surviving energy of a
finite signed family is the square of the *sum of the scalar cell responses*, divided
by the Gram determinant. -/
theorem normSqP_elim2_sum_eq_sq_sum_cellDet_div (n₁ n₂ : Fin 3 → ℝ)
    (s : Finset κ) (v : κ → Fin 3 → ℝ) (hn₁ : n₁ ≠ 0) (hn₂ : perp2 n₁ n₂ ≠ 0) :
    normSqP (elim2 n₁ n₂ (∑ i ∈ s, v i))
      = (∑ i ∈ s, cellDet n₁ n₂ (v i)) ^ 2 / wedgeSq n₁ n₂ := by
  rw [normSqP_elim2_eq_det3_sq_div n₁ n₂ _ hn₁ hn₂, det3_sum_right]
  rfl

/-- The Gram debt in the same scalar coordinates: it is exactly the difference between
the square of the sum and the sum of the squares of the cell responses. -/
theorem gramDebt_eq_sq_sum_sub_sum_sq_div (n₁ n₂ : Fin 3 → ℝ)
    (s : Finset κ) (v : κ → Fin 3 → ℝ) (hn₁ : n₁ ≠ 0) (hn₂ : perp2 n₁ n₂ ≠ 0) :
    gramDebt n₁ n₂ s v
      = ((∑ i ∈ s, cellDet n₁ n₂ (v i)) ^ 2
          - ∑ i ∈ s, cellDet n₁ n₂ (v i) ^ 2) / wedgeSq n₁ n₂ := by
  have hdiag : ∑ i ∈ s, normSqP (elim2 n₁ n₂ (v i))
      = (∑ i ∈ s, cellDet n₁ n₂ (v i) ^ 2) / wedgeSq n₁ n₂ := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl
      (fun i _ => normSqP_elim2_eq_det3_sq_div n₁ n₂ (v i) hn₁ hn₂)
  have h := normSqP_elim2_sum_eq_diag_add_gramDebt n₁ n₂ s v
  rw [normSqP_elim2_sum_eq_sq_sum_cellDet_div n₁ n₂ s v hn₁ hn₂, hdiag] at h
  rw [sub_div]
  linarith

/-! ## 5. The reflection duplicate no-go -/

/-- **Equal cells pair positively.**  If two members of the finite family are literally
the same channel vector, their cross pairing is the (nonnegative) surviving energy of
that channel.  Since the stored near cell of an off-ordinate zero is already the
reflection-symmetrized response `Z_σ + Z_{Rσ}`, the members indexed by `σ` and by `Rσ`
are equal, so reflection symmetry produces a *duplicate*, never a cancellation. -/
theorem dotP_elim2_of_eq (n₁ n₂ : Fin 3 → ℝ) {x y : Fin 3 → ℝ} (hxy : x = y) :
    dotP (elim2 n₁ n₂ x) (elim2 n₁ n₂ y) = normSqP (elim2 n₁ n₂ x) := by
  rw [hxy]; rfl

theorem dotP_elim2_of_eq_nonneg (n₁ n₂ : Fin 3 → ℝ) {x y : Fin 3 → ℝ} (hxy : x = y) :
    0 ≤ dotP (elim2 n₁ n₂ x) (elim2 n₁ n₂ y) := by
  rw [dotP_elim2_of_eq n₁ n₂ hxy]
  exact normSqP_nonneg _

end ThreeTaperSchurGram
end Zeta23Bridge
