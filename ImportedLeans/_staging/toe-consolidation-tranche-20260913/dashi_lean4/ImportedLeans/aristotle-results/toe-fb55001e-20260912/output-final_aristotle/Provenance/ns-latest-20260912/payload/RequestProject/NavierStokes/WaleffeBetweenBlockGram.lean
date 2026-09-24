/-
# The between-block Gram debt of the partner-compressed output fibre

`WaleffeOutputGainFibre.lean` compresses the fibre of the output `k` by the
shared-output involution `p ↦ k − p`: the two advective cells of a *partner
block* `{p, k−p}` assemble into `pairAdvection`, and after the Leray projection
the resulting **block cell**

  `C_p := P_k ( i(u_p·q) u_q + i(u_q·p) u_p )`,  `q = k − p`,

carries only the output frequency, `‖C_p‖ ≤ 2|k| ‖u_p‖‖u_q‖`.

The next tempting move is to sum the *squares* of the block cells over the
fibre, i.e. to hope that after partner compression the whole-fibre mass is
bounded by the sum of the cellwise masses,

  `‖∑_p C_p‖² ≤ ∑_p ‖C_p‖²`  (†)

— a cardinality-free fibre payment.  The exact finite-fibre identity contains a
signed Gram remainder, the **between-block Gram debt**

  `gramDebt = ‖∑_p C_p‖² − ∑_p ‖C_p‖² = ∑_{p ≠ p'} Re ⟪C_p, C_{p'}⟫`,

and (†) is exactly the claim that this debt is never positive.

This file settles that claim, negatively, and it does so on the *literal
physical cells* rather than on abstract Hilbert-space blocks:

* §1 gives the exact fibre Gram decomposition (`nsq_sum_herm`, `gramDebt_eq`)
  and the two-block form `gramDebt = 2 Re ⟪C_{p₁}, C_{p₂}⟫`.

* §2 exhibits an explicit configuration on the integer lattice: an output
  `k = (0,0,2)` and two distinct partner blocks
  `{(4,8,1), (−4,−8,1)}` and `{(8,4,1), (−8,−4,1)}`, all four legs of length
  exactly `9`, carrying **genuine helical (curl-eigenvector) amplitudes** with
  integer real and imaginary parts.  Every mode is divergence free, both blocks
  lie in the *same* Bony class `HH→low` with the *same* parameter `θ = 2/9`
  (`< 1/2`), both blocks have the identical helicity signature `(+9, −9)`, and
  the two legs of each block have the same length as the corresponding legs of
  the other block.  So every symbol — output frequency, leg frequencies,
  helicity eigenvalues, Bony class — coincides between the two blocks.

* §3 computes the two block cells exactly: `C₁ = (−288, 144, 0)`,
  `C₂ = (−144, 288, 0)`.  Hence

    `‖C₁‖² = ‖C₂‖² = 103680`,  `Re ⟪C₁,C₂⟫ = 82944 = (4/5)‖C₁‖‖C₂‖`,
    `gramDebt = 165888 > 0`.

  The between-block Gram entry is therefore **not** annihilated by an
  orthogonality relation, and it is not multiplied by any difference of
  symbols: all symbol differences available between these two blocks vanish
  identically, while the Gram entry sits at `4/5` of its Cauchy–Schwarz
  maximum.

* §4 states the consequences as negative theorems: (†) is false
  (`not_partnerCompressed_fibre_subadditive`), it stays false when one
  restricts to helical amplitudes inside a single Bony class
  (`not_partnerCompressed_fibre_subadditive_helical`), and no "second symbol
  difference'' can be extracted from the off-diagonal kernel
  (`between_block_gram_not_paid_by_symbols`).

Nothing here is postulated, and nothing here proves regularity: this is a
falsification.  It says that the remaining whole-fibre estimate cannot be
obtained from partner compression plus generic (or even helical, Bony-class
adapted) Hilbert-space algebra; the payment has to come from information that
distinguishes the two blocks above — their relative lattice geometry inside the
dynamics — and not from their symbols.
-/
import RequestProject.NavierStokes.WaleffeOutputGainFibre
import RequestProject.NavierStokes.WaleffeExternalBonyClasses

noncomputable section

namespace ClayNS.Waleffe

open Complex

/-! ## 1. The partner-compressed block cell and the exact fibre Gram identity -/

/-- The **partner-compressed block cell** of the block `{p, k−p}` in the fibre
of the output `k`: the Leray projection of the advective pair of the block. -/
def blockCell (u : Wave → Fin 3 → ℂ) (k p : Wave) : Fin 3 → ℂ :=
  leray k (pairAdvection p (k - p) (u p) (u (k - p)))

/-- The block cell depends only on the *block*, not on the representative. -/
theorem blockCell_partner (u : Wave → Fin 3 → ℂ) (k p : Wave) :
    blockCell u k (k - p) = blockCell u k p := by
  unfold blockCell
  have h : k - (k - p) = p := by abel
  rw [h]
  congr 1
  funext i
  simp only [pairAdvection]
  ring

/-- The **between-block Gram debt** of a family of blocks in the fibre of `k`:
the excess of the squared mass of the compressed fibre over the sum of the
cellwise squared masses. -/
def gramDebt (u : Wave → Fin 3 → ℂ) (k : Wave) (S : Finset Wave) : ℝ :=
  nsq (fun i => ∑ p ∈ S, blockCell u k p i) - ∑ p ∈ S, nsq (blockCell u k p)

theorem nsq_eq_herm_re (v : Fin 3 → ℂ) : nsq v = (herm v v).re := by
  rw [herm_self, Complex.ofReal_re]

/-- **The exact fibre Gram identity.**  The squared mass of a finite sum of
vectors is the sum of all Gram entries, diagonal and off-diagonal. -/
theorem nsq_sum_herm {ι : Type*} (S : Finset ι) (v : ι → Fin 3 → ℂ) :
    nsq (fun i => ∑ p ∈ S, v p i)
      = ∑ p ∈ S, ∑ q ∈ S, (herm (v p) (v q)).re := by
  rw [nsq_eq_herm_re, herm_sum_left]
  simp only [herm_sum_right, Complex.re_sum]

/-- The Gram debt is exactly the sum of the off-diagonal Gram entries. -/
theorem gramDebt_eq (u : Wave → Fin 3 → ℂ) (k : Wave) (S : Finset Wave) :
    gramDebt u k S
      = ∑ p ∈ S, ∑ q ∈ S.erase p, (herm (blockCell u k p) (blockCell u k q)).re := by
  classical
  unfold gramDebt
  rw [nsq_sum_herm]
  rw [← sub_eq_zero]
  have hsplit : ∀ p ∈ S, ∑ q ∈ S, (herm (blockCell u k p) (blockCell u k q)).re
      = nsq (blockCell u k p)
        + ∑ q ∈ S.erase p, (herm (blockCell u k p) (blockCell u k q)).re := by
    intro p hp
    rw [← Finset.add_sum_erase S _ hp, nsq_eq_herm_re]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  ring

/-- Two-block form of the debt: `‖C₁ + C₂‖² = ‖C₁‖² + ‖C₂‖² + 2 Re ⟪C₁,C₂⟫`. -/
theorem nsq_add_herm (a b : Fin 3 → ℂ) :
    nsq (fun i => a i + b i) = nsq a + nsq b + 2 * (herm a b).re := by
  simp [nsq, herm, Fin.sum_univ_three, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re]
  ring

theorem gramDebt_pair (u : Wave → Fin 3 → ℂ) (k : Wave) {p₁ p₂ : Wave} (h : p₁ ≠ p₂) :
    gramDebt u k {p₁, p₂} = 2 * (herm (blockCell u k p₁) (blockCell u k p₂)).re := by
  classical
  unfold gramDebt
  simp only [Finset.sum_pair h]
  rw [nsq_add_herm]
  ring

/-! ## 1b. What the off-diagonal kernel actually is

Before the counterexamples, the exact expansion the hoped-for gain would have to
come from.  On a divergence-free configuration the leg wavevectors disappear
from the compressed cell entirely (`blockCell_output_form`), so the between-block
Gram entry is a sum of four terms, each a *product* of two output symbols
`u·k` with a Gram entry of two Leray-projected leg amplitudes
(`herm_blockCell_expand`).  Neither factor is a *difference* of symbols, and the
projections `P_k u_x` of legs sitting at different wavevectors have no reason to
be orthogonal: they are just vectors in the same plane `k^⊥ ⊆ ℂ³`.  §2–§5 show
that this is not an artefact of the presentation — the gain really is absent. -/

/-- **Output normal form of the compressed block cell.**  For divergence-free
legs the block cell carries no leg wavevector: it is the Leray projection of the
two legs weighted by the *output* symbols `u_p·k` and `u_q·k`. -/
theorem blockCell_output_form (u : Wave → Fin 3 → ℂ) (k p : Wave)
    (htp : dotb (u p) (wC p) = 0) (htq : dotb (u (k - p)) (wC (k - p)) = 0) :
    blockCell u k p
      = fun i => (I * dotb (u p) (wC k)) * leray k (u (k - p)) i
          + (I * dotb (u (k - p)) (wC k)) * leray k (u p) i := by
  have hpq : p + (k - p) = k := by abel
  have hkC : (fun i => wC p i + wC (k - p) i) = wC k := funext (wC_add hpq)
  have h1 : dotb (u p) (wC k) = dotb (u p) (wC (k - p)) := by
    rw [← hkC, dotb_add_right, htp, zero_add]
  have h2 : dotb (u (k - p)) (wC k) = dotb (u (k - p)) (wC p) := by
    rw [← hkC, dotb_add_right, htq, add_zero]
  rw [blockCell, h1, h2]
  have hsplit : pairAdvection p (k - p) (u p) (u (k - p))
      = fun i => (Complex.I * dotb (u p) (wC (k - p))) * (u (k - p)) i
          + (Complex.I * dotb (u (k - p)) (wC p)) * (u p) i := rfl
  rw [hsplit, leray_add, leray_smul, leray_smul]

/-- Bilinear expansion of a Hermitian pairing of two weighted pairs. -/
theorem herm_pair_expand (c d c' d' : ℂ) (a b a' b' : Fin 3 → ℂ) :
    herm (fun i => c * a i + d * b i) (fun i => c' * a' i + d' * b' i)
      = (starRingEnd ℂ) c * c' * herm a a' + (starRingEnd ℂ) c * d' * herm a b'
        + (starRingEnd ℂ) d * c' * herm b a' + (starRingEnd ℂ) d * d' * herm b b' := by
  simp [herm, Fin.sum_univ_three, map_add, map_mul]
  ring

/-- **The between-block Gram kernel, exactly.**  Every off-diagonal entry of the
compressed fibre is a sum of four terms, each of which is a product of two
output symbols `u·k` with the Gram entry of two Leray-projected leg amplitudes.
No difference of symbols occurs anywhere in it. -/
theorem herm_blockCell_expand (u : Wave → Fin 3 → ℂ) (k p p' : Wave)
    (htp : dotb (u p) (wC p) = 0) (htq : dotb (u (k - p)) (wC (k - p)) = 0)
    (htp' : dotb (u p') (wC p') = 0) (htq' : dotb (u (k - p')) (wC (k - p')) = 0) :
    herm (blockCell u k p) (blockCell u k p')
      = (starRingEnd ℂ) (I * dotb (u p) (wC k)) * (I * dotb (u p') (wC k))
            * herm (leray k (u (k - p))) (leray k (u (k - p')))
        + (starRingEnd ℂ) (I * dotb (u p) (wC k)) * (I * dotb (u (k - p')) (wC k))
            * herm (leray k (u (k - p))) (leray k (u p'))
        + (starRingEnd ℂ) (I * dotb (u (k - p)) (wC k)) * (I * dotb (u p') (wC k))
            * herm (leray k (u p)) (leray k (u (k - p')))
        + (starRingEnd ℂ) (I * dotb (u (k - p)) (wC k)) * (I * dotb (u (k - p')) (wC k))
            * herm (leray k (u p)) (leray k (u p')) := by
  rw [blockCell_output_form u k p htp htq, blockCell_output_form u k p' htp' htq',
    herm_pair_expand]

/-! ## 2. An explicit physical helical configuration in one output fibre -/

/-- The output wavevector `k = (0,0,2)`. -/
def ceK : Wave := ![0, 0, 2]

/-- First block: `p₁ = (4,8,1)`, `q₁ = (−4,−8,1)`; both of length `9`. -/
def ceP1 : Wave := ![4, 8, 1]
def ceQ1 : Wave := ![-4, -8, 1]

/-- Second block: `p₂ = (8,4,1)`, `q₂ = (−8,−4,1)`; both of length `9`. -/
def ceP2 : Wave := ![8, 4, 1]
def ceQ2 : Wave := ![-8, -4, 1]

/-- The amplitude field.  On each of the four legs it is an exact eigenvector of
the curl (a helical mode) with integer real and imaginary parts; elsewhere it
vanishes. -/
def ceU : Wave → Fin 3 → ℂ := fun a =>
  if a = ceP1 then ![4 - 7*I, -1 + 4*I, -8 - 4*I]
  else if a = ceQ1 then ![-4 - 7*I, 1 + 4*I, -8 + 4*I]
  else if a = ceP2 then ![-1 - 4*I, 4 + 7*I, -8 + 4*I]
  else if a = ceQ2 then ![1 - 4*I, -4 + 7*I, -8 - 4*I]
  else ![0, 0, 0]

theorem ceK_sub_ceP1 : ceK - ceP1 = ceQ1 := by
  funext i; fin_cases i <;> simp [ceK, ceP1, ceQ1]

theorem ceK_sub_ceP2 : ceK - ceP2 = ceQ2 := by
  funext i; fin_cases i <;> simp [ceK, ceP2, ceQ2]

theorem ceP1_ne_ceP2 : ceP1 ≠ ceP2 := by
  intro h
  have := congrFun h 0
  simp [ceP1, ceP2] at this

theorem ceQ1_ne_ceP1 : ceQ1 ≠ ceP1 := by
  intro h
  have := congrFun h 0
  simp [ceQ1, ceP1] at this

theorem ceP2_ne_ceP1 : ceP2 ≠ ceP1 := fun h => ceP1_ne_ceP2 h.symm

theorem ceP2_ne_ceQ1 : ceP2 ≠ ceQ1 := by
  intro h
  have := congrFun h 0
  simp [ceP2, ceQ1] at this

theorem ceQ2_ne_ceP1 : ceQ2 ≠ ceP1 := by
  intro h
  have := congrFun h 0
  simp [ceQ2, ceP1] at this

theorem ceQ2_ne_ceQ1 : ceQ2 ≠ ceQ1 := by
  intro h
  have := congrFun h 0
  simp [ceQ2, ceQ1] at this

theorem ceQ2_ne_ceP2 : ceQ2 ≠ ceP2 := by
  intro h
  have := congrFun h 0
  simp [ceQ2, ceP2] at this

@[simp] theorem ceU_ceP1 : ceU ceP1 = ![4 - 7*I, -1 + 4*I, -8 - 4*I] := by
  simp [ceU]

@[simp] theorem ceU_ceQ1 : ceU ceQ1 = ![-4 - 7*I, 1 + 4*I, -8 + 4*I] := by
  simp [ceU, ceQ1_ne_ceP1]

@[simp] theorem ceU_ceP2 : ceU ceP2 = ![-1 - 4*I, 4 + 7*I, -8 + 4*I] := by
  simp [ceU, ceP2_ne_ceP1, ceP2_ne_ceQ1]

@[simp] theorem ceU_ceQ2 : ceU ceQ2 = ![1 - 4*I, -4 + 7*I, -8 - 4*I] := by
  simp [ceU, ceQ2_ne_ceP1, ceQ2_ne_ceQ1, ceQ2_ne_ceP2]

/-- **Every mode of the configuration is divergence free.** -/
theorem ceU_divFree (a : Wave) : dotb (ceU a) (wC a) = 0 := by
  unfold ceU
  split_ifs with h1 h2 h3 h4
  · subst h1
    simp [dotb, wC, ceP1, Fin.sum_univ_three, Complex.ext_iff]
    norm_num
  · subst h2
    simp [dotb, wC, ceQ1, Fin.sum_univ_three, Complex.ext_iff]
    norm_num
  · subst h3
    simp [dotb, wC, ceP2, Fin.sum_univ_three, Complex.ext_iff]
    norm_num
  · subst h4
    simp [dotb, wC, ceQ2, Fin.sum_univ_three, Complex.ext_iff]
    norm_num
  · simp [dotb, Fin.sum_univ_three]

/-! ### The four legs are exact curl eigenvectors (helical modes) -/

theorem ceU_helical_ceP1 :
    cross (wC ceP1) (ceU ceP1) = fun i => (-I) * ((9 : ℝ) : ℂ) * ceU ceP1 i := by
  rw [ceU_ceP1]
  funext i
  fin_cases i <;>
    simp [cross, crossProduct, wC, ceP1, Complex.ext_iff] <;> norm_num

theorem ceU_helical_ceQ1 :
    cross (wC ceQ1) (ceU ceQ1) = fun i => (-I) * ((-9 : ℝ) : ℂ) * ceU ceQ1 i := by
  rw [ceU_ceQ1]
  funext i
  fin_cases i <;>
    simp [cross, crossProduct, wC, ceQ1, Complex.ext_iff] <;> norm_num

theorem ceU_helical_ceP2 :
    cross (wC ceP2) (ceU ceP2) = fun i => (-I) * ((9 : ℝ) : ℂ) * ceU ceP2 i := by
  rw [ceU_ceP2]
  funext i
  fin_cases i <;>
    simp [cross, crossProduct, wC, ceP2, Complex.ext_iff] <;> norm_num

theorem ceU_helical_ceQ2 :
    cross (wC ceQ2) (ceU ceQ2) = fun i => (-I) * ((-9 : ℝ) : ℂ) * ceU ceQ2 i := by
  rw [ceU_ceQ2]
  funext i
  fin_cases i <;>
    simp [cross, crossProduct, wC, ceQ2, Complex.ext_iff] <;> norm_num

/-! ### Frequencies and Bony class -/

theorem wsq_ceK : wsq ceK = 4 := by simp [wsq, ceK, Fin.sum_univ_three]; norm_num
theorem wsq_ceP1 : wsq ceP1 = 81 := by simp [wsq, ceP1, Fin.sum_univ_three]; norm_num
theorem wsq_ceQ1 : wsq ceQ1 = 81 := by simp [wsq, ceQ1, Fin.sum_univ_three]; norm_num
theorem wsq_ceP2 : wsq ceP2 = 81 := by simp [wsq, ceP2, Fin.sum_univ_three]; norm_num
theorem wsq_ceQ2 : wsq ceQ2 = 81 := by simp [wsq, ceQ2, Fin.sum_univ_three]; norm_num

theorem wlen_ceK : wlen ceK = 2 := by
  rw [wlen, wsq_ceK]
  rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem wlen_ceP1 : wlen ceP1 = 9 := by
  rw [wlen, wsq_ceP1, show (81:ℝ) = 9^2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem wlen_ceQ1 : wlen ceQ1 = 9 := by
  rw [wlen, wsq_ceQ1, show (81:ℝ) = 9^2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem wlen_ceP2 : wlen ceP2 = 9 := by
  rw [wlen, wsq_ceP2, show (81:ℝ) = 9^2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem wlen_ceQ2 : wlen ceQ2 = 9 := by
  rw [wlen, wsq_ceQ2, show (81:ℝ) = 9^2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- Both blocks lie in the high-high-to-low Bony class with `θ = 2/9 < 1/2`. -/
theorem bonyClass_ceP1 : bonyClass (2/9) ceK ceP1 = 2 := by
  rw [bonyClass_eq_two_iff, ceK_sub_ceP1, wlen_ceK, wlen_ceP1, wlen_ceQ1]
  norm_num

theorem bonyClass_ceP2 : bonyClass (2/9) ceK ceP2 = 2 := by
  rw [bonyClass_eq_two_iff, ceK_sub_ceP2, wlen_ceK, wlen_ceP2, wlen_ceQ2]
  norm_num

/-! ## 3. The two block cells, exactly -/

theorem blockCell_ceP1 : blockCell ceU ceK ceP1 = ![-288, 144, 0] := by
  rw [blockCell, ceK_sub_ceP1, ceU_ceP1, ceU_ceQ1]
  funext i
  fin_cases i <;>
    simp [leray, pairAdvection, dotb, herm, wC, wsq, ceK, ceP1, ceQ1, Fin.sum_univ_three,
      Complex.ext_iff] <;>
    norm_num

theorem blockCell_ceP2 : blockCell ceU ceK ceP2 = ![-144, 288, 0] := by
  rw [blockCell, ceK_sub_ceP2, ceU_ceP2, ceU_ceQ2]
  funext i
  fin_cases i <;>
    simp [leray, pairAdvection, dotb, herm, wC, wsq, ceK, ceP2, ceQ2, Fin.sum_univ_three,
      Complex.ext_iff] <;>
    norm_num

theorem nsq_blockCell_ceP1 : nsq (blockCell ceU ceK ceP1) = 103680 := by
  rw [blockCell_ceP1]
  simp [nsq, Fin.sum_univ_three, Complex.normSq_apply]
  norm_num

theorem nsq_blockCell_ceP2 : nsq (blockCell ceU ceK ceP2) = 103680 := by
  rw [blockCell_ceP2]
  simp [nsq, Fin.sum_univ_three, Complex.normSq_apply]
  norm_num

/-- **The between-block Gram entry, exactly.** -/
theorem herm_blockCell_ce :
    (herm (blockCell ceU ceK ceP1) (blockCell ceU ceK ceP2)).re = 82944 := by
  rw [blockCell_ceP1, blockCell_ceP2]
  simp [herm, Fin.sum_univ_three, Complex.mul_re]
  norm_num

/-- **The debt is strictly positive.** -/
theorem gramDebt_ce : gramDebt ceU ceK {ceP1, ceP2} = 165888 := by
  rw [gramDebt_pair ceU ceK ceP1_ne_ceP2, herm_blockCell_ce]
  norm_num

theorem gramDebt_ce_pos : 0 < gramDebt ceU ceK {ceP1, ceP2} := by
  rw [gramDebt_ce]; norm_num

/-! ## 4. The debt is not even bounded by a cardinality-free constant

The two-block configuration of §2–§3 refutes the sharp form `‖∑ C‖² ≤ ∑ ‖C‖²`.
The following one-parameter family refutes *every* constant: it produces, in the
same output fibre `k = (0,0,2)`, `n` distinct partner blocks whose compressed
cells are all equal, so that the compressed fibre mass is exactly `n` times the
sum of the cellwise masses.  All amplitudes are divergence free, and the blocks
are pairwise distinct legs of the same fibre. -/

/-- The `N`-th block representative `p_N = (N, 0, 1)` in the fibre of `k = (0,0,2)`. -/
def famP (N : ℤ) : Wave := ![N, 0, 1]

/-- A divergence-free amplitude field supported on the legs `(±N, 0, 1)`, with
the positive legs normalized so that all block cells coincide. -/
def famU : Wave → Fin 3 → ℂ := fun a =>
  if a 1 = 0 ∧ a 2 = 1 then
    (if 0 < a 0 then ![1 / (a 0 : ℂ), 0, -1]
      else if a 0 < 0 then ![0, 1, 0] else ![0, 0, 0])
  else ![0, 0, 0]

theorem famP_injective : Function.Injective famP := by
  intro N M h
  have := congrFun h 0
  simpa [famP] using this

theorem famU_divFree (a : Wave) : dotb (famU a) (wC a) = 0 := by
  unfold famU
  split_ifs with h1 h2 h3
  · have ha0 : ((a 0 : ℤ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Int.cast_eq_zero]
      omega
    have ha2 : a 2 = 1 := h1.2
    simp [dotb, wC, Fin.sum_univ_three, h1.1, ha2]
    field_simp
    norm_num
  · simp [dotb, wC, Fin.sum_univ_three, h1.1]
  · simp [dotb, wC, Fin.sum_univ_three]
  · simp [dotb, wC, Fin.sum_univ_three]

theorem ceK_sub_famP (N : ℤ) : ceK - famP N = ![-N, 0, 1] := by
  funext i; fin_cases i <;> simp [ceK, famP]

theorem famU_famP {N : ℤ} (hN : 0 < N) : famU (famP N) = ![1 / (N : ℂ), 0, -1] := by
  simp [famU, famP, hN]

theorem famU_partner {N : ℤ} (hN : 0 < N) : famU ![-N, 0, 1] = ![0, 1, 0] := by
  have h1 : ¬ (N < 0) := by omega
  simp [famU, h1, hN]

/-- **Every block of the family has the same compressed cell.** -/
theorem blockCell_famP {N : ℤ} (hN : 0 < N) :
    blockCell famU ceK (famP N) = ![0, -2*I, 0] := by
  have hNe : ((N : ℤ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Int.cast_eq_zero]
    omega
  rw [blockCell, ceK_sub_famP, famU_famP hN, famU_partner hN]
  funext i
  fin_cases i <;>
    (simp [leray, pairAdvection, dotb, herm, wC, wsq, ceK, famP, Fin.sum_univ_three,
      Complex.ext_iff]
     (try field_simp)
     (try norm_num))

/-- The `n` blocks of the family, as a set of representatives. -/
def famBlocks (n : ℕ) : Finset Wave := (Finset.Icc (1 : ℤ) (n : ℤ)).image famP

theorem card_famBlocks (n : ℕ) : (famBlocks n).card = n := by
  rw [famBlocks, Finset.card_image_of_injective _ famP_injective, Int.card_Icc]
  simp

theorem sum_blockCell_famBlocks (n : ℕ) (i : Fin 3) :
    ∑ p ∈ famBlocks n, blockCell famU ceK p i = (n : ℂ) * (![0, -2*I, 0] : Fin 3 → ℂ) i := by
  rw [famBlocks, Finset.sum_image (fun a _ b _ h => famP_injective h)]
  have hcongr : ∀ N ∈ Finset.Icc (1 : ℤ) (n : ℤ),
      blockCell famU ceK (famP N) i = (![0, -2*I, 0] : Fin 3 → ℂ) i := by
    intro N hN
    have : (0 : ℤ) < N := by
      have := (Finset.mem_Icc.1 hN).1
      omega
    rw [blockCell_famP this]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Int.card_Icc]
  simp [nsmul_eq_mul]

theorem sum_nsq_blockCell_famBlocks (n : ℕ) :
    ∑ p ∈ famBlocks n, nsq (blockCell famU ceK p) = 4 * n := by
  have hcongr : ∀ p ∈ famBlocks n, nsq (blockCell famU ceK p) = 4 := by
    intro p hp
    rw [famBlocks, Finset.mem_image] at hp
    obtain ⟨N, hN, rfl⟩ := hp
    have hpos : (0 : ℤ) < N := by
      have := (Finset.mem_Icc.1 hN).1
      omega
    rw [blockCell_famP hpos]
    simp [nsq, Fin.sum_univ_three, Complex.normSq_apply]
    norm_num
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, card_famBlocks]
  simp [nsmul_eq_mul]
  ring

theorem nsq_sum_blockCell_famBlocks (n : ℕ) :
    nsq (fun i => ∑ p ∈ famBlocks n, blockCell famU ceK p i) = 4 * n ^ 2 := by
  have h : (fun i => ∑ p ∈ famBlocks n, blockCell famU ceK p i)
      = fun i => (n : ℂ) * (![0, -2*I, 0] : Fin 3 → ℂ) i := by
    funext i
    exact sum_blockCell_famBlocks n i
  rw [h]
  simp [nsq, Fin.sum_univ_three, Complex.normSq_apply]
  ring

/-- **The compressed fibre mass of the family is `n` times the sum of the
cellwise masses.**  So no constant, however large, makes the partner-compressed
fibre payment cardinality free. -/
theorem famBlocks_mass_eq_card_mul (n : ℕ) :
    nsq (fun i => ∑ p ∈ famBlocks n, blockCell famU ceK p i)
      = (famBlocks n).card * ∑ p ∈ famBlocks n, nsq (blockCell famU ceK p) := by
  rw [nsq_sum_blockCell_famBlocks, sum_nsq_blockCell_famBlocks, card_famBlocks]
  ring

theorem gramDebt_famBlocks (n : ℕ) : gramDebt famU ceK (famBlocks n) = 4 * n ^ 2 - 4 * n := by
  rw [gramDebt, nsq_sum_blockCell_famBlocks, sum_nsq_blockCell_famBlocks]

/-- The Cauchy–Schwarz bound that always holds: the compressed fibre mass is at
most the number of blocks times the sum of the cellwise masses. -/
theorem nsq_sum_blockCell_le_card_mul (u : Wave → Fin 3 → ℂ) (k : Wave) (S : Finset Wave) :
    nsq (fun i => ∑ p ∈ S, blockCell u k p i)
      ≤ S.card * ∑ p ∈ S, nsq (blockCell u k p) := by
  have h1 : nrm (fun i => ∑ p ∈ S, blockCell u k p i) ≤ ∑ p ∈ S, nrm (blockCell u k p) :=
    nrm_sum_le S _
  have h0 : 0 ≤ nrm (fun i => ∑ p ∈ S, blockCell u k p i) := nrm_nonneg _
  have h2 : (∑ p ∈ S, nrm (blockCell u k p)) ^ 2
      ≤ S.card * ∑ p ∈ S, (nrm (blockCell u k p)) ^ 2 := sq_sum_le_card_mul_sum_sq
  have h3 : nsq (fun i => ∑ p ∈ S, blockCell u k p i)
      ≤ (∑ p ∈ S, nrm (blockCell u k p)) ^ 2 := by
    rw [← nrm_sq]
    nlinarith [h0, h1]
  have h4 : ∑ p ∈ S, (nrm (blockCell u k p)) ^ 2 = ∑ p ∈ S, nsq (blockCell u k p) :=
    Finset.sum_congr rfl (fun p _ => nrm_sq _)
  rw [← h4]
  linarith

/-- **The cardinality factor is sharp.**  The general Cauchy–Schwarz bound is
attained by the family above, so the `card S` loss in the squared fibre payment
cannot be improved. -/
theorem card_factor_sharp (n : ℕ) :
    nsq (fun i => ∑ p ∈ famBlocks n, blockCell famU ceK p i)
      = (famBlocks n).card * ∑ p ∈ famBlocks n, nsq (blockCell famU ceK p) ∧
    ∀ (u : Wave → Fin 3 → ℂ) (k : Wave) (S : Finset Wave),
      nsq (fun i => ∑ p ∈ S, blockCell u k p i)
        ≤ S.card * ∑ p ∈ S, nsq (blockCell u k p) :=
  ⟨famBlocks_mass_eq_card_mul n, nsq_sum_blockCell_le_card_mul⟩

/-! ## 5. The negative theorems -/

/-- **Partner compression alone does not give a cardinality-free fibre payment.**
There is a divergence-free amplitude configuration and a pair of distinct
partner blocks in one output fibre for which the compressed fibre mass strictly
exceeds the sum of the cellwise masses. -/
theorem not_partnerCompressed_fibre_subadditive :
    ¬ ∀ (u : Wave → Fin 3 → ℂ) (k : Wave) (S : Finset Wave),
        (∀ a, dotb (u a) (wC a) = 0) → wsq k ≠ 0 →
        nsq (fun i => ∑ p ∈ S, blockCell u k p i) ≤ ∑ p ∈ S, nsq (blockCell u k p) := by
  intro h
  have hk : wsq ceK ≠ 0 := by rw [wsq_ceK]; norm_num
  have := h ceU ceK {ceP1, ceP2} ceU_divFree hk
  have hd := gramDebt_ce_pos
  unfold gramDebt at hd
  linarith

/-- **No constant makes the partner-compressed fibre payment cardinality free.**
For every constant `K` there is a divergence-free configuration and a family of
distinct partner blocks in one output fibre whose compressed mass exceeds
`K` times the sum of the cellwise masses. -/
theorem no_cardinality_free_constant :
    ∀ K : ℝ, ∃ (u : Wave → Fin 3 → ℂ) (k : Wave) (S : Finset Wave),
      (∀ a, dotb (u a) (wC a) = 0) ∧ wsq k ≠ 0 ∧
      K * ∑ p ∈ S, nsq (blockCell u k p)
        < nsq (fun i => ∑ p ∈ S, blockCell u k p i) := by
  intro K
  obtain ⟨n, hn⟩ := exists_nat_gt (max K 1)
  refine ⟨famU, ceK, famBlocks n, famU_divFree, by rw [wsq_ceK]; norm_num, ?_⟩
  rw [nsq_sum_blockCell_famBlocks, sum_nsq_blockCell_famBlocks]
  have hK : K < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have h1 : (1 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  nlinarith [h1, hK]

/-- The same failure, with every extra structural hypothesis the Bony/helical
route could ask for: all four legs are exact curl eigenvectors, all four legs
have the same length `9`, the two blocks have the same helicity signature
`(+9, −9)`, and both blocks lie in the same Bony class `HH→low` with the same
`θ = 2/9 < 1/2`. -/
theorem not_partnerCompressed_fibre_subadditive_helical :
    ∃ (u : Wave → Fin 3 → ℂ) (k p₁ p₂ : Wave),
      (∀ a, dotb (u a) (wC a) = 0) ∧ wsq k ≠ 0 ∧ p₁ ≠ p₂ ∧
      wlen p₁ = wlen p₂ ∧ wlen (k - p₁) = wlen (k - p₂) ∧
      cross (wC p₁) (u p₁) = (fun i => (-I) * ((9 : ℝ) : ℂ) * u p₁ i) ∧
      cross (wC p₂) (u p₂) = (fun i => (-I) * ((9 : ℝ) : ℂ) * u p₂ i) ∧
      cross (wC (k - p₁)) (u (k - p₁))
        = (fun i => (-I) * ((-9 : ℝ) : ℂ) * u (k - p₁) i) ∧
      cross (wC (k - p₂)) (u (k - p₂))
        = (fun i => (-I) * ((-9 : ℝ) : ℂ) * u (k - p₂) i) ∧
      bonyClass (2/9) k p₁ = 2 ∧ bonyClass (2/9) k p₂ = 2 ∧
      ∑ p ∈ ({p₁, p₂} : Finset Wave), nsq (blockCell u k p)
        < nsq (fun i => ∑ p ∈ ({p₁, p₂} : Finset Wave), blockCell u k p i) := by
  refine ⟨ceU, ceK, ceP1, ceP2, ceU_divFree, by rw [wsq_ceK]; norm_num, ceP1_ne_ceP2,
    by rw [wlen_ceP1, wlen_ceP2], ?_, ceU_helical_ceP1, ceU_helical_ceP2, ?_, ?_,
    bonyClass_ceP1, bonyClass_ceP2, ?_⟩
  · rw [ceK_sub_ceP1, ceK_sub_ceP2, wlen_ceQ1, wlen_ceQ2]
  · rw [ceK_sub_ceP1]; exact ceU_helical_ceQ1
  · rw [ceK_sub_ceP2]; exact ceU_helical_ceQ2
  · have hd := gramDebt_ce_pos
    unfold gramDebt at hd
    linarith

/-- **No orthogonality relation, and no second symbol difference.**  For the two
blocks above every available symbol difference vanishes — same output, same leg
lengths, same helicity eigenvalues, same Bony class — yet the between-block Gram
entry is positive and sits at exactly `4/5` of its Cauchy–Schwarz maximum:

  `25 · (Re ⟪C₁,C₂⟫)² = 16 · ‖C₁‖² ‖C₂‖²`.

So the off-diagonal kernel of the compressed fibre carries no gain factor that
could be produced by a difference of symbols. -/
theorem between_block_gram_not_paid_by_symbols :
    0 < (herm (blockCell ceU ceK ceP1) (blockCell ceU ceK ceP2)).re ∧
      25 * ((herm (blockCell ceU ceK ceP1) (blockCell ceU ceK ceP2)).re) ^ 2
        = 16 * (nsq (blockCell ceU ceK ceP1) * nsq (blockCell ceU ceK ceP2)) := by
  constructor
  · rw [herm_blockCell_ce]; norm_num
  · rw [herm_blockCell_ce, nsq_blockCell_ceP1, nsq_blockCell_ceP2]; norm_num

/-! ## 6. The counterexamples are real velocity fields

The configurations above are divergence-free amplitude configurations, which is
all the refuted propositions are about.  They are however also *realizable by
honest real-valued periodic velocity fields*: adding the conjugate mode at `-a`
to every mode restores the Hermitian symmetry `u(-a) = conj u(a)` without
changing a single cell of the fibre of `k = (0,0,2)`, because the reflected
legs sit at third coordinate `-1` and their partners under `p ↦ k - p` are not
occupied. -/

/-- The Hermitian (reality) completion of an amplitude configuration. -/
def realify (u : Wave → Fin 3 → ℂ) : Wave → Fin 3 → ℂ :=
  fun a i => u a i + (starRingEnd ℂ) (u (-a) i)

/-- The completion satisfies the reality condition of a real velocity field. -/
theorem realify_hermitian (u : Wave → Fin 3 → ℂ) (a : Wave) :
    realify u (-a) = fun i => (starRingEnd ℂ) (realify u a i) := by
  funext i
  simp [realify, neg_neg, add_comm]

/-- The completion of a divergence-free configuration is divergence free. -/
theorem realify_divFree {u : Wave → Fin 3 → ℂ} (h : ∀ a, dotb (u a) (wC a) = 0) (a : Wave) :
    dotb (realify u a) (wC a) = 0 := by
  have hsplit : dotb (realify u a) (wC a)
      = dotb (u a) (wC a) + dotb (fun i => (starRingEnd ℂ) (u (-a) i)) (wC a) := by
    simp [dotb, realify, add_mul, Finset.sum_add_distrib]
  have h2 : (starRingEnd ℂ) (dotb (u (-a)) (wC (-a))) = 0 := by rw [h (-a), map_zero]
  simp only [dotb, map_sum, map_mul, wC, Pi.neg_apply, Int.cast_neg, map_neg, map_intCast,
    mul_neg, Finset.sum_neg_distrib, neg_eq_zero] at h2
  rw [hsplit, h a, zero_add]
  simpa [dotb, wC] using h2

/-- Where the reflected mode is unoccupied, the completion changes nothing. -/
theorem realify_apply_of_neg_zero {u : Wave → Fin 3 → ℂ} {a : Wave}
    (h : u (-a) = fun _ => 0) : realify u a = u a := by
  funext i
  simp [realify, h]

/-- The block cell only sees the two legs of its own block. -/
theorem blockCell_congr {u v : Wave → Fin 3 → ℂ} {k p : Wave}
    (h1 : u p = v p) (h2 : u (k - p) = v (k - p)) : blockCell u k p = blockCell v k p := by
  rw [blockCell, blockCell, h1, h2]

theorem ceU_eq_zero_of_third {a : Wave} (h : a 2 = -1) : ceU a = fun _ => 0 := by
  have hp1 : a ≠ ceP1 := by intro he; rw [he] at h; simp [ceP1] at h
  have hq1 : a ≠ ceQ1 := by intro he; rw [he] at h; simp [ceQ1] at h
  have hp2 : a ≠ ceP2 := by intro he; rw [he] at h; simp [ceP2] at h
  have hq2 : a ≠ ceQ2 := by intro he; rw [he] at h; simp [ceQ2] at h
  funext i
  fin_cases i <;> simp [ceU, hp1, hq1, hp2, hq2]

theorem famU_eq_zero_of_third {a : Wave} (h : a 2 = -1) : famU a = fun _ => 0 := by
  have h1 : ¬ (a 1 = 0 ∧ a 2 = 1) := by
    rintro ⟨-, h2⟩
    rw [h] at h2
    exact absurd h2 (by decide)
  funext i
  fin_cases i <;> simp [famU, h1]

theorem realify_ceU_ceP1 : realify ceU ceP1 = ceU ceP1 :=
  realify_apply_of_neg_zero (ceU_eq_zero_of_third (by simp [ceP1]))

theorem realify_ceU_ceQ1 : realify ceU ceQ1 = ceU ceQ1 :=
  realify_apply_of_neg_zero (ceU_eq_zero_of_third (by simp [ceQ1]))

theorem realify_ceU_ceP2 : realify ceU ceP2 = ceU ceP2 :=
  realify_apply_of_neg_zero (ceU_eq_zero_of_third (by simp [ceP2]))

theorem realify_ceU_ceQ2 : realify ceU ceQ2 = ceU ceQ2 :=
  realify_apply_of_neg_zero (ceU_eq_zero_of_third (by simp [ceQ2]))

theorem blockCell_realify_ceP1 : blockCell (realify ceU) ceK ceP1 = ![-288, 144, 0] := by
  have e2 : realify ceU (ceK - ceP1) = ceU (ceK - ceP1) := by
    rw [ceK_sub_ceP1]; exact realify_ceU_ceQ1
  have h : blockCell (realify ceU) ceK ceP1 = blockCell ceU ceK ceP1 :=
    blockCell_congr realify_ceU_ceP1 e2
  rw [h, blockCell_ceP1]

theorem blockCell_realify_ceP2 : blockCell (realify ceU) ceK ceP2 = ![-144, 288, 0] := by
  have e2 : realify ceU (ceK - ceP2) = ceU (ceK - ceP2) := by
    rw [ceK_sub_ceP2]; exact realify_ceU_ceQ2
  have h : blockCell (realify ceU) ceK ceP2 = blockCell ceU ceK ceP2 :=
    blockCell_congr realify_ceU_ceP2 e2
  rw [h, blockCell_ceP2]

theorem blockCell_realify_famP {N : ℤ} (hN : 0 < N) :
    blockCell (realify famU) ceK (famP N) = ![0, -2*I, 0] := by
  have e1 : realify famU (famP N) = famU (famP N) :=
    realify_apply_of_neg_zero (famU_eq_zero_of_third (a := -famP N) (by simp [famP]))
  have e2 : realify famU (ceK - famP N) = famU (ceK - famP N) :=
    realify_apply_of_neg_zero
      (famU_eq_zero_of_third (a := -(ceK - famP N)) (by simp [ceK, famP]))
  have h : blockCell (realify famU) ceK (famP N) = blockCell famU ceK (famP N) :=
    blockCell_congr e1 e2
  rw [h, blockCell_famP hN]

theorem blockCell_realify_famBlocks (n : ℕ) :
    ∀ p ∈ famBlocks n, blockCell (realify famU) ceK p = blockCell famU ceK p := by
  intro p hp
  rw [famBlocks, Finset.mem_image] at hp
  obtain ⟨N, hN, rfl⟩ := hp
  have hpos : (0 : ℤ) < N := by
    have := (Finset.mem_Icc.1 hN).1
    omega
  rw [blockCell_realify_famP hpos, blockCell_famP hpos]

/-- **The failure of the squared fibre payment survives the reality condition.**
Even for genuinely real-valued periodic velocity fields — `u(-a) = conj u(a)`,
divergence free — no constant makes the partner-compressed fibre payment
cardinality free. -/
theorem no_cardinality_free_constant_real :
    ∀ K : ℝ, ∃ (u : Wave → Fin 3 → ℂ) (k : Wave) (S : Finset Wave),
      (∀ a, dotb (u a) (wC a) = 0) ∧
      (∀ a, u (-a) = fun i => (starRingEnd ℂ) (u a i)) ∧ wsq k ≠ 0 ∧
      K * ∑ p ∈ S, nsq (blockCell u k p)
        < nsq (fun i => ∑ p ∈ S, blockCell u k p i) := by
  intro K
  obtain ⟨n, hn⟩ := exists_nat_gt (max K 1)
  refine ⟨realify famU, ceK, famBlocks n, realify_divFree famU_divFree,
    realify_hermitian famU, by rw [wsq_ceK]; norm_num, ?_⟩
  have hsum : ∀ i, ∑ p ∈ famBlocks n, blockCell (realify famU) ceK p i
      = ∑ p ∈ famBlocks n, blockCell famU ceK p i := by
    intro i
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [blockCell_realify_famBlocks n p hp]
  have hnsq : ∑ p ∈ famBlocks n, nsq (blockCell (realify famU) ceK p)
      = ∑ p ∈ famBlocks n, nsq (blockCell famU ceK p) :=
    Finset.sum_congr rfl (fun p hp => by rw [blockCell_realify_famBlocks n p hp])
  have hfun : (fun i => ∑ p ∈ famBlocks n, blockCell (realify famU) ceK p i)
      = fun i => ∑ p ∈ famBlocks n, blockCell famU ceK p i := funext hsum
  rw [hnsq, hfun, nsq_sum_blockCell_famBlocks, sum_nsq_blockCell_famBlocks]
  have hK : K < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have h1 : (1 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  nlinarith [h1, hK]

/-- The helical two-block obstruction also survives the reality condition: the
between-block Gram entry of a real, divergence-free field whose two blocks agree
in every symbol is still `4/5` of its Cauchy–Schwarz maximum. -/
theorem between_block_gram_not_paid_by_symbols_real :
    (∀ a, dotb (realify ceU a) (wC a) = 0) ∧
    (∀ a, realify ceU (-a) = fun i => (starRingEnd ℂ) (realify ceU a i)) ∧
    0 < (herm (blockCell (realify ceU) ceK ceP1) (blockCell (realify ceU) ceK ceP2)).re ∧
    25 * ((herm (blockCell (realify ceU) ceK ceP1)
            (blockCell (realify ceU) ceK ceP2)).re) ^ 2
      = 16 * (nsq (blockCell (realify ceU) ceK ceP1)
          * nsq (blockCell (realify ceU) ceK ceP2)) := by
  refine ⟨realify_divFree ceU_divFree, realify_hermitian ceU, ?_, ?_⟩
  · rw [blockCell_realify_ceP1, blockCell_realify_ceP2, ← blockCell_ceP1, ← blockCell_ceP2,
      herm_blockCell_ce]
    norm_num
  · rw [blockCell_realify_ceP1, blockCell_realify_ceP2, ← blockCell_ceP1, ← blockCell_ceP2,
      herm_blockCell_ce, nsq_blockCell_ceP1, nsq_blockCell_ceP2]
    norm_num

end ClayNS.Waleffe
