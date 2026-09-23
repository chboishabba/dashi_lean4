/-
# A1a: one *literal* uniformly nonvanishing bubble entry on the lattice symbol

`UniformGaussianFloor` reduced the uniform Gaussian floor `βZ_j ≥ b_Z` to a
single entry datum for the reduced bubble kernel

    M(q) = C(q) V(q) C(q)ᵀ,      G(q) = C(q)ᵀ C(q),

namely `|M_{ab}(q_j)| ≥ c > 0` uniformly, with `b_Z = c²/2`.  That module said
nothing about which entry, at which momentum, and left the constant `c` as an
abstract source datum.

This module computes the entry exactly for the project's **literal lattice
constrained symbol**

    G(p) = (1/p̂²)·(1 − p̂p̂ᵀ/p̂²),      p̂_μ = 2 sin(π p_μ),

and shows that the answer is a *single scalar entry of the first background
variation*, with no Brillouin-zone integral and no near/far split anywhere:

* `transverseProjector_conj_diag` — if the momentum has a vanishing component in
  direction `μ` then the transverse projector acts as the identity on that
  direction, so conjugation by it leaves the `(μ,μ)` entry untouched:
  `(P V P)_{μμ} = V_{μμ}`.
* `latticeReducedBubble_diag` — hence, exactly,

      M_{μμ}(p) = V_{μμ}(p) / p̂²        whenever p̂_μ = 0, p̂² ≠ 0.

* `phatSq_le_twelve_of_component_zero` — on such a momentum `p̂² ≤ 12`
  *unconditionally* (three surviving lattice sines, each `|p̂_ν| ≤ 2`), because
  the lattice momentum is bounded — this is where the lattice, rather than the
  continuum, does the work.  So

      |M_{μμ}(p)| ≥ |V_{μμ}(p)| / 12,

  uniformly in the momentum, the volume and the cutoff: no infrared denominator
  can spoil the bound, since the transverse direction is *not* the small one.
* `latticeBetaTrace_ge_of_diag`, `latticeUniformFloor_of_diagBound` — combining
  with the paramagnetic sign datum, `βZ_j ≥ v²/288` uniformly in `j`, where
  `v` is a uniform lower bound on the single number `|V_{μμ}(q_j)|`.
* `transverseProjector_conj_block`, `latticeBetaTrace_ge_transverseBlock` — the
  same for the *whole* block of directions transverse to the momentum, so the
  datum can be the Frobenius norm of the transverse block of `V` rather than a
  single entry.
* `cornerMomentum` and `latticeUniformFloor_corner` — at the concrete momentum
  `q = (0, 1/2, 0, 0)` (lattice momentum `π` in one direction, present on every
  even lattice at every scale) we have `p̂² = 4` exactly, so `c = |V_{00}|/4`
  and the floor sharpens to `b_Z = v²/32`; `latticeBetaTrace_corner_block` gives
  the block form there, with the three transverse directions `{0,2,3}`.

**What is proved and what is not.**  Everything above is a theorem.  What is
*not* asserted anywhere is a value for `V_{μμ}` of Bałaban's literal constrained
fluctuation operator; that single number is the remaining A1a source datum, and
this module is the statement that it is the *only* one — the momentum, the index
pair, the uniformity in scale/volume/cutoff and the constant relating it to
`b_Z` are all settled here.
-/
import RequestProject.YangMills.TransverseGram
import RequestProject.YangMills.UniformGaussianFloor

namespace YangMills

open Matrix Finset Real

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The transverse projector is the identity on a vanishing direction -/

/-- If `u μ = 0` the `μ`-th row of the transverse projector is the `μ`-th
coordinate row. -/
theorem transverseProjector_row_of_zero (u : n → ℝ) {μ : n} (hμ : u μ = 0) (a : n) :
    transverseProjector u μ a = if μ = a then 1 else 0 := by
  simp [transverseProjector, Matrix.one_apply, Matrix.vecMulVec_apply, hμ]

/-- If `u μ = 0` the `μ`-th column of the transverse projector is the `μ`-th
coordinate column. -/
theorem transverseProjector_col_of_zero (u : n → ℝ) {μ : n} (hμ : u μ = 0) (b : n) :
    transverseProjector u b μ = if b = μ then 1 else 0 := by
  simp [transverseProjector, Matrix.one_apply, Matrix.vecMulVec_apply, hμ]

/-- **Conjugation by the transverse projector does not move a transverse
diagonal entry.**  If the momentum has no component in direction `μ`, then
`(P V P)_{μμ} = V_{μμ}` for every matrix `V`. -/
theorem transverseProjector_conj_diag (u : n → ℝ) (V : Matrix n n ℝ) {μ : n}
    (hμ : u μ = 0) :
    (transverseProjector u * V * transverseProjector u) μ μ = V μ μ := by
  have hrow : ∀ a : n, transverseProjector u μ a = if μ = a then 1 else 0 :=
    fun a => transverseProjector_row_of_zero u hμ a
  have hcol : ∀ b : n, transverseProjector u b μ = if b = μ then 1 else 0 :=
    fun b => transverseProjector_col_of_zero u hμ b
  have hstep : ∀ b : n, (transverseProjector u * V) μ b = V μ b := by
    intro b
    rw [Matrix.mul_apply]
    simp [hrow]
  rw [Matrix.mul_apply]
  simp [hstep, hcol]

/-- **The whole transverse block is fixed.**  Conjugation by the transverse
projector leaves untouched every entry indexed by two directions in which the
momentum vanishes. -/
theorem transverseProjector_conj_block (u : n → ℝ) (V : Matrix n n ℝ) {mu nu : n}
    (hmu : u mu = 0) (hnu : u nu = 0) :
    (transverseProjector u * V * transverseProjector u) mu nu = V mu nu := by
  have hrow : ∀ a : n, transverseProjector u mu a = if mu = a then 1 else 0 :=
    fun a => transverseProjector_row_of_zero u hmu a
  have hcol : ∀ b : n, transverseProjector u b nu = if b = nu then 1 else 0 :=
    fun b => transverseProjector_col_of_zero u hnu b
  have hstep : ∀ b : n, (transverseProjector u * V) mu b = V mu b := by
    intro b
    rw [Matrix.mul_apply]
    simp [hrow]
  rw [Matrix.mul_apply]
  simp [hstep, hcol]

omit [DecidableEq n] in
/-- **A quantitative floor from a whole block of the reduced bubble kernel.**
Every sub-block of `M = C V Cᵀ` contributes to the Frobenius sum, so the
one-loop coefficient dominates half the block Frobenius norm. -/
theorem betaTrace_ge_block_sum {G V S C W : Matrix n n ℝ}
    (hG : G = Cᵀ * C) (hV : Vᵀ = V) (hS : S = -(Wᵀ * W)) (T : Finset n) :
    1 / 2 * ∑ a ∈ T, ∑ b ∈ T, ((C * V * Cᵀ) a b) ^ 2 ≤ betaTrace G V V S := by
  have hseag : (G * S).trace ≤ 0 := seagull_nonpos_of_negSemidef hG hS
  have hbub : (G * V * G * V).trace = ∑ x, ∑ y, ((C * V * Cᵀ) x y) ^ 2 :=
    bubble_eq_frobenius hG hV
  have hinner : ∀ a ∈ T, ∑ b ∈ T, ((C * V * Cᵀ) a b) ^ 2
      ≤ ∑ b, ((C * V * Cᵀ) a b) ^ 2 := fun a _ =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
      (fun b _ _ => sq_nonneg _)
  have hle : ∑ a ∈ T, ∑ b ∈ T, ((C * V * Cᵀ) a b) ^ 2
      ≤ ∑ a, ∑ b, ((C * V * Cᵀ) a b) ^ 2 := by
    refine le_trans (Finset.sum_le_sum hinner) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
      (fun a _ _ => Finset.sum_nonneg fun b _ => sq_nonneg _)
  rw [betaTrace, hbub]
  linarith

/-! ## Lattice bounds: the momentum square is bounded on the lattice -/

/-- **The key lattice bound.**  If one component of the lattice momentum
vanishes, the momentum square is at most `12`.  This is what makes the
transverse diagonal entry bound uniform: no infrared denominator appears. -/
theorem phatSq_le_twelve_of_component_zero (p : Fin 4 → ℝ) {μ : Fin 4}
    (hμ : phat (p μ) = 0) : phatSq p ≤ 12 := by
  have h : ∀ ν : Fin 4, (phat (p ν)) ^ 2 ≤ 4 := fun ν => phat_sq_le_four (p ν)
  have hz : (phat (p μ)) ^ 2 = 0 := by rw [hμ]; ring
  have hsplit : phatSq p
      = (phat (p μ)) ^ 2 + ∑ ν ∈ Finset.univ.erase μ, (phat (p ν)) ^ 2 := by
    rw [phatSq, ← Finset.sum_erase_add _ _ (Finset.mem_univ μ)]; ring
  have hcard : (Finset.univ.erase μ).card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ μ)]
    simp
  have hbound : ∑ ν ∈ Finset.univ.erase μ, (phat (p ν)) ^ 2 ≤ 12 := by
    calc ∑ ν ∈ Finset.univ.erase μ, (phat (p ν)) ^ 2
        ≤ ∑ _ν ∈ Finset.univ.erase μ, (4 : ℝ) :=
          Finset.sum_le_sum (fun ν _ => h ν)
      _ = 12 := by rw [Finset.sum_const, hcard]; norm_num
  rw [hsplit, hz]
  linarith

/-! ## The literal reduced bubble entry -/

section Lattice

/-- The literal lattice constrained symbol at momentum `p`. -/
noncomputable def latticeSymbolOf (p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  constrainedPropagator ((phatSq p)⁻¹ • (1 : Matrix (Fin 4) (Fin 4) ℝ))
    (rowVec (phatVec p))

/-- The Gram factor of the lattice constrained symbol, `C(p) = (p̂²)^{-1/2}·P`. -/
noncomputable def latticeGramFactor (p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Real.sqrt (phatSq p)⁻¹ • transverseProjector (phatVec p)

theorem latticeSymbol_eq_gram (p : Fin 4 → ℝ) (hp : phatSq p ≠ 0) :
    constrainedPropagator ((phatSq p)⁻¹ • (1 : Matrix (Fin 4) (Fin 4) ℝ))
        (rowVec (phatVec p))
      = (latticeGramFactor p)ᵀ * latticeGramFactor p :=
  latticeSymbol_gram p hp

/-- **The reduced bubble kernel of the lattice symbol, exactly.**
`M(p) = C(p) V C(p)ᵀ = (1/p̂²)·(P V P)`. -/
theorem latticeReducedBubble_eq (p : Fin 4 → ℝ) (hp : 0 ≤ phatSq p)
    (V : Matrix (Fin 4) (Fin 4) ℝ) :
    latticeGramFactor p * V * (latticeGramFactor p)ᵀ
      = (phatSq p)⁻¹ • (transverseProjector (phatVec p) * V
          * transverseProjector (phatVec p)) := by
  have hnn : (0:ℝ) ≤ (phatSq p)⁻¹ := inv_nonneg.mpr hp
  rw [latticeGramFactor, Matrix.transpose_smul, transverseProjector_transpose,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    Real.mul_self_sqrt hnn]

/-- **The literal entry.**  At a momentum with vanishing `μ`-component, the
`(μ,μ)` entry of the reduced bubble kernel is exactly `V_{μμ}/p̂²`. -/
theorem latticeReducedBubble_diag (p : Fin 4 → ℝ) (hp : 0 ≤ phatSq p)
    (V : Matrix (Fin 4) (Fin 4) ℝ) {μ : Fin 4} (hμ : phat (p μ) = 0) :
    (latticeGramFactor p * V * (latticeGramFactor p)ᵀ) μ μ = V μ μ / phatSq p := by
  have hz : phatVec p μ = 0 := hμ
  rw [latticeReducedBubble_eq p hp V]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [transverseProjector_conj_diag (phatVec p) V hz]
  field_simp

/-- **The uniform entry bound.**  `|M_{μμ}(p)| ≥ |V_{μμ}|/12`, uniformly over all
lattice momenta with vanishing `μ`-component — hence uniformly in the volume and
in the cutoff. -/
theorem latticeReducedBubble_diag_abs_ge (p : Fin 4 → ℝ) (hp : 0 < phatSq p)
    (V : Matrix (Fin 4) (Fin 4) ℝ) {μ : Fin 4} (hμ : phat (p μ) = 0) :
    |V μ μ| / 12 ≤ |(latticeGramFactor p * V * (latticeGramFactor p)ᵀ) μ μ| := by
  rw [latticeReducedBubble_diag p hp.le V hμ, abs_div, abs_of_pos hp]
  have h12 : phatSq p ≤ 12 := phatSq_le_twelve_of_component_zero p hμ
  exact div_le_div_of_nonneg_left (abs_nonneg _) hp h12

/-! ## From the entry to the uniform Gaussian floor -/

/-- **The Gaussian coefficient on the literal lattice symbol, bounded below by
one entry of the first background variation.**  With the paramagnetic sign datum
(`S = −WᵀW`) and a symmetric first variation, the one-loop coefficient at a
momentum transverse to `μ` obeys `β ≥ V_{μμ}²/288`. -/
theorem latticeBetaTrace_ge_of_diag (p : Fin 4 → ℝ) (hp : 0 < phatSq p)
    {μ : Fin 4} (hμ : phat (p μ) = 0)
    (V S W : Matrix (Fin 4) (Fin 4) ℝ) (hV : Vᵀ = V) (hS : S = -(Wᵀ * W)) :
    (V μ μ) ^ 2 / 288
      ≤ betaTrace (constrainedPropagator ((phatSq p)⁻¹ • (1 : Matrix (Fin 4) (Fin 4) ℝ))
          (rowVec (phatVec p))) V V S := by
  have hG := latticeSymbol_eq_gram p (ne_of_gt hp)
  have hmain := betaTrace_ge_entry_sq (G := (latticeGramFactor p)ᵀ * latticeGramFactor p)
    (V := V) (S := S) (C := latticeGramFactor p) (W := W) rfl hV hS μ μ
  rw [hG]
  refine le_trans ?_ hmain
  have hentry : (latticeGramFactor p * V * (latticeGramFactor p)ᵀ) μ μ = V μ μ / phatSq p :=
    latticeReducedBubble_diag p hp.le V hμ
  rw [hentry, div_pow]
  have h12 : phatSq p ≤ 12 := phatSq_le_twelve_of_component_zero p hμ
  have hpos : (0:ℝ) < (phatSq p) ^ 2 := by positivity
  have hsq : 2 * (phatSq p) ^ 2 ≤ 288 := by nlinarith
  have hstep : (V μ μ) ^ 2 / 288 ≤ (V μ μ) ^ 2 / (2 * (phatSq p) ^ 2) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hsq
  have heq : 1 / 2 * ((V μ μ) ^ 2 / (phatSq p) ^ 2)
      = (V μ μ) ^ 2 / (2 * (phatSq p) ^ 2) := by
    field_simp
  rw [heq]
  exact hstep

/-- **The uniform floor, scale by scale.**  A scale-indexed family of literal
lattice paramagnetic instances, each at a momentum transverse to some direction
`μ_j`, with the single number `|V_j(μ_j,μ_j)|` bounded below by `v > 0`
uniformly in the scale, has `βZ_j ≥ v²/288` uniformly.  Nothing depends on the
number of scales, the volume or the cutoff. -/
theorem latticeUniformFloor_of_diagBound
    (p : ℕ → (Fin 4 → ℝ)) (hp : ∀ j, 0 < phatSq (p j))
    (mu : ℕ → Fin 4) (hmu : ∀ j, phat (p j (mu j)) = 0)
    (V S W : ℕ → Matrix (Fin 4) (Fin 4) ℝ)
    (hV : ∀ j, (V j)ᵀ = V j) (hS : ∀ j, S j = -((W j)ᵀ * W j))
    {v : ℝ} (hv : 0 ≤ v) (hdiag : ∀ j, v ≤ |V j (mu j) (mu j)|) (j : ℕ) :
    v ^ 2 / 288
      ≤ betaTrace (constrainedPropagator ((phatSq (p j))⁻¹ • (1 : Matrix (Fin 4) (Fin 4) ℝ))
          (rowVec (phatVec (p j)))) (V j) (V j) (S j) := by
  have hmain := latticeBetaTrace_ge_of_diag (p j) (hp j) (hmu j) (V j) (S j) (W j)
    (hV j) (hS j)
  refine le_trans ?_ hmain
  have hsq : v ^ 2 ≤ (V j (mu j) (mu j)) ^ 2 := by
    have h := hdiag j
    have habs := sq_abs (V j (mu j) (mu j))
    nlinarith [abs_nonneg (V j (mu j) (mu j))]
  linarith

/-! ## The whole transverse block of the first variation -/

/-- The block form of the literal entry: for two directions transverse to the
momentum, `M_{μν}(p) = V_{μν}/p̂²`. -/
theorem latticeReducedBubble_block (p : Fin 4 → ℝ) (hp : 0 ≤ phatSq p)
    (V : Matrix (Fin 4) (Fin 4) ℝ) {mu nu : Fin 4}
    (hmu : phat (p mu) = 0) (hnu : phat (p nu) = 0) :
    (latticeGramFactor p * V * (latticeGramFactor p)ᵀ) mu nu = V mu nu / phatSq p := by
  rw [latticeReducedBubble_eq p hp V]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [transverseProjector_conj_block (phatVec p) V (mu := mu) (nu := nu) hmu hnu]
  field_simp

/-- **The Gaussian coefficient dominates the Frobenius norm of the transverse
block of the first background variation.**  For any set `T` of directions in
which the momentum vanishes,

    β ≥ (∑_{μ,ν ∈ T} V_{μν}²) / (2 (p̂²)²).

So the A1a source datum need not single out one entry: it is enough that the
transverse block of the literal first variation is not identically zero,
quantitatively and uniformly in the scale. -/
theorem latticeBetaTrace_ge_transverseBlock (p : Fin 4 → ℝ) (hp : 0 < phatSq p)
    (T : Finset (Fin 4)) (hT : ∀ mu ∈ T, phat (p mu) = 0)
    (V S W : Matrix (Fin 4) (Fin 4) ℝ) (hV : Vᵀ = V) (hS : S = -(Wᵀ * W)) :
    (∑ a ∈ T, ∑ b ∈ T, (V a b) ^ 2) / (2 * (phatSq p) ^ 2)
      ≤ betaTrace (constrainedPropagator ((phatSq p)⁻¹ • (1 : Matrix (Fin 4) (Fin 4) ℝ))
          (rowVec (phatVec p))) V V S := by
  have hG := latticeSymbol_eq_gram p (ne_of_gt hp)
  have hmain := betaTrace_ge_block_sum
    (G := (latticeGramFactor p)ᵀ * latticeGramFactor p) (V := V) (S := S)
    (C := latticeGramFactor p) (W := W) rfl hV hS T
  rw [hG]
  refine le_trans (le_of_eq ?_) hmain
  have hrewrite : ∑ a ∈ T, ∑ b ∈ T,
      ((latticeGramFactor p * V * (latticeGramFactor p)ᵀ) a b) ^ 2
      = (∑ a ∈ T, ∑ b ∈ T, (V a b) ^ 2) / (phatSq p) ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [latticeReducedBubble_block p hp.le V (hT a ha) (hT b hb), div_pow]
  rw [hrewrite]
  ring

/-! ## A concrete momentum available at every scale, volume and cutoff -/

/-- The lattice momentum `π` in direction `1`, zero in the others.  It is a
momentum of every even lattice torus, at every scale. -/
noncomputable def cornerMomentum : Fin 4 → ℝ := fun μ => if μ = 1 then 1/2 else 0

theorem phat_half : phat (1/2 : ℝ) = 2 := by
  have h : π * (1/2 : ℝ) = π / 2 := by ring
  rw [phat, sinAtom, h, Real.sin_pi_div_two]
  norm_num

theorem phat_cornerMomentum_zero : phat (cornerMomentum 0) = 0 := by
  simp [cornerMomentum]

/-- At the corner momentum the lattice momentum square is exactly `4`. -/
theorem phatSq_cornerMomentum : phatSq cornerMomentum = 4 := by
  have h0 : cornerMomentum 0 = 0 := by simp [cornerMomentum]
  have h1 : cornerMomentum 1 = 1/2 := by simp [cornerMomentum]
  have h2 : cornerMomentum 2 = 0 := by simp [cornerMomentum]
  have h3 : cornerMomentum 3 = 0 := by simp [cornerMomentum]
  simp only [phatSq, Fin.sum_univ_four, h0, h1, h2, h3, phat_zero, phat_half]
  norm_num

theorem phatSq_cornerMomentum_pos : 0 < phatSq cornerMomentum := by
  rw [phatSq_cornerMomentum]; norm_num

/-- **The sharp form at the corner momentum.**  There `p̂² = 4` exactly, so
`M_{00} = V_{00}/4` and the floor is `b_Z = v²/32`. -/
theorem latticeReducedBubble_corner (V : Matrix (Fin 4) (Fin 4) ℝ) :
    (latticeGramFactor cornerMomentum * V * (latticeGramFactor cornerMomentum)ᵀ) 0 0
      = V 0 0 / 4 := by
  rw [latticeReducedBubble_diag cornerMomentum phatSq_cornerMomentum_pos.le V
    phat_cornerMomentum_zero, phatSq_cornerMomentum]

/-- **The uniform Gaussian floor at the corner momentum.**  If the literal first
background variation of the constrained fluctuation operator has
`|V_j(0,0)| ≥ v > 0` at the corner momentum uniformly in the scale, and the
second variation is paramagnetic, then `βZ_j ≥ v²/32` uniformly in the scale,
the volume and the cutoff. -/
theorem latticeUniformFloor_corner
    (V S W : ℕ → Matrix (Fin 4) (Fin 4) ℝ)
    (hV : ∀ j, (V j)ᵀ = V j) (hS : ∀ j, S j = -((W j)ᵀ * W j))
    {v : ℝ} (hv : 0 ≤ v) (hdiag : ∀ j, v ≤ |V j 0 0|) (j : ℕ) :
    v ^ 2 / 32
      ≤ betaTrace (constrainedPropagator ((phatSq cornerMomentum)⁻¹
          • (1 : Matrix (Fin 4) (Fin 4) ℝ)) (rowVec (phatVec cornerMomentum)))
          (V j) (V j) (S j) := by
  have hG := latticeSymbol_eq_gram cornerMomentum (ne_of_gt phatSq_cornerMomentum_pos)
  have hmain := betaTrace_ge_entry_sq
    (G := (latticeGramFactor cornerMomentum)ᵀ * latticeGramFactor cornerMomentum)
    (V := V j) (S := S j) (C := latticeGramFactor cornerMomentum) (W := W j) rfl
    (hV j) (hS j) 0 0
  rw [hG]
  refine le_trans ?_ hmain
  rw [latticeReducedBubble_corner (V j)]
  have hsq : v ^ 2 ≤ (V j 0 0) ^ 2 := by
    have h := hdiag j
    have habs := sq_abs (V j 0 0)
    nlinarith [abs_nonneg (V j 0 0)]
  have hrw : (V j 0 0 / 4) ^ 2 = (V j 0 0) ^ 2 / 16 := by ring
  rw [hrw]
  linarith

/-- **The transverse block at the corner momentum.**  Three of the four
directions are transverse there, and `p̂² = 4`, so

    β ≥ (∑_{μ,ν ∈ {0,2,3}} V_{μν}²)/32.

This is the weakest form of the A1a Gaussian datum produced here. -/
theorem latticeBetaTrace_corner_block
    (V S W : Matrix (Fin 4) (Fin 4) ℝ) (hV : Vᵀ = V) (hS : S = -(Wᵀ * W)) :
    (∑ a ∈ ({0, 2, 3} : Finset (Fin 4)), ∑ b ∈ ({0, 2, 3} : Finset (Fin 4)),
        (V a b) ^ 2) / 32
      ≤ betaTrace (constrainedPropagator ((phatSq cornerMomentum)⁻¹
          • (1 : Matrix (Fin 4) (Fin 4) ℝ)) (rowVec (phatVec cornerMomentum)))
          V V S := by
  have hT : ∀ mu ∈ ({0, 2, 3} : Finset (Fin 4)), phat (cornerMomentum mu) = 0 := by
    intro mu hmu
    fin_cases hmu <;> simp [cornerMomentum]
  have h := latticeBetaTrace_ge_transverseBlock cornerMomentum phatSq_cornerMomentum_pos
    ({0, 2, 3} : Finset (Fin 4)) hT V S W hV hS
  have h32 : (2 : ℝ) * (phatSq cornerMomentum) ^ 2 = 32 := by
    rw [phatSq_cornerMomentum]; norm_num
  rwa [h32] at h

/-- **The floor in the shape consumed by `A1LiteralSource`.**  The corner-momentum
datum supplies the field `gaussianFloor` with the explicit constant
`b_Z = v²/32 > 0`. -/
theorem gaussianFloor_corner
    (V S W : ℕ → Matrix (Fin 4) (Fin 4) ℝ)
    (hV : ∀ j, (V j)ᵀ = V j) (hS : ∀ j, S j = -((W j)ᵀ * W j))
    {v : ℝ} (hv : 0 < v) (hdiag : ∀ j, v ≤ |V j 0 0|)
    (betaZ : ℕ → (ℕ → ℝ) → ℝ) (gref : ℕ → ℝ)
    (hident : ∀ j, betaZ j gref
      = betaTrace (constrainedPropagator ((phatSq cornerMomentum)⁻¹
          • (1 : Matrix (Fin 4) (Fin 4) ℝ)) (rowVec (phatVec cornerMomentum)))
          (V j) (V j) (S j)) :
    0 < v ^ 2 / 32 ∧ ∀ j, v ^ 2 / 32 ≤ betaZ j gref := by
  refine ⟨by positivity, fun j => ?_⟩
  rw [hident j]
  exact latticeUniformFloor_corner V S W hV hS hv.le hdiag j

end Lattice

/-! ## The floor for the full Brillouin sum -/

section Brillouin

variable {iota : Type*} [Fintype iota]

/-- **The uniform Gaussian floor for the literal Brillouin sum.**  If the
Gaussian part of the shell coefficient is the finite Brillouin sum of the
one-loop integrand over the lattice momenta, and the corner momentum is one of
them, then a uniform lower bound `v` on the single entry `|V_j(q₀)(0,0)|` gives
`βZ_j ≥ v²/32`.  All other momenta contribute nonnegatively because of the
paramagnetic sign, so no control of the rest of the Brillouin zone is needed. -/
theorem latticeBrillouinFloor_corner
    (p : iota → (Fin 4 → ℝ)) (hp : ∀ q, phatSq (p q) ≠ 0)
    (V S W : iota → Matrix (Fin 4) (Fin 4) ℝ)
    (hV : ∀ q, (V q)ᵀ = V q) (hS : ∀ q, S q = -((W q)ᵀ * W q))
    (q₀ : iota) (hq₀ : p q₀ = cornerMomentum) {v : ℝ} (hv : 0 ≤ v)
    (hdiag : v ≤ |V q₀ 0 0|) :
    v ^ 2 / 32
      ≤ ∑ q, brillouinIntegrand (latticeSymbolOf (p q)) (V q) (V q) (S q) := by
  have hmain := brillouinSum_ge_entry_sq
    (g := fun q => latticeSymbolOf (p q)) (v := V) (s := S)
    (C := fun q => latticeGramFactor (p q)) (W := W)
    (fun q => latticeSymbol_eq_gram (p q) (hp q)) hV hS q₀ 0 0
  refine le_trans ?_ hmain
  have hentry : (latticeGramFactor (p q₀) * V q₀ * (latticeGramFactor (p q₀))ᵀ) 0 0
      = V q₀ 0 0 / 4 := by
    rw [hq₀]; exact latticeReducedBubble_corner (V q₀)
  rw [hentry]
  have hsq : v ^ 2 ≤ (V q₀ 0 0) ^ 2 := by
    have habs := sq_abs (V q₀ 0 0)
    nlinarith [abs_nonneg (V q₀ 0 0), hdiag, hv]
  have hrw : (V q₀ 0 0 / 4) ^ 2 = (V q₀ 0 0) ^ 2 / 16 := by ring
  rw [hrw]
  linarith

end Brillouin

/-! ## Boundary tests -/

section Checks

/-- The entry identity is not vacuous: with `V` the identity the corner entry is
`1/4`, so the floor is genuinely positive. -/
theorem latticeReducedBubble_corner_one :
    (latticeGramFactor cornerMomentum * (1 : Matrix (Fin 4) (Fin 4) ℝ)
        * (latticeGramFactor cornerMomentum)ᵀ) 0 0 = 1 / 4 := by
  rw [latticeReducedBubble_corner]
  norm_num [Matrix.one_apply]

/-- The longitudinal momentum, `π` in direction `0`. -/
noncomputable def axisMomentum : Fin 4 → ℝ := fun μ => if μ = 0 then 1/2 else 0

theorem phatSq_axisMomentum : phatSq axisMomentum = 4 := by
  have h0 : axisMomentum 0 = 1/2 := by simp [axisMomentum]
  have h1 : axisMomentum 1 = 0 := by simp [axisMomentum]
  have h2 : axisMomentum 2 = 0 := by simp [axisMomentum]
  have h3 : axisMomentum 3 = 0 := by simp [axisMomentum]
  simp only [phatSq, Fin.sum_univ_four, h0, h1, h2, h3, phat_zero, phat_half]
  norm_num

/-- The transversality hypothesis is load-bearing: at a momentum with a
*nonzero* `μ`-component the conjugated entry is genuinely changed.  Here the
momentum is `π` in direction `0`, so the projector annihilates direction `0` and
the `(0,0)` entry of `P·1·P` is `0`, not `1`. -/
theorem transverseProjector_conj_diag_fails :
    (transverseProjector (phatVec axisMomentum) * (1 : Matrix (Fin 4) (Fin 4) ℝ)
        * transverseProjector (phatVec axisMomentum)) 0 0 = 0 := by
  have hu : normSqVec (phatVec axisMomentum) = 4 := by
    rw [normSqVec_phatVec]; exact phatSq_axisMomentum
  have hidem : transverseProjector (phatVec axisMomentum)
      * transverseProjector (phatVec axisMomentum)
      = transverseProjector (phatVec axisMomentum) :=
    transverseProjector_idem _ (by rw [hu]; norm_num)
  have h0 : phatVec axisMomentum 0 = 2 := by
    have : axisMomentum 0 = 1/2 := by simp [axisMomentum]
    simp only [phatVec, this, phat_half]
  rw [Matrix.mul_one, hidem, transverseProjector, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, hu, h0]
  norm_num [Matrix.one_apply]

end Checks

end YangMills
