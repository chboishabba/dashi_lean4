/-
# Row A1a — the literal Wilson vertex seen through the constrained propagator

The Gaussian sector of the shell coefficient is a *one-loop trace*
`betaTrace G V V S = ½Tr(GVGV) − ½Tr(GS)` in which the propagator `G` is the
**constrained** lattice symbol.  `TransverseSymbol.constrainedPropagator_rankOne`
computes that symbol in closed form: with the scalar Wilson propagator
`(p̂²)⁻¹·1` and the single (longitudinal) constraint `p̂ᵀ`,

    G(p) = (p̂²)⁻¹ · P(p),      P(p) = 1 − p̂ p̂ᵀ / p̂².

So the object that actually enters the bubble is not the first variation `V`
itself but its **transverse conjugate** `P V P`.  This file computes that
conjugate for the literal source objects, and the answer is a lattice Ward
identity.

* `wilsonCubicBgZero_eq` : the literal Wilson cubic vertex at zero background
  momentum, in closed form,

      W_{αβ;ρ}(x) = δ_{αβ} sin(2πx_ρ)
                    − (cos(πx_ρ)/2)·(δ_{βρ} p̂_α + δ_{αρ} p̂_β).

  Everything except the first term is a rank-one term with a factor `p̂`.
* `transverseProjector_conj_wilsonBgZeroMatrix` : hence

      P W P = sin(2πx_ρ) · P,

  because `P p̂ = 0`.  This is the lattice Ward identity
  `Γ_{αβρ}(k,−k,0) = ∂_ρ D⁻¹_{αβ}(k)` seen through the transverse projector: the
  whole vertex collapses onto the derivative `∂_ρ p̂² = 2 sin(2πx_ρ)` of the
  Wilson inverse propagator (in this normalisation, `sin(2πx_ρ)`).
* `transverseProjector_conj_gaugeVariationMatrix` : the gauge-projection
  variation is annihilated outright, `P R_gauge P = 0`, since every one of its
  terms carries a factor `p̂` in each index.
* `transverseProjector_conj_diagonal_entry` : a Lorentz-diagonal contribution
  (this is the shape of the averaging variation `Q` and of the constrained part
  of `R`, by `AveragingLorentzDiagonal` and `LorentzBlockDiagonal`) contributes
  `∑_k P_{ik}² D_{kk}` to a diagonal entry, hence at most `d·P_{ii}` in modulus
  if `|D_{kk}| ≤ d`.

The consequence, `transverseConjugate_diag_ge`, is the honest replacement for the
mixed-component estimate: the diagonal entry of the transverse conjugate obeys

    (P V P)_{ii} ≥ P_{ii} · (sin(2πx_ρ) − d).

Note what this says about the *mixed* component the earlier route used: by the
Ward identity `P V P` has **no** independent mixed component — it is a multiple
of the projector — and that multiple vanishes at `x_ρ = 0`, which is exactly
where the mixed-component patch of `MixedComponentPatch` lives.  The literal
one-loop integrand therefore cannot be bounded below there; see
`A1WardAssembly` for the formal refutation and for the patch that replaces it.
-/
import RequestProject.YangMills.MixedComponentPatch
import RequestProject.YangMills.TransverseBubbleEntry

namespace YangMills

open Real Matrix Finset

/-! ## 1. Conjugation of a rank-one matrix by a symmetric matrix -/

theorem symm_conj_vecMulVec {n : Type*} [Fintype n] {P : Matrix n n ℝ} (hP : Pᵀ = P)
    (a b : n → ℝ) :
    P * Matrix.vecMulVec a b * P
      = Matrix.vecMulVec (P.mulVec a) (P.mulVec b) := by
  ext i j
  have hPji : ∀ l, P l j = P j l := fun l => by
    have := congrFun (congrFun hP j) l
    simpa using this
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct]
  calc ∑ l, (∑ k, P i k * (a k * b l)) * P l j
      = ∑ l, (∑ k, P i k * a k) * (b l * P l j) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_mul]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => by ring
    _ = (∑ k, P i k * a k) * ∑ l, P j l * b l := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => by rw [hPji l]; ring
    _ = (∑ k, P i k * a k) * ∑ l, P j l * b l := rfl

theorem vecMulVec_transpose_swap {n m : Type*} (a : n → ℝ) (b : m → ℝ) :
    (Matrix.vecMulVec a b)ᵀ = Matrix.vecMulVec b a := by
  ext i j; simp [Matrix.vecMulVec_apply, mul_comm]

theorem vecMulVec_zero_left {n : Type*} (b : n → ℝ) :
    Matrix.vecMulVec (0 : n → ℝ) b = 0 := by
  ext i j; simp [Matrix.vecMulVec_apply]

theorem vecMulVec_zero_right {n : Type*} (a : n → ℝ) :
    Matrix.vecMulVec a (0 : n → ℝ) = 0 := by
  ext i j; simp [Matrix.vecMulVec_apply]

/-- Conjugating a rank-one matrix one of whose legs is annihilated by the
projector gives zero. -/
theorem symm_conj_vecMulVec_eq_zero {n : Type*} [Fintype n] {P : Matrix n n ℝ}
    (hP : Pᵀ = P) {a b : n → ℝ} (h : P.mulVec a = 0 ∨ P.mulVec b = 0) :
    P * Matrix.vecMulVec a b * P = 0 := by
  rw [symm_conj_vecMulVec hP]
  rcases h with h | h
  · rw [h, vecMulVec_zero_left]
  · rw [h, vecMulVec_zero_right]

/-! ## 2. The literal Wilson cubic vertex in closed form -/

/-- The `ρ`-th coordinate covector. -/
def basisVec (rho : Fin 4) : Fin 4 → ℝ := fun mu => if mu = rho then 1 else 0

/-- **The literal Wilson cubic vertex at zero background momentum.**  Writing
`p̂_μ = 2 sin(π x_μ)` for the lattice momentum,

    W_{αβ;ρ}(x) = δ_{αβ} sin(2πx_ρ) − (cos(πx_ρ)/2)(δ_{βρ} p̂_α + δ_{αρ} p̂_β). -/
theorem wilsonCubicBgZero_eq (x : Fin 4 → ℝ) (al be rho : Fin 4) :
    wilsonCubicBgZero x al be rho
      = (if al = be then sinAtom (2 * x rho) else 0)
        - Real.cos (π * x rho) / 2 *
            ((if be = rho then phat (x al) else 0) + (if al = rho then phat (x be) else 0)) := by
  have h1 : π * (x rho - -x rho) = π * (2 * x rho) := by ring
  have h2 : π * (-x al - 0) = -(π * x al) := by ring
  have h3 : π * (0 - x be) = -(π * x be) := by ring
  have h4 : π * -x rho = -(π * x rho) := by ring
  simp only [wilsonCubicBgZero, wilsonCubic, h1, h2, h3, h4, Real.sin_neg, Real.cos_neg,
    sinAtom, phat]
  split_ifs <;> subst_vars <;> simp_all <;> ring

/-- The first background variation of the Wilson Hessian as a Lorentz matrix. -/
noncomputable def wilsonBgZeroMatrix (x : Fin 4 → ℝ) (rho : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun al be => wilsonCubicBgZero x al be rho

/-- The matrix form of `wilsonCubicBgZero_eq`: a multiple of the identity plus a
rank-one term whose legs are the lattice momentum. -/
theorem wilsonBgZeroMatrix_eq (x : Fin 4 → ℝ) (rho : Fin 4) :
    wilsonBgZeroMatrix x rho
      = sinAtom (2 * x rho) • (1 : Matrix (Fin 4) (Fin 4) ℝ)
        - (Real.cos (π * x rho) / 2) •
            (Matrix.vecMulVec (phatVec x) (basisVec rho)
              + Matrix.vecMulVec (basisVec rho) (phatVec x)) := by
  ext al be
  simp only [wilsonBgZeroMatrix, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.add_apply, Matrix.vecMulVec_apply, smul_eq_mul, basisVec,
    phatVec]
  rw [wilsonCubicBgZero_eq]
  by_cases hbr : be = rho <;> by_cases har : al = rho <;> simp [hbr, har]

/-- **The lattice Ward identity through the transverse projector.**  Because
`P p̂ = 0`, the whole rank-one part of the Wilson vertex is annihilated and

    P W P = sin(2πx_ρ) · P. -/
theorem transverseProjector_conj_wilsonBgZeroMatrix (x : Fin 4 → ℝ) (rho : Fin 4)
    (hx : phatSq x ≠ 0) :
    transverseProjector (phatVec x) * wilsonBgZeroMatrix x rho
        * transverseProjector (phatVec x)
      = sinAtom (2 * x rho) • transverseProjector (phatVec x) := by
  have hnorm : normSqVec (phatVec x) ≠ 0 := by rwa [normSqVec_phatVec]
  have hP : (transverseProjector (phatVec x))ᵀ = transverseProjector (phatVec x) :=
    transverseProjector_transpose _
  have hk : (transverseProjector (phatVec x)).mulVec (phatVec x) = 0 :=
    transverseProjector_mulVec_self _ hnorm
  rw [wilsonBgZeroMatrix_eq]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    transverseProjector_idem _ hnorm]
  have hzero : transverseProjector (phatVec x) *
      ((Real.cos (π * x rho) / 2) •
        (Matrix.vecMulVec (phatVec x) (basisVec rho)
          + Matrix.vecMulVec (basisVec rho) (phatVec x)))
      * transverseProjector (phatVec x) = 0 := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
      symm_conj_vecMulVec_eq_zero hP (Or.inl hk),
      symm_conj_vecMulVec_eq_zero hP (Or.inr hk), add_zero, smul_zero]
  rw [hzero, sub_zero]

/-! ## 3. The gauge-projection variation is annihilated outright -/

/-- The gauge-projection variation as a Lorentz matrix. -/
noncomputable def gaugeVariationMatrix (f : ℝ) (k : Fin 4 → ℝ) (rho : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun al be => gaugeVariationSymbol f k rho al be

/-- Every term of the gauge-projection variation carries a factor `k` in each
index: it is a combination of `e_ρ kᵀ + k e_ρᵀ` and `k kᵀ`. -/
theorem gaugeVariationMatrix_eq (f : ℝ) (k : Fin 4 → ℝ) (rho : Fin 4) :
    gaugeVariationMatrix f k rho
      = (f / (∑ ga : Fin 4, (k ga) ^ 2)) •
          (Matrix.vecMulVec (basisVec rho) k + Matrix.vecMulVec k (basisVec rho))
        - (2 * f * k rho / (∑ ga : Fin 4, (k ga) ^ 2) ^ 2) • Matrix.vecMulVec k k := by
  ext al be
  simp only [gaugeVariationMatrix, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.add_apply, Matrix.vecMulVec_apply, smul_eq_mul, basisVec]
  rw [gaugeVariationSymbol_eq]
  by_cases har : al = rho <;> by_cases hbr : be = rho <;> simp [har, hbr] <;> ring

/-- **`P R_gauge P = 0`.**  The longitudinal gauge-projection variation does not
survive the transverse conjugation at all. -/
theorem transverseProjector_conj_gaugeVariationMatrix (f : ℝ) (x : Fin 4 → ℝ) (rho : Fin 4)
    (hx : phatSq x ≠ 0) :
    transverseProjector (phatVec x) * gaugeVariationMatrix f (phatVec x) rho
        * transverseProjector (phatVec x) = 0 := by
  have hnorm : normSqVec (phatVec x) ≠ 0 := by rwa [normSqVec_phatVec]
  have hP : (transverseProjector (phatVec x))ᵀ = transverseProjector (phatVec x) :=
    transverseProjector_transpose _
  have hk : (transverseProjector (phatVec x)).mulVec (phatVec x) = 0 :=
    transverseProjector_mulVec_self _ hnorm
  rw [gaugeVariationMatrix_eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.add_mul, symm_conj_vecMulVec_eq_zero hP (Or.inr hk),
    symm_conj_vecMulVec_eq_zero hP (Or.inl hk), add_zero, smul_zero,
    Matrix.mul_smul, Matrix.smul_mul, symm_conj_vecMulVec_eq_zero hP (Or.inl hk),
    smul_zero, sub_zero]

/-! ## 4. A Lorentz-diagonal contribution -/

/-- A diagonal matrix contributes `∑_k P_{ik}² D_{kk}` to the `(i,i)` entry of
the transverse conjugate. -/
theorem symm_conj_diagonal_entry {n : Type*} [Fintype n] {P D : Matrix n n ℝ} (hP : Pᵀ = P)
    (hD : ∀ a b, a ≠ b → D a b = 0) (i : n) :
    (P * D * P) i i = ∑ k, (P i k) ^ 2 * D k k := by
  have hPji : ∀ l, P l i = P i l := fun l => by
    have := congrFun (congrFun hP i) l
    simpa using this
  simp only [Matrix.mul_apply]
  calc ∑ l, (∑ k, P i k * D k l) * P l i
      = ∑ l, (P i l * D l l) * P l i := by
        refine Finset.sum_congr rfl fun l _ => ?_
        congr 1
        refine Finset.sum_eq_single l (fun k _ hk => by rw [hD k l hk, mul_zero]) ?_
        intro h; exact absurd (Finset.mem_univ l) h
    _ = ∑ k, (P i k) ^ 2 * D k k := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hPji l]; ring

/-- The sum of squares of a row of a symmetric idempotent matrix is the diagonal
entry. -/
theorem symm_idem_row_sq_sum {n : Type*} [Fintype n] {P : Matrix n n ℝ} (hP : Pᵀ = P)
    (hidem : P * P = P) (i : n) : ∑ k, (P i k) ^ 2 = P i i := by
  have hPji : ∀ l, P l i = P i l := fun l => by
    have := congrFun (congrFun hP i) l
    simpa using this
  have := congrFun (congrFun hidem i) i
  rw [Matrix.mul_apply] at this
  rw [← this]
  exact Finset.sum_congr rfl fun k _ => by rw [hPji k]; ring

/-- **The diagonal contribution is bounded by `d·P_{ii}`.** -/
theorem abs_symm_conj_diagonal_entry_le {n : Type*} [Fintype n] {P D : Matrix n n ℝ}
    (hP : Pᵀ = P) (hidem : P * P = P) (hD : ∀ a b, a ≠ b → D a b = 0)
    {d : ℝ} (hd : ∀ a, |D a a| ≤ d) (i : n) :
    |(P * D * P) i i| ≤ d * P i i := by
  rw [symm_conj_diagonal_entry hP hD i]
  calc |∑ k, (P i k) ^ 2 * D k k| ≤ ∑ k, |(P i k) ^ 2 * D k k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, (P i k) ^ 2 * d := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        exact mul_le_mul_of_nonneg_left (hd k) (sq_nonneg _)
    _ = d * P i i := by rw [← Finset.sum_mul, symm_idem_row_sq_sum hP hidem i]; ring

/-! ## 5. The diagonal entry of the transverse conjugate -/

/-- **The honest lower bound for the one-loop entry.**  For the literal first
variation `V = W + Q + R_constr + R_gauge` at zero background momentum, where
`Q + R_constr` is Lorentz diagonal with entries bounded by `d`,

    (P V P)_{ii} ≥ P_{ii} · (sin(2πx_ρ) − d).

The Wilson piece contributes through the Ward identity, the gauge piece not at
all, and the diagonal pieces are paid for by `d`. -/
theorem transverseConjugate_diag_ge {x : Fin 4 → ℝ} (hx : phatSq x ≠ 0) (rho : Fin 4)
    {f d : ℝ} {D : Matrix (Fin 4) (Fin 4) ℝ}
    (hD : ∀ a b, a ≠ b → D a b = 0) (hd : ∀ a, |D a a| ≤ d) (i : Fin 4) :
    (transverseProjector (phatVec x)) i i * (sinAtom (2 * x rho) - d)
      ≤ (transverseProjector (phatVec x) *
          (wilsonBgZeroMatrix x rho + gaugeVariationMatrix f (phatVec x) rho + D)
          * transverseProjector (phatVec x)) i i := by
  have hnorm : normSqVec (phatVec x) ≠ 0 := by rwa [normSqVec_phatVec]
  have hP : (transverseProjector (phatVec x))ᵀ = transverseProjector (phatVec x) :=
    transverseProjector_transpose _
  have hidem : transverseProjector (phatVec x) * transverseProjector (phatVec x)
      = transverseProjector (phatVec x) := transverseProjector_idem _ hnorm
  set P := transverseProjector (phatVec x) with hPdef
  have hsplit : P * (wilsonBgZeroMatrix x rho + gaugeVariationMatrix f (phatVec x) rho + D) * P
      = (P * wilsonBgZeroMatrix x rho * P) + (P * gaugeVariationMatrix f (phatVec x) rho * P)
        + (P * D * P) := by
    simp only [Matrix.mul_add, Matrix.add_mul]
  rw [hsplit]
  simp only [Matrix.add_apply]
  rw [transverseProjector_conj_wilsonBgZeroMatrix x rho hx,
    transverseProjector_conj_gaugeVariationMatrix f x rho hx]
  simp only [Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul, add_zero]
  have hbound := abs_symm_conj_diagonal_entry_le hP hidem hD hd i
  have hneg : -(d * P i i) ≤ (P * D * P) i i := neg_le_of_abs_le hbound
  nlinarith [hbound]

end YangMills
