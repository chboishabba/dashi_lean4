/-
The literal pairwise expansion of the finite zero-side Frobenius square, and
the two candidate defect observables.

`FrobeniusDecomposition.lean` splits `‖A‖_F²` around a single distinguished
target zero.  Here the expansion is carried out for the *whole* family at once,
in the form the top-down route needs (milestone **M2**), and the two candidate
defect carriers are compared algebraically (milestone **M3**).

With `A = ∑_ρ Q_ρ`, `Q_ρ = 2 m_ρ (a_ρ a_ρᵀ - b_ρ b_ρᵀ)`, the exact identity is

  `‖A‖_F² = ∑_ρ 4 m_ρ² (A_ρ - B_ρ)²   (the diagonal on-line baselines)`
  `        + 8 ∑_ρ m_ρ² (A_ρ B_ρ - C_ρ²)   (the diagonal Gram sum, D_diag)`
  `        + ∑_ρ ∑_{σ ≠ ρ} ⟨Q_ρ, Q_σ⟩_F   (the off-diagonal interference)`

(`frobSq_pairFamily_expand`).  Nothing here is called a "critical baseline":
each term is exactly what it is.  Since the diagonal baselines are squares, the
diagonal Gram sum obeys the *literal* inequality

  `D_diag ≤ ‖A‖_F² + E_off`,

whenever `E_off` dominates the off-diagonal interference
(`diagGramSum_le_of_offDiag_bound`), and, transporting through `A = G - E`,

  `D_diag ≤ 2‖G‖_F² + 2‖E‖_F² + E_off`

(`diagGramSum_le_transport`) — a genuine inequality between real numbers, not
an asymptotic statement, ready to be fed the prime-side bound on `‖G‖_F²`.

For **M3**, the trace of a pair block is `tr Q = 2m(A - B)`, so the rank--trace
combination `F₂ = c·tr A - ‖A‖_F²` carries the Gram defect with the *opposite*
sign to `F₁ = ‖A‖_F²`:

  `c·tr Q - ‖Q‖_F² = 2mc(A - B) - 4m²(A - B)² - 8m²(AB - C²)`

(`rankTrace_pairBlock`).  Consequently a *lower* bound on the Gram defect makes
`F₁` large (`frobSq_ge_of_gramDefect_lower`) but makes `F₂` small
(`rankTrace_le_of_gramDefect_lower`).  The two observables therefore respond to
the transverse offset `α` with opposite monotonicity: the Gram defect is
detected by `F₁` from below and by `F₂` from above.  Whichever is used, it is
this sign that decides the direction in which the prime-side bound has to be
applied.
-/
import RiemannAnalytic.OneSidedGram

namespace RiemannAnalytic

open Finset Matrix

variable {ι : Type*} {n : Type*} [Fintype n]

/-! ### M2: the full pairwise expansion -/

/-- The **diagonal Gram sum** of a family of pair blocks:
`D_diag = 8 ∑_ρ m_ρ² (A_ρ B_ρ - C_ρ²)`. -/
def diagGramSum (s : Finset ι) (m : ι → ℝ) (a b : ι → n → ℝ) : ℝ :=
  8 * ∑ ρ ∈ s, m ρ ^ 2 * gramDefect (a ρ) (b ρ)

/-- The **diagonal baseline sum** of a family of pair blocks:
`∑_ρ 4 m_ρ² (A_ρ - B_ρ)²`. -/
def diagBaselineSum (s : Finset ι) (m : ι → ℝ) (a b : ι → n → ℝ) : ℝ :=
  ∑ ρ ∈ s, 4 * m ρ ^ 2 * ((a ρ ⬝ᵥ a ρ) - (b ρ ⬝ᵥ b ρ)) ^ 2

/-- The **off-diagonal interference** of a family of pair blocks. -/
noncomputable def offDiagInterference [DecidableEq ι] (s : Finset ι) (m : ι → ℝ)
    (a b : ι → n → ℝ) : ℝ :=
  ∑ ρ ∈ s, ∑ σ ∈ s.erase ρ, frobInner (pairBlock (m ρ) (a ρ) (b ρ))
    (pairBlock (m σ) (a σ) (b σ))

/-- The diagonal Gram sum is nonnegative. -/
theorem diagGramSum_nonneg (s : Finset ι) (m : ι → ℝ) (a b : ι → n → ℝ) :
    0 ≤ diagGramSum s m a b := by
  unfold diagGramSum
  have : 0 ≤ ∑ ρ ∈ s, m ρ ^ 2 * gramDefect (a ρ) (b ρ) :=
    Finset.sum_nonneg fun ρ _ => mul_nonneg (sq_nonneg _) (gramDefect_nonneg _ _)
  linarith

/-- The diagonal baseline sum is nonnegative. -/
theorem diagBaselineSum_nonneg (s : Finset ι) (m : ι → ℝ) (a b : ι → n → ℝ) :
    0 ≤ diagBaselineSum s m a b :=
  Finset.sum_nonneg fun ρ _ => by positivity

/-- **M2: the exact pairwise expansion of the finite zero-side Frobenius
square.**

  `‖A‖_F² = diagonal baselines + diagonal Gram sum + off-diagonal
  interference`,

with every term literally defined; no term is *called* a critical baseline. -/
theorem frobSq_pairFamily_expand [DecidableEq ι] (s : Finset ι) (m : ι → ℝ)
    (a b : ι → n → ℝ) :
    frobSq (∑ ρ ∈ s, pairBlock (m ρ) (a ρ) (b ρ))
      = diagBaselineSum s m a b + diagGramSum s m a b
        + offDiagInterference s m a b := by
  classical
  rw [frobSq_sum s fun ρ => pairBlock (m ρ) (a ρ) (b ρ)]
  have hrow : ∀ ρ ∈ s, ∑ σ ∈ s, frobInner (pairBlock (m ρ) (a ρ) (b ρ))
        (pairBlock (m σ) (a σ) (b σ))
      = frobSq (pairBlock (m ρ) (a ρ) (b ρ))
        + ∑ σ ∈ s.erase ρ, frobInner (pairBlock (m ρ) (a ρ) (b ρ))
            (pairBlock (m σ) (a σ) (b σ)) := by
    intro ρ hρ
    exact (Finset.add_sum_erase s
      (fun σ => frobInner (pairBlock (m ρ) (a ρ) (b ρ))
        (pairBlock (m σ) (a σ) (b σ))) hρ).symm
  have hdiag : ∑ ρ ∈ s, frobSq (pairBlock (m ρ) (a ρ) (b ρ))
      = diagBaselineSum s m a b + diagGramSum s m a b := by
    unfold diagBaselineSum diagGramSum
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [pairBlock_gramDecomposition]
    ring
  rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib, hdiag]
  unfold offDiagInterference
  ring

/-- **The diagonal Gram sum is bounded by the assembled Frobenius square plus
the off-diagonal budget.**  This is the literal form of the reduction: no
counterfactual "criticalized" configuration is used, only the fact that the
diagonal baselines are squares. -/
theorem diagGramSum_le_of_offDiag_bound [DecidableEq ι] (s : Finset ι) (m : ι → ℝ)
    (a b : ι → n → ℝ) {Eoff : ℝ} (hoff : -Eoff ≤ offDiagInterference s m a b) :
    diagGramSum s m a b ≤ frobSq (∑ ρ ∈ s, pairBlock (m ρ) (a ρ) (b ρ)) + Eoff := by
  have hexp := frobSq_pairFamily_expand s m a b
  have hbase := diagBaselineSum_nonneg s m a b
  linarith

/-! ### Transport through `A = G - E` -/

/-- The Frobenius square of a difference is at most twice the sum of the two
Frobenius squares. -/
theorem frobSq_sub_le (G E : Matrix n n ℝ) :
    frobSq (G - E) ≤ 2 * frobSq G + 2 * frobSq E := by
  unfold frobSq frobInner
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  simp only [Matrix.sub_apply]
  nlinarith [sq_nonneg (G i j + E i j)]

/-- **Literal `A → G` transport of the diagonal Gram sum.**  If the assembled
zero-side matrix is the prime-side matrix minus an error matrix, `A = G - E`,
then

  `D_diag ≤ 2‖G‖_F² + 2‖E‖_F² + E_off`.

Every term is a real number and the inequality is exact; feeding a prime-side
bound `‖G‖_F² ≤ M₂(T) + E_prime` gives the corresponding literal chain. -/
theorem diagGramSum_le_transport [DecidableEq ι] (s : Finset ι) (m : ι → ℝ)
    (a b : ι → n → ℝ) (G E : Matrix n n ℝ)
    (hA : ∑ ρ ∈ s, pairBlock (m ρ) (a ρ) (b ρ) = G - E)
    {Eoff : ℝ} (hoff : -Eoff ≤ offDiagInterference s m a b) :
    diagGramSum s m a b ≤ 2 * frobSq G + 2 * frobSq E + Eoff := by
  have h1 := diagGramSum_le_of_offDiag_bound s m a b hoff
  rw [hA] at h1
  have h2 := frobSq_sub_le G E
  linarith

/-- The same, with the prime-side bound already applied:
`‖G‖_F² ≤ M₂ + E_prime` gives `D_diag ≤ 2M₂ + 2E_prime + 2‖E‖_F² + E_off`. -/
theorem diagGramSum_le_prime [DecidableEq ι] (s : Finset ι) (m : ι → ℝ)
    (a b : ι → n → ℝ) (G E : Matrix n n ℝ)
    (hA : ∑ ρ ∈ s, pairBlock (m ρ) (a ρ) (b ρ) = G - E)
    {Eoff M₂ Eprime : ℝ} (hoff : -Eoff ≤ offDiagInterference s m a b)
    (hprime : frobSq G ≤ M₂ + Eprime) :
    diagGramSum s m a b ≤ 2 * M₂ + 2 * Eprime + 2 * frobSq E + Eoff := by
  have h := diagGramSum_le_transport s m a b G E hA hoff
  linarith

/-! ### M3: the two candidate defect observables -/

/-- The trace of a rank-one matrix is the dot product of its two vectors. -/
theorem trace_vecMulVec (a b : n → ℝ) : Matrix.trace (vecMulVec a b) = a ⬝ᵥ b := by
  simp [Matrix.trace, Matrix.diag, vecMulVec_apply, dotProduct]

/-- **The trace of a pair block:** `tr Q = 2m(A - B)`. -/
theorem pairBlock_trace (m : ℝ) (a b : n → ℝ) :
    Matrix.trace (pairBlock m a b) = 2 * m * ((a ⬝ᵥ a) - (b ⬝ᵥ b)) := by
  unfold pairBlock
  rw [Matrix.trace_smul, Matrix.trace_sub, trace_vecMulVec, trace_vecMulVec]
  simp [smul_eq_mul]

/-- **The rank--trace functional of a pair block.**

  `c·tr Q - ‖Q‖_F² = 2mc(A - B) - 4m²(A - B)² - 8m²(AB - C²)`.

The Gram defect enters with a **negative** sign, the opposite of its sign in
the raw Frobenius square. -/
theorem rankTrace_pairBlock (c m : ℝ) (a b : n → ℝ) :
    c * Matrix.trace (pairBlock m a b) - frobSq (pairBlock m a b)
      = 2 * m * c * ((a ⬝ᵥ a) - (b ⬝ᵥ b))
        - 4 * m ^ 2 * ((a ⬝ᵥ a) - (b ⬝ᵥ b)) ^ 2
        - 8 * m ^ 2 * gramDefect a b := by
  rw [pairBlock_trace, pairBlock_gramDecomposition]
  ring

/-- **`F₁ = ‖·‖_F²` responds to the Gram defect from below.**  A lower bound
for the Gram defect is a lower bound for the pair-block Frobenius square, over
and above its baseline. -/
theorem frobSq_ge_of_gramDefect_lower {D : ℝ} (m : ℝ) (a b : n → ℝ)
    (hD : D ≤ gramDefect a b) :
    4 * m ^ 2 * ((a ⬝ᵥ a) - (b ⬝ᵥ b)) ^ 2 + 8 * m ^ 2 * D
      ≤ frobSq (pairBlock m a b) := by
  rw [pairBlock_gramDecomposition]
  nlinarith [sq_nonneg m, hD]

/-- **`F₂ = c·tr - ‖·‖_F²` responds to the Gram defect from above.**  The same
lower bound for the Gram defect is an *upper* bound for the rank--trace
functional.  So the two candidate observables are monotone in the transverse
data with opposite signs: a coercive Gram defect pushes `F₁` up and `F₂`
down. -/
theorem rankTrace_le_of_gramDefect_lower {D : ℝ} (c m : ℝ) (a b : n → ℝ)
    (hD : D ≤ gramDefect a b) :
    c * Matrix.trace (pairBlock m a b) - frobSq (pairBlock m a b)
      ≤ 2 * m * c * ((a ⬝ᵥ a) - (b ⬝ᵥ b))
        - 4 * m ^ 2 * ((a ⬝ᵥ a) - (b ⬝ᵥ b)) ^ 2 - 8 * m ^ 2 * D := by
  rw [rankTrace_pairBlock]
  nlinarith [sq_nonneg m, hD]

/-- **The rank--trace functional of the whole family.**  Combining the trace
additivity with the pairwise expansion,

  `c·tr A - ‖A‖_F² = c ∑_ρ 2m_ρ(A_ρ - B_ρ) - diagonal baselines - D_diag
      - off-diagonal interference`.

In particular the diagonal Gram sum is subtracted, so an upper bound on the
rank--trace functional does *not* by itself bound `D_diag` from above; the
inequality has to be run in the other direction. -/
theorem rankTrace_pairFamily [DecidableEq ι] (s : Finset ι) (c : ℝ) (m : ι → ℝ)
    (a b : ι → n → ℝ) :
    c * Matrix.trace (∑ ρ ∈ s, pairBlock (m ρ) (a ρ) (b ρ))
        - frobSq (∑ ρ ∈ s, pairBlock (m ρ) (a ρ) (b ρ))
      = c * ∑ ρ ∈ s, 2 * m ρ * ((a ρ ⬝ᵥ a ρ) - (b ρ ⬝ᵥ b ρ))
        - diagBaselineSum s m a b - diagGramSum s m a b
        - offDiagInterference s m a b := by
  rw [frobSq_pairFamily_expand s m a b, Matrix.trace_sum]
  rw [Finset.sum_congr rfl fun ρ (_ : ρ ∈ s) => pairBlock_trace (m ρ) (a ρ) (b ρ)]
  ring

end RiemannAnalytic
