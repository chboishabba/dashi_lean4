/-
# The lattice transverse symbol satisfies the hypotheses of the sign criterion

`TransverseSymbol` produced the closed-form constrained symbol of the project's
lattice conventions,

    G(p) = (1/p̂²) · (1 − p̂p̂ᵀ/p̂²),      p̂_μ = 2 sin(π p_μ),

as the Schur projection of the scalar covariance `(1/p̂²)·1` by the rank-one
constraint `p̂ᵀ`, and showed that it inverts the Wilson operator on the
constraint kernel.  `SeagullSign` reduced the sign of the Gaussian coefficient
to a Gram factorisation of the symbol plus a sign for the second background
variation.

This module joins the two: the transverse projector is a symmetric idempotent,
hence its own Gram factor, so the lattice symbol is exactly of the form the sign
criterion consumes, and

* `latticeBrillouinSum_pos_of_paramagnetic` — for the project's literal lattice
  transverse symbol, any symmetric first background variation and any negative
  semidefinite second background variation, the finite Brillouin sum of the
  one-loop integrand is strictly positive as soon as the symbol does not
  annihilate the first variation at one momentum.

So on the lattice-symbol side the Gaussian A1a target reduces to a single
qualitative source datum: *the sign of the second background variation*.  No
value of a beta coefficient is asserted; the first and second background
variations of the literal Bałaban operator are still the missing input.
-/
import RequestProject.YangMills.SeagullSign
import RequestProject.YangMills.TransverseSymbol

namespace YangMills

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- The rank-one matrix `uuᵀ` is symmetric. -/
theorem vecMulVec_transpose (u : n → ℝ) :
    (Matrix.vecMulVec u u)ᵀ = Matrix.vecMulVec u u := by
  ext i j; simp [Matrix.vecMulVec_apply, mul_comm]

omit [DecidableEq n] in
/-- `uuᵀ · uuᵀ = |u|² · uuᵀ`. -/
theorem vecMulVec_mul_self (u : n → ℝ) :
    Matrix.vecMulVec u u * Matrix.vecMulVec u u = (normSqVec u) • Matrix.vecMulVec u u := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul,
    normSqVec]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The transverse projector is symmetric. -/
theorem transverseProjector_transpose (u : n → ℝ) :
    (transverseProjector u)ᵀ = transverseProjector u := by
  rw [transverseProjector, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_smul, vecMulVec_transpose]

/-- The transverse projector is idempotent. -/
theorem transverseProjector_idem (u : n → ℝ) (hu : normSqVec u ≠ 0) :
    transverseProjector u * transverseProjector u = transverseProjector u := by
  set c := normSqVec u with hc
  set w := Matrix.vecMulVec u u with hw
  have hww : w * w = c • w := vecMulVec_mul_self u
  have e : (1 - c⁻¹ • w) * (1 - c⁻¹ • w) = 1 - c⁻¹ • w := by
    have expand : (1 - c⁻¹ • w) * (1 - c⁻¹ • w)
        = 1 - c⁻¹ • w - c⁻¹ • w + (c⁻¹ * c⁻¹) • (w * w) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.mul_smul]
      module
    have hcc : c⁻¹ * c⁻¹ * c = c⁻¹ := by field_simp
    rw [expand, hww, smul_smul, hcc]
    abel
  rw [transverseProjector, ← hc, ← hw, e]

/-- **The transverse projector is its own Gram factor.** -/
theorem transverseProjector_gram (u : n → ℝ) (hu : normSqVec u ≠ 0) :
    transverseProjector u = (transverseProjector u)ᵀ * transverseProjector u := by
  rw [transverseProjector_transpose, transverseProjector_idem u hu]

/-- A nonnegative multiple of the transverse projector is a Gram matrix, with
the explicit factor `√a · P`. -/
theorem smul_transverseProjector_gram (u : n → ℝ) (hu : normSqVec u ≠ 0) {a : ℝ}
    (ha : 0 ≤ a) :
    a • transverseProjector u
      = (Real.sqrt a • transverseProjector u)ᵀ * (Real.sqrt a • transverseProjector u) := by
  rw [Matrix.transpose_smul, transverseProjector_transpose, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, transverseProjector_idem u hu,
    Real.mul_self_sqrt ha]

section Lattice

/-- **The lattice constrained symbol in Gram form.**  With `p̂² ≠ 0`,

    G(p) = (1/p̂²)·(1 − p̂p̂ᵀ/p̂²) = C(p)ᵀ C(p),   C(p) = (1/p̂²)^{1/2}·(1 − p̂p̂ᵀ/p̂²). -/
theorem latticeSymbol_gram (p : Fin 4 → ℝ) (hp : phatSq p ≠ 0) :
    constrainedPropagator ((phatSq p)⁻¹ • (1 : Matrix (Fin 4) (Fin 4) ℝ))
        (rowVec (phatVec p))
      = (Real.sqrt (phatSq p)⁻¹ • transverseProjector (phatVec p))ᵀ
        * (Real.sqrt (phatSq p)⁻¹ • transverseProjector (phatVec p)) := by
  have hu : normSqVec (phatVec p) ≠ 0 := by rw [normSqVec_phatVec]; exact hp
  rw [constrainedPropagator_lattice p hp]
  exact smul_transverseProjector_gram (phatVec p) hu (inv_nonneg.mpr (phatSq_nonneg p))

variable {ι : Type*} [Fintype ι]

/-- **Positivity of the Gaussian coefficient on the lattice transverse symbol.**
Let `p : ι → (Fin 4 → ℝ)` be a finite set of momenta with `p̂² ≠ 0`, let the
first background variation `v(q)` be symmetric and the second background
variation be negative semidefinite, `s(q) = −W(q)ᵀW(q)`, and suppose that at one
momentum the symbol does not annihilate the first variation.  Then the finite
Brillouin sum of the one-loop integrand, evaluated on the project's literal
lattice constrained symbol, is strictly positive.

The only remaining source datum in this statement is the *sign* of the second
background variation of the literal fluctuation operator. -/
theorem latticeBrillouinSum_pos_of_paramagnetic
    (p : ι → (Fin 4 → ℝ)) (hp : ∀ q, phatSq (p q) ≠ 0)
    (v s W : ι → Matrix (Fin 4) (Fin 4) ℝ)
    (hv : ∀ q, (v q)ᵀ = v q) (hs : ∀ q, s q = -((W q)ᵀ * W q))
    (q₀ : ι)
    (hne : constrainedPropagator ((phatSq (p q₀))⁻¹ • (1 : Matrix (Fin 4) (Fin 4) ℝ))
        (rowVec (phatVec (p q₀))) * v q₀
      * constrainedPropagator ((phatSq (p q₀))⁻¹ • (1 : Matrix (Fin 4) (Fin 4) ℝ))
        (rowVec (phatVec (p q₀))) ≠ 0) :
    0 < ∑ q, brillouinIntegrand
        (constrainedPropagator ((phatSq (p q))⁻¹ • (1 : Matrix (Fin 4) (Fin 4) ℝ))
          (rowVec (phatVec (p q)))) (v q) (v q) (s q) :=
  brillouinSum_pos_of_gram _ v s
    (fun q => Real.sqrt (phatSq (p q))⁻¹ • transverseProjector (phatVec (p q))) W
    (fun q => latticeSymbol_gram (p q) (hp q)) hv hs q₀ hne

section NonVacuity

omit [DecidableEq n] in
/-- The trace of the rank-one matrix `uuᵀ` is `|u|²`. -/
theorem trace_vecMulVec (u : n → ℝ) : (Matrix.vecMulVec u u).trace = normSqVec u := by
  simp [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, normSqVec]

/-- The transverse projector has trace `dim − 1`; in particular it is nonzero as
soon as the space has dimension at least two. -/
theorem transverseProjector_trace (u : n → ℝ) (hu : normSqVec u ≠ 0) :
    (transverseProjector u).trace = (Fintype.card n : ℝ) - 1 := by
  rw [transverseProjector, Matrix.trace_sub, Matrix.trace_one, Matrix.trace_smul,
    trace_vecMulVec, smul_eq_mul, inv_mul_cancel₀ hu]

theorem transverseProjector_ne_zero (u : n → ℝ) (hu : normSqVec u ≠ 0)
    (hcard : Fintype.card n ≠ 1) : transverseProjector u ≠ 0 := by
  intro h
  have ht := transverseProjector_trace u hu
  rw [h, Matrix.trace_zero] at ht
  have : (Fintype.card n : ℝ) = 1 := by linarith
  exact hcard (by exact_mod_cast this)

/-- **The non-annihilation hypothesis of the lattice criterion is satisfiable.**
Taking the first background variation to be the transverse projector itself, the
lattice symbol does not annihilate it at any momentum with `p̂² ≠ 0`. -/
theorem latticeSymbol_bubble_ne_zero (p : Fin 4 → ℝ) (hp : phatSq p ≠ 0) :
    constrainedPropagator ((phatSq p)⁻¹ • (1 : Matrix (Fin 4) (Fin 4) ℝ))
          (rowVec (phatVec p)) * transverseProjector (phatVec p)
        * constrainedPropagator ((phatSq p)⁻¹ • (1 : Matrix (Fin 4) (Fin 4) ℝ))
          (rowVec (phatVec p)) ≠ 0 := by
  have hu : normSqVec (phatVec p) ≠ 0 := by rw [normSqVec_phatVec]; exact hp
  have hidem := transverseProjector_idem (phatVec p) hu
  rw [constrainedPropagator_lattice p hp]
  have e : ((phatSq p)⁻¹ • transverseProjector (phatVec p))
        * transverseProjector (phatVec p)
      * ((phatSq p)⁻¹ • transverseProjector (phatVec p))
      = ((phatSq p)⁻¹ * (phatSq p)⁻¹) • transverseProjector (phatVec p) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, hidem, smul_smul]
  rw [e]
  refine smul_ne_zero ?_ (transverseProjector_ne_zero (phatVec p) hu (by simp))
  exact mul_ne_zero (inv_ne_zero hp) (inv_ne_zero hp)

/-- **The lattice criterion is instantiable.**  At a single momentum with
`p̂² ≠ 0`, first variation the transverse projector and vanishing second
variation, the Brillouin sum is strictly positive. -/
theorem latticeBrillouinSum_pos_example (p : Fin 4 → ℝ) (hp : phatSq p ≠ 0) :
    0 < ∑ _q : Fin 1, brillouinIntegrand
        (constrainedPropagator ((phatSq p)⁻¹ • (1 : Matrix (Fin 4) (Fin 4) ℝ))
          (rowVec (phatVec p)))
        (transverseProjector (phatVec p)) (transverseProjector (phatVec p))
        (0 : Matrix (Fin 4) (Fin 4) ℝ) := by
  have hu : normSqVec (phatVec p) ≠ 0 := by rw [normSqVec_phatVec]; exact hp
  refine latticeBrillouinSum_pos_of_paramagnetic (ι := Fin 1) (fun _ => p) (fun _ => hp)
    (fun _ => transverseProjector (phatVec p)) (fun _ => 0) (fun _ => 0)
    (fun _ => transverseProjector_transpose (phatVec p)) (fun _ => by simp) 0 ?_
  exact latticeSymbol_bubble_ne_zero p hp

end NonVacuity

end Lattice

end YangMills
