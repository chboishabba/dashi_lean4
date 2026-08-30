/-
# What decides the sign of the Gaussian coefficient: the second variation

`ConstrainedPositivity` reduced the sign question for the diagonal one-loop
functional

    betaTrace G V V S = ½ Tr(G V G V) − ½ Tr(G S)

to the seagull term: the bubble is always `≥ 0` for a constrained (Schur
projected) propagator and a symmetric variation.  This module pushes the
reduction one step further, from an inequality on a trace to a *structural*
property of the second background variation `S`, and records the sharpness of
the resulting criterion.

* `trace_gram_mul_gram_nonneg` — for a Gram propagator `G = CᵀC` and a positive
  semidefinite second variation `S = WᵀW`, `Tr(G S) ≥ 0`.  So a purely
  "diamagnetic" (Gram) seagull enters the coefficient with the *unfavourable*
  sign.

* `affineGram_expansion` — if the fluctuation operator is the Gram form of a
  background-affine first-order operator, `Δ(s,t) = M(s,t)ᵀ M(s,t)` with
  `M(s,t) = M₀ + s•M₁ + t•M₂`, then

      Δ(s,t) = M₀ᵀM₀ + s•V₁ + t•V₂ + (s·t)•S + (s·s)•(M₁ᵀM₁) + (t·t)•(M₂ᵀM₂),
      V_i = M₀ᵀM_i + M_iᵀM₀   (symmetric),   S = M₁ᵀM₂ + M₂ᵀM₁,

  and on the diagonal (`M₁ = M₂`) the mixed second variation is
  `S = 2•(M₁ᵀM₁) ⪰ 0`.  Combined with the previous item:
  `diamagnetic_seagull_nonneg`.  A covariant-derivative-squared operator with no
  spin/commutator term therefore never gets positivity for free — the bubble has
  to beat the seagull (`betaTrace_nonneg_iff_bubble_dominates`), and
  `betaTrace_nonpos_of_pure_diamagnetic` shows the coefficient is genuinely
  `≤ 0` when the bubble is switched off.

* `betaTrace_nonneg_of_paramagnetic` / `betaTrace_pos_of_paramagnetic` and the
  Brillouin corollary `brillouinSum_pos_of_paramagnetic_seagull` — conversely, a
  negative semidefinite ("paramagnetic") second variation `S = −WᵀW` makes the
  whole coefficient nonnegative, and strictly positive as soon as the propagator
  does not annihilate the first variation at one momentum.  This is the cleanest
  checkable form of the A1a Gaussian target: *extract the second background
  variation and check its sign*.

* `betaTrace_nonneg_of_paramagnetic_dominance` — the mixed case
  `S = S_dia − S_para` with both parts Gram: positivity follows from dominance
  of the paramagnetic part in the propagator trace.

Nothing here asserts which case the literal Bałaban operator falls into; that is
exactly the source datum A1a still needs.  All statements are exact algebra over
`ℝ`.
-/
import RequestProject.YangMills.CMP109SymbolChain

namespace YangMills

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- **A Gram second variation has a nonnegative propagator trace.**
`Tr(CᵀC · WᵀW) = Tr((WCᵀ)ᵀ(WCᵀ)) ≥ 0`. -/
theorem trace_gram_mul_gram_nonneg {G S C W : Matrix n n ℝ}
    (hG : G = Cᵀ * C) (hS : S = Wᵀ * W) :
    0 ≤ (G * S).trace := by
  have e : G * S = Cᵀ * (C * Wᵀ * W) := by
    rw [hG, hS]; simp [Matrix.mul_assoc]
  have e2 : C * Wᵀ * W * Cᵀ = (W * Cᵀ)ᵀ * (W * Cᵀ) := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, show C * Wᵀ * W * Cᵀ = (W * Cᵀ)ᵀ * (W * Cᵀ) from e2]
  have hpsd : ((W * Cᵀ)ᵀ * (W * Cᵀ)).PosSemidef := by
    simpa using Matrix.posSemidef_conjTranspose_mul_self (W * Cᵀ)
  exact hpsd.trace_nonneg

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- A negative semidefinite ("paramagnetic") second variation has a nonpositive
propagator trace, which is precisely the seagull hypothesis of
`betaTrace_nonneg_of_seagull_nonpos`. -/
theorem seagull_nonpos_of_negSemidef {G S C W : Matrix n n ℝ}
    (hG : G = Cᵀ * C) (hS : S = -(Wᵀ * W)) :
    (G * S).trace ≤ 0 := by
  have h : 0 ≤ (G * (Wᵀ * W)).trace := trace_gram_mul_gram_nonneg hG rfl
  rw [hS, Matrix.mul_neg, Matrix.trace_neg]
  linarith

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- **Paramagnetic sign criterion.**  A constrained (Gram) propagator, a
symmetric first variation and a negative semidefinite second variation give a
nonnegative one-loop coefficient. -/
theorem betaTrace_nonneg_of_paramagnetic {G V S C W : Matrix n n ℝ}
    (hG : G = Cᵀ * C) (hV : Vᵀ = V) (hS : S = -(Wᵀ * W)) :
    0 ≤ betaTrace G V V S :=
  betaTrace_nonneg_of_seagull_nonpos hG hV (seagull_nonpos_of_negSemidef hG hS)

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- The strict form: if in addition the propagator does not annihilate the first
variation, the coefficient is strictly positive. -/
theorem betaTrace_pos_of_paramagnetic {G V S C W : Matrix n n ℝ}
    (hG : G = Cᵀ * C) (hV : Vᵀ = V) (hne : G * V * G ≠ 0) (hS : S = -(Wᵀ * W)) :
    0 < betaTrace G V V S :=
  betaTrace_pos_of_seagull_nonpos hG hV hne (seagull_nonpos_of_negSemidef hG hS)

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- **Mixed case: paramagnetic dominance.**  If the second variation splits into
a diamagnetic and a paramagnetic Gram part, `S = W₁ᵀW₁ − W₂ᵀW₂`, positivity of
the coefficient follows from dominance of the paramagnetic part inside the
propagator trace. -/
theorem betaTrace_nonneg_of_paramagnetic_dominance {G V S C W₁ W₂ : Matrix n n ℝ}
    (hG : G = Cᵀ * C) (hV : Vᵀ = V) (hS : S = W₁ᵀ * W₁ - W₂ᵀ * W₂)
    (hdom : (G * (W₁ᵀ * W₁)).trace ≤ (G * (W₂ᵀ * W₂)).trace) :
    0 ≤ betaTrace G V V S := by
  refine betaTrace_nonneg_of_seagull_nonpos hG hV ?_
  rw [hS, Matrix.mul_sub, Matrix.trace_sub]
  linarith

section AffineGram

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- **The background expansion of a Gram fluctuation operator.**  For a
background-affine first-order operator `M(s,t) = M₀ + s•M₁ + t•M₂` the
fluctuation operator `Δ = MᵀM` expands with symmetric first variations
`V_i = M₀ᵀM_i + M_iᵀM₀` and mixed second variation `S = M₁ᵀM₂ + M₂ᵀM₁`. -/
theorem affineGram_expansion (M₀ M₁ M₂ : Matrix n n ℝ) (s t : ℝ) :
    (M₀ + s • M₁ + t • M₂)ᵀ * (M₀ + s • M₁ + t • M₂)
      = M₀ᵀ * M₀ + s • (M₀ᵀ * M₁ + M₁ᵀ * M₀) + t • (M₀ᵀ * M₂ + M₂ᵀ * M₀)
        + (s * t) • (M₁ᵀ * M₂ + M₂ᵀ * M₁)
        + (s * s) • (M₁ᵀ * M₁) + (t * t) • (M₂ᵀ * M₂) := by
  simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, mul_comm t s]
  abel

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- The first variations of a Gram fluctuation operator are symmetric, so the
bubble term of the diagonal coefficient is always nonnegative. -/
theorem affineGram_variation_symm (M₀ M₁ : Matrix n n ℝ) :
    (M₀ᵀ * M₁ + M₁ᵀ * M₀)ᵀ = M₀ᵀ * M₁ + M₁ᵀ * M₀ := by
  simp [Matrix.transpose_add, Matrix.transpose_mul, add_comm]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- On the diagonal the mixed second variation of a Gram fluctuation operator is
`2 M₁ᵀ M₁`, a positive semidefinite matrix. -/
theorem affineGram_diagonal_secondVariation (M₁ : Matrix n n ℝ) :
    M₁ᵀ * M₁ + M₁ᵀ * M₁ = (2 : ℝ) • (M₁ᵀ * M₁) := by
  rw [two_smul]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- **The diamagnetic seagull has the unfavourable sign.**  For a Gram
propagator and the diagonal second variation `S = 2 M₁ᵀM₁` of a Gram fluctuation
operator, `Tr(G S) ≥ 0`, i.e. the seagull term `−½Tr(G S)` of the coefficient is
nonpositive.  Positivity of the coefficient then has to come from the bubble. -/
theorem diamagnetic_seagull_nonneg {G C M₁ : Matrix n n ℝ} (hG : G = Cᵀ * C) :
    0 ≤ (G * ((2 : ℝ) • (M₁ᵀ * M₁))).trace := by
  have h : 0 ≤ (G * (M₁ᵀ * M₁)).trace := trace_gram_mul_gram_nonneg hG rfl
  rw [Matrix.mul_smul, Matrix.trace_smul]
  simpa using by linarith [h]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- In the purely diamagnetic case the sign question is exactly a competition
between bubble and seagull. -/
theorem betaTrace_nonneg_iff_bubble_dominates (G V S : Matrix n n ℝ) :
    0 ≤ betaTrace G V V S ↔ (G * S).trace ≤ (G * V * G * V).trace := by
  rw [betaTrace]
  constructor <;> intro h <;> linarith

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- **Sharpness.**  With the bubble switched off (`V = 0`) and a diamagnetic
second variation, the coefficient is nonpositive: the criterion of
`betaTrace_nonneg_of_paramagnetic` is not vacuous, and its sign hypothesis
cannot be dropped. -/
theorem betaTrace_nonpos_of_pure_diamagnetic {G S C W : Matrix n n ℝ}
    (hG : G = Cᵀ * C) (hS : S = Wᵀ * W) :
    betaTrace G 0 0 S ≤ 0 := by
  have h : 0 ≤ (G * S).trace := trace_gram_mul_gram_nonneg hG hS
  rw [betaTrace]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.trace_zero]
  linarith

end AffineGram

section Brillouin

variable {ι : Type*} [Fintype ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **A1a Gaussian positivity from the sign of the literal second variation.**
Suppose that at every Brillouin momentum the unconstrained symbol is a Gram
covariance with invertible reduced constraint block, the first background
variation is symmetric, and the second background variation is negative
semidefinite, `s(q) = −W(q)ᵀW(q)`; and suppose at one momentum the constrained
propagator does not annihilate the first variation.  Then the Gaussian
coefficient is a strictly positive finite Brillouin sum.

This is the form in which the literal symbol extraction can be consumed: no
global control over the Brillouin zone, no near/far split, and only a *sign*
(not an estimate) is required of the extracted second variation. -/
theorem brillouinSum_pos_of_paramagnetic_seagull
    (Bq : ι → Matrix κ κ ℝ) (Qs : ι → Matrix m κ ℝ)
    (hK : ∀ q, (Qs q * ((Bq q)ᵀ * Bq q) * (Qs q)ᵀ).det ≠ 0)
    (v s W : ι → Matrix κ κ ℝ) (hv : ∀ q, (v q)ᵀ = v q)
    (hs : ∀ q, s q = -((W q)ᵀ * W q))
    (q₀ : ι)
    (hq₀ : constrainedPropagator ((Bq q₀)ᵀ * Bq q₀) (Qs q₀) * v q₀
        * constrainedPropagator ((Bq q₀)ᵀ * Bq q₀) (Qs q₀) ≠ 0) :
    0 < ∑ q, brillouinIntegrand (constrainedPropagator ((Bq q)ᵀ * Bq q) (Qs q))
        (v q) (v q) (s q) := by
  refine brillouinSum_pos_criterion (μ := m) Bq Qs hK v s hv (fun q => ?_) q₀ hq₀
  exact seagull_nonpos_of_negSemidef
    (constrainedPropagator_gram (Bq q) (Qs q) (hK q)) (hs q)

omit [DecidableEq κ] in
/-- **The paramagnetic criterion in Gram form.**  The same conclusion as
`brillouinSum_pos_of_paramagnetic_seagull`, stated for a symbol that is supplied
already in factorised form `g(q) = C(q)ᵀC(q)` rather than through the Schur
formula.  This is the form used by closed-form symbols such as the lattice
transverse propagator. -/
theorem brillouinSum_pos_of_gram (g v s C W : ι → Matrix κ κ ℝ)
    (hg : ∀ q, g q = (C q)ᵀ * C q) (hv : ∀ q, (v q)ᵀ = v q)
    (hs : ∀ q, s q = -((W q)ᵀ * W q))
    (q₀ : ι) (hne : g q₀ * v q₀ * g q₀ ≠ 0) :
    0 < ∑ q, brillouinIntegrand (g q) (v q) (v q) (s q) := by
  refine brillouinSum_pos_of_exists _ _ _ _ (fun q => ?_) q₀ ?_
  · exact betaTrace_nonneg_of_seagull_nonpos (hg q) (hv q)
      (seagull_nonpos_of_negSemidef (hg q) (hs q))
  · exact betaTrace_pos_of_seagull_nonpos (hg q₀) (hv q₀) hne
      (seagull_nonpos_of_negSemidef (hg q₀) (hs q₀))

end Brillouin

end YangMills
