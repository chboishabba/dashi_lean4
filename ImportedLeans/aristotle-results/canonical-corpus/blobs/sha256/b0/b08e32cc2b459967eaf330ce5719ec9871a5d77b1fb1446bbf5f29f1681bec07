/-
# Row A1a — the derivative of the eliminated-coordinate substitution

In the block-spin step the substitution `B' = C(U)B` is *not* an arbitrary
background-dependent change of variables.  It is the identity on almost every
bond; on each eliminated bond its value is defined by solving the single
constraint equation

    (Q(U) C(U) B)(c) = 0,

i.e. the substitution lands identically in the kernel of the averaging operator:
`Q(U)C(U) = 0` for every background `U`.

Differentiating that identity along a background family is an *exact* algebraic
statement, not a guess about an abstract connection term:

    Q'C + QC' = 0,   hence   Q C' = −Q' C.

This file proves that, and then closes the remaining freedom.

* `constraint_derivative` : `Q(t)·C' = −Q'·C(t)`.
* `eliminated_derivative_solve` : if the derivative is supported on the
  eliminated coordinates, `C' = E·X`, and the pivot `P = Q(t)·E` has a left
  inverse, then `X = −P⁻¹·(Q'·C(t))` — the substitution derivative is *computed*
  by the pivot solve, not postulated.
* `eliminated_derivative_unique` : two substitution derivatives with the same
  support and the same pivot agree.
* `unmoved_entry_derivative_zero` : on a bond where `C` does not move, `C'`
  vanishes — the formal version of "`C` is the identity on almost every bond".
* `pivot_needed` : without an invertible pivot the constraint derivative does
  not determine `C'`; two different candidates satisfy the same equation.

Nothing here asserts the literal `Q'(U)` of Bałaban's construction; that
remains the open source datum.  What is closed is the step from `Q'` to `C'`.
-/
import RequestProject.YangMills.MatrixFamilyDerivative

namespace YangMills

open Matrix

variable {c n m : Type*} [Fintype c] [Fintype n] [DecidableEq c]

omit [Fintype c] [DecidableEq c] in
/-- **The exact algebraic consequence of the constraint identity:
`Q C' = −Q' C`.** -/
theorem constraint_derivative {Q : ℝ → Matrix c n ℝ} {C : ℝ → Matrix n m ℝ}
    {Q' : Matrix c n ℝ} {C' : Matrix n m ℝ} {t : ℝ}
    (hQ : HasMatDerivAt Q Q' t) (hC : HasMatDerivAt C C' t)
    (hconstr : ∀ s, Q s * C s = 0) :
    Q t * C' = -(Q' * C t) := by
  have h := (hQ.mul hC).of_eq_zero hconstr
  have : Q' * C t + Q t * C' = 0 := h
  linear_combination (norm := module) this

/-- **The pivot solve.**  If the substitution derivative is carried by the
eliminated coordinates, `C' = E·X`, and the pivot `P = Q(t)·E` has a left
inverse `Pinv`, then `X` is determined: `X = −Pinv·(Q'·C(t))`. -/
theorem eliminated_derivative_solve {Q : ℝ → Matrix c n ℝ} {C : ℝ → Matrix n m ℝ}
    {Q' : Matrix c n ℝ} {C' : Matrix n m ℝ} {t : ℝ}
    {E : Matrix n c ℝ} {X : Matrix c m ℝ} {P Pinv : Matrix c c ℝ}
    (hQ : HasMatDerivAt Q Q' t) (hC : HasMatDerivAt C C' t)
    (hconstr : ∀ s, Q s * C s = 0)
    (hsupp : C' = E * X) (hP : Q t * E = P) (hPinv : Pinv * P = 1) :
    X = -(Pinv * (Q' * C t)) := by
  have h := constraint_derivative hQ hC hconstr
  rw [hsupp, ← Matrix.mul_assoc, hP] at h
  calc X = (Pinv * P) * X := by rw [hPinv, Matrix.one_mul]
    _ = Pinv * (P * X) := by rw [Matrix.mul_assoc]
    _ = Pinv * (-(Q' * C t)) := by rw [h]
    _ = -(Pinv * (Q' * C t)) := by rw [Matrix.mul_neg]

/-- Two eliminated-coordinate substitution derivatives with the same support and
the same invertible pivot coincide. -/
theorem eliminated_derivative_unique {E : Matrix n c ℝ} {X Y : Matrix c m ℝ}
    {Qt : Matrix c n ℝ} {P Pinv : Matrix c c ℝ}
    (hP : Qt * E = P) (hPinv : Pinv * P = 1)
    (h : Qt * (E * X) = Qt * (E * Y)) : X = Y := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP] at h
  calc X = (Pinv * P) * X := by rw [hPinv, Matrix.one_mul]
    _ = Pinv * (P * X) := by rw [Matrix.mul_assoc]
    _ = Pinv * (P * Y) := by rw [h]
    _ = (Pinv * P) * Y := by rw [Matrix.mul_assoc]
    _ = Y := by rw [hPinv, Matrix.one_mul]

omit [Fintype c] [Fintype n] [DecidableEq c] in
/-- **`C` is the identity on almost every bond.**  Where the substitution entry
does not move with the background, its derivative vanishes. -/
theorem unmoved_entry_derivative_zero {C : ℝ → Matrix n m ℝ} {C' : Matrix n m ℝ}
    {t : ℝ} (hC : HasMatDerivAt C C' t) {i : n} {j : m} {v : ℝ}
    (hfix : ∀ s, C s i j = v) : C' i j = 0 := by
  have h : (fun s => C s i j) = fun _ => v := funext hfix
  have h1 : HasDerivAt (fun s => C s i j) (C' i j) t := hC i j
  rw [h] at h1
  exact h1.unique (hasDerivAt_const t v)

/-- **The pivot is load-bearing.**  With a degenerate pivot the constraint
derivative does not determine the substitution derivative: two different
matrices satisfy the same equation. -/
theorem pivot_needed :
    ∃ (Qt : Matrix (Fin 1) (Fin 1) ℝ) (E : Matrix (Fin 1) (Fin 1) ℝ)
      (X Y : Matrix (Fin 1) (Fin 1) ℝ),
      X ≠ Y ∧ Qt * (E * X) = Qt * (E * Y) := by
  refine ⟨0, 1, 0, 1, ?_, by simp⟩
  intro h
  have := congrFun (congrFun h 0) 0
  simp at this

end YangMills
