import Mathlib
import Integration.Experiment.QuantityGraph
import Integration.Experiment.Uncertainty
import Integration.Experiment.Compiler

/-!
# Stage 5, lane 3 — certified sensitivities on graph edges, and a compiler that
propagates them

`TOE_STAGE4_INFERENCE.md` frontier item 3 records:

> **Certification is opt-in.**  `CertifiedSensitivity` exists and two laws use
> it.  The Stage-3 quantity-graph edges still carry uncertified rational
> sensitivity lists, and `compile` still does not invoke `Cov.push`/`RCov.push`.
> Obligation: a certified field on `Law`, and a compiler field carrying the
> propagated covariance.

Both halves are supplied here.

## The certificate on an edge

`CertifiedLaw n` is a quantity-graph `Law` of arity `n` together with

* a **real extension** `realEval` of its rational `eval`, and the proof
  `agrees` that the two agree on rational inputs;
* the proof `certified` that, at every rational operating point, the `i`-th
  entry of the edge's *own declared* `sensitivity` list is the derivative of
  `realEval` in the `i`-th coordinate.

So a `CertifiedLaw` is not a new sensitivity: it is the edge's existing
annotation with its obligation discharged.  `chargeCertificate` and
`energyCertificate` certify the coulomb-counting edge `Q = I t` and the energy
edge `E = V Q` of `Integration.Experiment.QuantityGraph`.

## The compiler field

`Integration.Experiment.Compiler.ExperimentSpec` gains `inputVariances`
(defaulting to `[]`, i.e. *nothing declared*), and `ExperimentPrediction` gains
`propagatedVariance`, which `compile` **computes**.  Proved here:

| Theorem | Content |
|---|---|
| `compile_propagatedVariance` | the compiler's number is the declared row applied to the declared variances |
| `compile_propagatedVariance_eq_push` | and it **is** `Cov.push` of that row against the diagonal input covariance — the compiler now invokes first-order propagation, not a separate formula |
| `compile_propagatedVariance_nonneg` | it is nonnegative whenever the declared variances are |
| `compile_propagatedVariance_of_nothing_declared` | with nothing declared it is `0`, and that `0` is a *declaration gap*, not an uncertainty claim |
| `compile_variance_from_certified_derivatives` | with a `CertifiedLaw` supplying the row, every factor in the propagated variance is a genuine partial derivative |

and the two negatives that keep the layers apart:

| Theorem | Content |
|---|---|
| `propagation_cannot_detect_a_wrong_row` | the compiler's number depends only on the row it is given: an uncertified row produces an equally well-typed, different answer |
| `certificate_does_not_make_propagation_exact` | a certified derivative is still only first order — for a nonlinear edge the linearised variation is not the true one |

## Claim boundary

No probability: a "variance" here is a declared nonnegative rational propagated
by a linear-algebra rule, exactly as in `Integration.Experiment.Uncertainty`.
Certification concerns derivatives of the *model*, not agreement with any
measurement.
-/

namespace Integration.Experiment.CertifiedPropagation

open Integration.Experiment.QuantityGraph
open Integration.Experiment.Uncertainty
open Integration.Experiment.Compiler

/-! ## §1 A certified edge -/

/-- **A quantity-graph edge whose declared sensitivities are proved to be
derivatives.**  `realEval` is a real extension of the edge's rational `eval`;
`certified` says the edge's own `sensitivity` list is the vector of partial
derivatives of that extension. -/
structure CertifiedLaw (n : ℕ) where
  /-- The edge being certified. -/
  law : Law
  /-- Its declared arity. -/
  arity : law.inputs.length = n
  /-- A real extension of the rational evaluation rule. -/
  realEval : (Fin n → ℝ) → ℝ
  /-- The extension agrees with the edge on rational inputs. -/
  agrees : ∀ v : Fin n → ℚ, realEval (fun i => (v i : ℝ)) = ((law.eval (List.ofFn v) : ℚ) : ℝ)
  /-- The edge's declared sensitivity vector at a rational operating point. -/
  row : (Fin n → ℚ) → Fin n → ℚ
  /-- The row really is the edge's own declared `sensitivity` list. -/
  row_is_declared : ∀ (v : Fin n → ℚ) (i : Fin n),
    row v i = (law.sensitivity (List.ofFn v)).getD i 0
  /-- **The certificate**: each declared entry is the corresponding partial
  derivative of the real extension. -/
  certified : ∀ (v : Fin n → ℚ) (i : Fin n),
    HasDerivAt (fun t : ℝ => realEval (Function.update (fun j => (v j : ℝ)) i t))
      ((row v i : ℝ)) ((v i : ℝ))

/-- The certificate, restated with `deriv`. -/
theorem CertifiedLaw.declared_is_the_partial_derivative {n : ℕ} (c : CertifiedLaw n)
    (v : Fin n → ℚ) (i : Fin n) :
    deriv (fun t : ℝ => c.realEval (Function.update (fun j => (v j : ℝ)) i t)) ((v i : ℝ))
      = ((c.row v i : ℚ) : ℝ) :=
  (c.certified v i).deriv

/-- The coulomb-counting edge `Q = I t`, certified: its declared list `[t, I]`
is the pair of partial derivatives of `(i, t) ↦ i · t`. -/
noncomputable def chargeCertificate : CertifiedLaw 2 where
  law := chargeLaw
  arity := rfl
  realEval := fun x => x 0 * x 1
  agrees := by
    intro v
    simp [chargeLaw, List.ofFn_succ]
  row := fun v => ![v 1, v 0]
  row_is_declared := by
    intro v i
    fin_cases i <;> simp [chargeLaw, List.ofFn_succ]
  certified := by
    intro v i
    fin_cases i
    · have : (fun t : ℝ => (Function.update (fun j => ((v j : ℝ))) 0 t) 0
          * (Function.update (fun j => ((v j : ℝ))) 0 t) 1)
          = fun t : ℝ => t * (v 1 : ℝ) := by
        funext t
        rw [Function.update_self, Function.update_of_ne (by decide)]
      simpa [this] using (hasDerivAt_id ((v 0 : ℝ))).mul_const ((v 1 : ℝ))
    · have : (fun t : ℝ => (Function.update (fun j => ((v j : ℝ))) 1 t) 0
          * (Function.update (fun j => ((v j : ℝ))) 1 t) 1)
          = fun t : ℝ => (v 0 : ℝ) * t := by
        funext t
        rw [Function.update_self, Function.update_of_ne (by decide)]
      simpa [this] using (hasDerivAt_id ((v 1 : ℝ))).const_mul ((v 0 : ℝ))

/-- The energy edge `E = V Q`, certified in the same way. -/
noncomputable def energyCertificate : CertifiedLaw 2 where
  law := energyLaw
  arity := rfl
  realEval := fun x => x 0 * x 1
  agrees := by
    intro v
    simp [energyLaw, List.ofFn_succ]
  row := fun v => ![v 1, v 0]
  row_is_declared := by
    intro v i
    fin_cases i <;> simp [energyLaw, List.ofFn_succ]
  certified := by
    intro v i
    fin_cases i
    · have : (fun t : ℝ => (Function.update (fun j => ((v j : ℝ))) 0 t) 0
          * (Function.update (fun j => ((v j : ℝ))) 0 t) 1)
          = fun t : ℝ => t * (v 1 : ℝ) := by
        funext t
        rw [Function.update_self, Function.update_of_ne (by decide)]
      simpa [this] using (hasDerivAt_id ((v 0 : ℝ))).mul_const ((v 1 : ℝ))
    · have : (fun t : ℝ => (Function.update (fun j => ((v j : ℝ))) 1 t) 0
          * (Function.update (fun j => ((v j : ℝ))) 1 t) 1)
          = fun t : ℝ => (v 0 : ℝ) * t := by
        funext t
        rw [Function.update_self, Function.update_of_ne (by decide)]
      simpa [this] using (hasDerivAt_id ((v 1 : ℝ))).const_mul ((v 0 : ℝ))

/-! ## §2 Propagation as `Cov.push` -/

/-- First-order propagation of independent input variances `d` along a
sensitivity row, as the `(0,0)` entry of `J Σ Jᵀ`. -/
def propagatedVariance {n : ℕ} (row d : Fin n → ℚ) (hd : ∀ i, 0 ≤ d i) : ℚ :=
  (Cov.push (Matrix.of ![row]) (Cov.diag d hd)).toMatrix 0 0

/-- The scalar formula, for the row form. -/
theorem propagatedVariance_eq_sum {n : ℕ} (row d : Fin n → ℚ) (hd : ∀ i, 0 ≤ d i) :
    propagatedVariance row d hd = ∑ i, (row i) ^ 2 * d i := by
  rw [propagatedVariance, scalar_variance_diagonal]
  rfl

theorem propagatedVariance_nonneg {n : ℕ} (row d : Fin n → ℚ) (hd : ∀ i, 0 ≤ d i) :
    0 ≤ propagatedVariance row d hd := by
  rw [propagatedVariance_eq_sum]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hd i)

/-- The declared `(sensitivity, variance)` list built from a row and a variance
vector. -/
def ofRow {n : ℕ} (row d : Fin n → ℚ) : List (ℚ × ℚ) :=
  List.ofFn (fun i => (row i, d i))

/-! ## §3 The compiler field -/

variable {H State Control Obs : Type} [Fintype H] [DecidableEq Obs]

/-- The compiler's propagated variance is computed from the declared row and
variances. -/
theorem compile_propagatedVariance (e : ExperimentSpec H State Control Obs) :
    (compile e).propagatedVariance
      = (e.inputVariances.map (fun p => p.1 ^ 2 * p.2)).sum := rfl

/-- **The compiler invokes first-order propagation.**  When the declared list
comes from a row and a variance vector, the number `compile` reports *is*
`Cov.push` of that row against the diagonal input covariance. -/
theorem compile_propagatedVariance_eq_push {n : ℕ} (e : ExperimentSpec H State Control Obs)
    (row d : Fin n → ℚ) (hd : ∀ i, 0 ≤ d i) (he : e.inputVariances = ofRow row d) :
    (compile e).propagatedVariance = propagatedVariance row d hd := by
  rw [compile_propagatedVariance, he, propagatedVariance_eq_sum, ofRow,
    List.map_ofFn, List.sum_ofFn]
  rfl

/-- Nonnegativity of the reported number, from the declared variances. -/
theorem compile_propagatedVariance_nonneg (e : ExperimentSpec H State Control Obs)
    (hd : ∀ p ∈ e.inputVariances, 0 ≤ p.2) :
    0 ≤ (compile e).propagatedVariance := by
  rw [compile_propagatedVariance]
  refine List.sum_nonneg ?_
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  exact mul_nonneg (sq_nonneg _) (hd p hp)

/-- **Nothing declared reports zero — and that zero is a declaration gap.**  The
compiler does not distinguish "no propagated uncertainty" from "no inputs
declared"; only the specification does. -/
theorem compile_propagatedVariance_of_nothing_declared
    (e : ExperimentSpec H State Control Obs) (he : e.inputVariances = []) :
    (compile e).propagatedVariance = 0 := by
  rw [compile_propagatedVariance, he]
  rfl

/-- **The propagated variance is built from genuine partial derivatives** when
the row is supplied by a certified edge: each factor squared in the reported
number is the derivative the certificate proves it to be. -/
theorem compile_variance_from_certified_derivatives {n : ℕ} (c : CertifiedLaw n)
    (v d : Fin n → ℚ) (hd : ∀ i, 0 ≤ d i) (e : ExperimentSpec H State Control Obs)
    (he : e.inputVariances = ofRow (c.row v) d) :
    (((compile e).propagatedVariance : ℚ) : ℝ)
      = ∑ i, (deriv (fun t : ℝ =>
          c.realEval (Function.update (fun j => (v j : ℝ)) i t)) ((v i : ℝ))) ^ 2
            * ((d i : ℚ) : ℝ) := by
  rw [compile_propagatedVariance_eq_push e (c.row v) d hd he, propagatedVariance_eq_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [c.declared_is_the_partial_derivative v i]

/-! ## §4 What certification does not buy -/

/-- **The compiler cannot detect a wrong row.**  Its output is a function of the
declared sensitivities alone: an uncertified row is just as well typed and gives
a different answer.  This is why the certificate has to be carried by the edge
rather than checked downstream. -/
theorem propagation_cannot_detect_a_wrong_row :
    ∃ (row₁ row₂ d : Fin 1 → ℚ) (hd : ∀ i, 0 ≤ d i),
      row₁ ≠ row₂ ∧ propagatedVariance row₁ d hd ≠ propagatedVariance row₂ d hd := by
  refine ⟨![1], ![2], ![1], ?_, ?_, ?_⟩
  · intro i; fin_cases i; norm_num
  · intro h
    have := congrFun h 0
    norm_num at this
  · rw [propagatedVariance_eq_sum, propagatedVariance_eq_sum]
    norm_num

/-- **A certified derivative is still only first order.**  For a nonlinear edge
the linearised variation is not the true variation, however exactly the
derivative is certified: propagation is a first-order rule, not an error
bound. -/
theorem certificate_does_not_make_propagation_exact :
    ∃ (f : ℝ → ℝ) (x h : ℝ), HasDerivAt f (2 * x) x ∧ h ≠ 0 ∧
      f (x + h) - f x ≠ (2 * x) * h := by
  refine ⟨fun t => t ^ 2, 1, 1, ?_, one_ne_zero, ?_⟩
  · simpa using (hasDerivAt_pow 2 (1 : ℝ))
  · norm_num

end Integration.Experiment.CertifiedPropagation
