/-
# The constrained Gaussian trace-log Hessian

This file proves the exact finite-dimensional second-variation identity for
`log det`, in the form it is used to read off a one-loop coefficient from a
background-dependent Gaussian normalisation

    log Z(U) = -(1/2) log det Â(U) + const.

For an operator family carrying the second-order jet

    A(s,t) = A + s•B + t•C + (s·t)•D,

with `A` nonsingular, the mixed second derivative of `log det` at the origin is

    ∂_s ∂_t log det A(s,t) |₀ = Tr(A⁻¹ D) − Tr(A⁻¹ B A⁻¹ C),

i.e. the exact *seagull minus bubble* structure: the `D`-term is the second
variation of the operator itself, the `B,C`-term is the product of two first
variations joined by two propagators.  Nothing here is specific to Yang–Mills:
it is the reusable substrate (`ConstrainedGaussianTraceLogHessian`) for the
one-loop coefficient and for any later Hessian consumer.

The proof is elementary and self-contained:

* `hasDerivAt_det_one_add_smul` — `d/dt det(1 + t•M)|₀ = Tr M`, obtained from the
  polynomial identity `Matrix.derivative_det_one_add_X_smul` by transporting it
  along the evaluation ring hom;
* `hasDerivAt_log_det_affine` — the first variation `d/dt log det(M + t•N)|₀ =
  Tr(M⁻¹N)` for nonsingular `M` (Jacobi's formula on an affine line);
* `hasDerivAt_trace_inv_affine` — the derivative of `s ↦ Tr((A+s•B)⁻¹(C+s•D))`
  at `0`, proved from the exact resolvent identity
  `(A+s•B)⁻¹ = A⁻¹ − s•((A+s•B)⁻¹ B A⁻¹)` and continuity of the inverse;
* `logDet_secondVariation` — the two combined.

No hypothesis beyond nonsingularity of `A` is used, and no norm on matrices is
needed.
-/
import Mathlib

namespace YangMills

open Matrix Filter Topology

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Trace of the first variation of the determinant at the identity.**
`d/dt det(1 + t•M)|_{t=0} = Tr M`. -/
theorem hasDerivAt_det_one_add_smul (M : Matrix n n ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • M).det) M.trace 0 := by
  set p : Polynomial ℝ :=
    (1 + (Polynomial.X : Polynomial ℝ) • M.map (Polynomial.C (R := ℝ))).det with hp
  have hev : ∀ t : ℝ, p.eval t = (1 + t • M).det := by
    intro t
    rw [hp, show Polynomial.eval t
        ((1 + (Polynomial.X : Polynomial ℝ) • M.map (Polynomial.C (R := ℝ))).det)
        = (Polynomial.evalRingHom t)
          ((1 + (Polynomial.X : Polynomial ℝ) • M.map (Polynomial.C (R := ℝ))).det) from rfl,
      RingHom.map_det]
    congr 1
    ext i j
    by_cases h : i = j
    · simp [Matrix.map_apply, h]; ring
    · simp [Matrix.map_apply, h]; ring
  have h1 := p.hasDerivAt (0 : ℝ)
  have h2 : Polynomial.eval 0 (Polynomial.derivative p) = M.trace :=
    Matrix.derivative_det_one_add_X_smul M
  rw [h2] at h1
  simpa [hev] using h1

/-- **Jacobi's formula on an affine line.**  For a nonsingular `M`,
`d/dt log det (M + t•N)|_{t=0} = Tr(M⁻¹N)`. -/
theorem hasDerivAt_log_det_affine (M N : Matrix n n ℝ) (hM : M.det ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log ((M + t • N).det)) (M⁻¹ * N).trace 0 := by
  have hfac : ∀ t : ℝ, (M + t • N) = M * (1 + t • (M⁻¹ * N)) := by
    intro t
    rw [Matrix.mul_add, mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hM), Matrix.one_mul]
  have hdet : ∀ t : ℝ, (M + t • N).det = M.det * (1 + t • (M⁻¹ * N)).det := by
    intro t; rw [hfac t, Matrix.det_mul]
  have h1 : HasDerivAt (fun t : ℝ => (M + t • N).det) (M.det * (M⁻¹ * N).trace) 0 := by
    have := (hasDerivAt_det_one_add_smul (M⁻¹ * N)).const_mul M.det
    simpa [hdet] using this
  have h2 : HasDerivAt Real.log (M.det)⁻¹ ((M + (0 : ℝ) • N).det) := by
    have h : (M + (0 : ℝ) • N).det = M.det := by simp
    rw [h]
    exact Real.hasDerivAt_log hM
  have hcomp := h2.comp 0 h1
  have hM' : (M.det)⁻¹ * (M.det * (M⁻¹ * N).trace) = (M⁻¹ * N).trace := by field_simp
  simpa [hM'] using hcomp

/-- **The exact resolvent identity along an affine line.** -/
theorem inv_affine_eq (A B : Matrix n n ℝ) (hA : A.det ≠ 0) {s : ℝ}
    (hs : (A + s • B).det ≠ 0) :
    (A + s • B)⁻¹ = A⁻¹ - s • ((A + s • B)⁻¹ * B * A⁻¹) := by
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 hA
  have h1 : (A + s • B)⁻¹ * (A + s • B) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hs)
  have h2 : (A + s • B)⁻¹ * ((A + s • B) * A⁻¹) = A⁻¹ := by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have h3 : (A + s • B) * A⁻¹ = 1 + s • (B * A⁻¹) := by
    rw [Matrix.add_mul, Matrix.mul_nonsing_inv _ hAu, Matrix.smul_mul]
  rw [h3, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc] at h2
  linear_combination (norm := module) h2

/-- **Derivative of the propagator-weighted trace along an affine line.** -/
theorem hasDerivAt_trace_inv_affine (A B C D : Matrix n n ℝ) (hA : A.det ≠ 0) :
    HasDerivAt (fun s : ℝ => ((A + s • B)⁻¹ * (C + s • D)).trace)
      ((A⁻¹ * D).trace - (A⁻¹ * B * A⁻¹ * C).trace) 0 := by
  set f : ℝ → ℝ := fun s => ((A + s • B)⁻¹ * (C + s • D)).trace with hf
  set g : ℝ → ℝ := fun s => (A⁻¹ * D).trace - ((A + s • B)⁻¹ * B * A⁻¹ * C).trace
      - s * ((A + s • B)⁻¹ * B * A⁻¹ * D).trace with hg
  have hcontA : Continuous (fun s : ℝ => A + s • B) := by fun_prop
  have hinv : ContinuousAt (fun s : ℝ => (A + s • B)⁻¹) 0 := by
    have h0 : (A + (0 : ℝ) • B) = A := by simp
    refine ContinuousAt.comp ?_ hcontA.continuousAt
    rw [h0]
    refine continuousAt_matrix_inv A ?_
    simpa [Ring.inverse_eq_inv'] using continuousAt_inv₀ hA
  have hgcont : ContinuousAt g 0 := by rw [hg]; fun_prop (disch := assumption)
  have hg0 : g 0 = (A⁻¹ * D).trace - (A⁻¹ * B * A⁻¹ * C).trace := by simp [hg]
  have hdetev : ∀ᶠ s : ℝ in 𝓝 0, (A + s • B).det ≠ 0 := by
    have h : ContinuousAt (fun s : ℝ => (A + s • B).det) 0 := hcontA.matrix_det.continuousAt
    simpa using h.eventually_ne (by simpa using hA)
  rw [hasDerivAt_iff_tendsto_slope]
  have hlim : Tendsto g (𝓝[≠] (0 : ℝ)) (𝓝 (g 0)) := hgcont.continuousWithinAt.tendsto
  rw [← hg0]
  refine hlim.congr' ?_
  have hev : ∀ᶠ s : ℝ in 𝓝[≠] (0 : ℝ), (A + s • B).det ≠ 0 ∧ s ≠ 0 :=
    (eventually_nhdsWithin_of_eventually_nhds hdetev).and self_mem_nhdsWithin
  filter_upwards [hev] with s ⟨hs, hs0⟩
  have hJ : (A + s • B)⁻¹ = A⁻¹ - s • ((A + s • B)⁻¹ * B * A⁻¹) := inv_affine_eq A B hA hs
  have hfs : f s = f 0 + s * g s := by
    rw [hf]
    simp only []
    rw [hJ]
    have hexp : (A⁻¹ - s • ((A + s • B)⁻¹ * B * A⁻¹)) * (C + s • D)
        = A⁻¹ * C + s • (A⁻¹ * D) - s • ((A + s • B)⁻¹ * B * A⁻¹ * C)
          - (s * s) • ((A + s • B)⁻¹ * B * A⁻¹ * D) := by
      simp [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_assoc]
      module
    rw [hexp]
    simp [hg, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul]
    ring
  have hslope : slope f 0 s = g s := by
    rw [slope_def_field, hfs, sub_zero, add_sub_cancel_left, mul_comm, mul_div_assoc,
      div_self hs0, mul_one]
  exact hslope.symm

/-- **`ConstrainedGaussianTraceLogHessian` — the exact second variation of
`log det`.**  For a nonsingular `A` and the second-order jet
`A(s,t) = A + s•B + t•C + (s·t)•D`,

    ∂_s ∂_t log det A(s,t)|₀ = Tr(A⁻¹ D) − Tr(A⁻¹ B A⁻¹ C).

The first term is the *seagull* (second variation of the operator), the second
is the *bubble* (two first variations joined by two propagators). -/
theorem logDet_secondVariation (A B C D : Matrix n n ℝ) (hA : A.det ≠ 0) :
    deriv (fun s : ℝ => deriv (fun t : ℝ =>
      Real.log ((A + s • B + t • C + (s * t) • D).det)) 0) 0
      = (A⁻¹ * D).trace - (A⁻¹ * B * A⁻¹ * C).trace := by
  have hcontA : Continuous (fun s : ℝ => A + s • B) := by fun_prop
  have hdetev : ∀ᶠ s : ℝ in 𝓝 0, (A + s • B).det ≠ 0 := by
    have h : ContinuousAt (fun s : ℝ => (A + s • B).det) 0 := hcontA.matrix_det.continuousAt
    simpa using h.eventually_ne (by simpa using hA)
  have hEq : (fun s : ℝ => deriv (fun t : ℝ =>
      Real.log ((A + s • B + t • C + (s * t) • D).det)) 0)
      =ᶠ[𝓝 0] fun s : ℝ => ((A + s • B)⁻¹ * (C + s • D)).trace := by
    filter_upwards [hdetev] with s hs
    have hre : ∀ t : ℝ, A + s • B + t • C + (s * t) • D = (A + s • B) + t • (C + s • D) := by
      intro t; rw [smul_add, smul_smul]; module
    have h := (hasDerivAt_log_det_affine (A + s • B) (C + s • D) hs).deriv
    simpa [hre] using h
  rw [hEq.deriv_eq]
  exact (hasDerivAt_trace_inv_affine A B C D hA).deriv

/-- The scalar CMP109-shaped one-loop trace: with `G` the propagator, `V₁,V₂` the
two first variations and `S` the second variation of the constrained operator,

    betaTrace G V₁ V₂ S = ½ Tr(G V₁ G V₂) − ½ Tr(G S).

This is *not* a definition of the physical beta coefficient; it is the exact
value of the Gaussian Hessian, see `gaussianHessian_eq_betaTrace`. -/
noncomputable def betaTrace (G V₁ V₂ S : Matrix n n ℝ) : ℝ :=
  1 / 2 * (G * V₁ * G * V₂).trace - 1 / 2 * (G * S).trace

/-- **The Gaussian Hessian is the bubble-minus-seagull trace.**  For
`log Z(s,t) = −½ log det A(s,t) + c` with `A(s,t) = A + s•V₁ + t•V₂ + (s·t)•S`,

    ∂_s ∂_t log Z |₀ = ½ Tr(G V₁ G V₂) − ½ Tr(G S),    G = A⁻¹.

This is the identity from which a one-loop coefficient is read off; no
convention for the coefficient itself is imposed here. -/
theorem gaussianHessian_eq_betaTrace (A V₁ V₂ S : Matrix n n ℝ) (hA : A.det ≠ 0) (c : ℝ) :
    deriv (fun s : ℝ => deriv (fun t : ℝ =>
      -(1 / 2 : ℝ) * Real.log ((A + s • V₁ + t • V₂ + (s * t) • S).det) + c) 0) 0
      = betaTrace A⁻¹ V₁ V₂ S := by
  have hinner : ∀ s : ℝ, deriv (fun t : ℝ =>
      -(1 / 2 : ℝ) * Real.log ((A + s • V₁ + t • V₂ + (s * t) • S).det) + c) 0
      = -(1 / 2 : ℝ) * deriv (fun t : ℝ =>
        Real.log ((A + s • V₁ + t • V₂ + (s * t) • S).det)) 0 := by
    intro s
    rw [deriv_add_const, deriv_const_mul_field]
  rw [funext hinner, deriv_const_mul_field, logDet_secondVariation A V₁ V₂ S hA, betaTrace,
    Matrix.mul_assoc]
  ring

end YangMills
