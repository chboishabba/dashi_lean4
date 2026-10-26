import Mathlib

/-!
# An adversarial steady-force pressure witness

Primary source under audit:
Weiping Yan and Vicenţiu D. Rădulescu (2021), DOI
10.1007/s12215-020-00540-3, equations (1.1) and (1.3), printed page 996;
Theorem 1.1 on page 997 permits nonzero small external f.

Original source identity: the authors own their stationary existence theorem.
This elementary polynomial counterexample is a DASHI independent *consistency
test*, not an allegation that the original authors considered this case.

Set U=0 in 3D, P(x)=eps*x₁²/2, f=(eps*x₁,0,0). The steady momentum equation
-νΔU+(U·∇)U+∇P=f is satisfied pointwise and U obeys homogeneous Dirichlet
conditions. For eps≠0, ΔP=eps=div f whereas the displayed equation (1.3),
without div f, would demand ΔP=0 because ∇U=0. No pressure boundary
condition was imposed in (1.1)-(1.3).

This file *kernel-facing* certifies the nontrivial one-coordinate polynomial
derivatives and their nonzero mismatch; the 3D embedding is explained above
but the whole vector calculus operator has not been constructed here. The
conclusion is conditional: one may add div f=0 or alter the pressure equation;
the source's main theorem is not refuted as a separately constrained result.
-/

namespace RequestProject.NavierStokes.YanRadulescuPressureCountermodel

def pressureSlice (eps x : ℝ) : ℝ := eps * x ^ 2 / 2

def forceSlice (eps x : ℝ) : ℝ := eps * x

/-- The pressure-gradient component agrees with the external force. -/
theorem pressureSlice_hasDerivAt (eps x : ℝ) :
    HasDerivAt (pressureSlice eps) (forceSlice eps x) x := by
  convert ((((hasDerivAt_id x).pow 2).const_mul eps).div_const 2) using 1 <;>
    simp [pressureSlice, forceSlice] <;> ring

/-- The force has nonzero divergence in the x₁ direction if eps ≠ 0. -/
theorem forceSlice_hasDerivAt (eps x : ℝ) :
    HasDerivAt (forceSlice eps) eps x := by
  simpa [forceSlice] using ((hasDerivAt_id x).const_mul eps)

/-- The scalar Laplacian (second x₁ derivative) of the pressure equals
the scalar force divergence. This is an actual derivative statement,
not merely an arbitrary scalar equality package. -/
theorem pressureSlice_second_derivative (eps x : ℝ) :
    deriv (fun z => deriv (pressureSlice eps) z) x = eps := by
  have hFirst :
      (fun z => deriv (pressureSlice eps) z) = forceSlice eps := by
    funext z
    exact (pressureSlice_hasDerivAt eps z).deriv
  rw [hFirst]
  exact (forceSlice_hasDerivAt eps x).deriv

/-- An unqualified pressure law setting ΔP equal to zero fails for this
non-solenoidal but arbitrarily small nonzero forcing slice. -/
theorem pressureSlice_laplacian_not_zero
    (eps x : ℝ) (hNonzero : eps ≠ 0) :
    deriv (fun z => deriv (pressureSlice eps) z) x ≠ 0 := by
  rw [pressureSlice_second_derivative]
  exact hNonzero

/-- The forcing amplitude can be taken positive and arbitrarily small.
The exact analytic epsilon bounds of the Nash–Moser theorem are NOT
claimed by this existential real witness. -/
theorem positive_nonzero_forcing_below
    (bound : ℝ) (hBound : 0 < bound) :
    ∃ eps : ℝ, 0 < eps ∧ eps < bound ∧ eps ≠ 0 := by
  refine ⟨bound / 2, by linarith, by linarith, ?_⟩
  linarith

end RequestProject.NavierStokes.YanRadulescuPressureCountermodel
