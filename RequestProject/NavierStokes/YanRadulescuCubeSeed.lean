import Mathlib

/-!
# Yan–Rădulescu (2021) explicit cube-seed structural model

Original authors: Weiping Yan and Vicenţiu D. Rădulescu.
Source: "Sobolev regular solutions for the incompressible Navier–Stokes
equations in higher dimensions: asymptotics and representation formulae",
Rend. Circ. Mat. Palermo II. Ser. 70 (2021), 995–1021.
DOI: 10.1007/s12215-020-00540-3. Corollary 1.1, displayed U^(0)
on p. 998 and its divergence-free / Dirichlet boundary conditions.

A separable structural reconstruction takes F : ℝ → ℝ and D = F'
at the relevant three coordinates, then builds
  (F(x₁)D(x₂)D(x₃), D(x₁)F(x₂)D(x₃),
    -2 D(x₁)D(x₂)F(x₃)).
The paper's exponential-polynomial cube seed motivates this *pattern*.
Identifying F and D with the paper's specific exponential-polynomial
factors is a separate exact-expression proof, not silently assumed.

The theorems below prove zero divergence from the stated HasDerivAt
hypotheses, and vanishing on every cube face from F,D endpoint zeros.
They do not prove Nash–Moser existence, Sobolev smallness, convergence
of U^(∞), positivity of viscosity, or the paper's pressure formula.
-/

namespace RequestProject.NavierStokes.YanRadulescuCubeSeed

def seed1 (F D : ℝ → ℝ) (x₁ x₂ x₃ : ℝ) : ℝ :=
  F x₁ * D x₂ * D x₃

def seed2 (F D : ℝ → ℝ) (x₁ x₂ x₃ : ℝ) : ℝ :=
  D x₁ * F x₂ * D x₃

def seed3 (F D : ℝ → ℝ) (x₁ x₂ x₃ : ℝ) : ℝ :=
  (-2 * D x₁ * D x₂) * F x₃

theorem hasDerivAt_seed1
    (F D : ℝ → ℝ) (x₁ x₂ x₃ : ℝ)
    (hF : HasDerivAt F (D x₁) x₁) :
    HasDerivAt (fun y => seed1 F D y x₂ x₃)
      (D x₁ * D x₂ * D x₃) x₁ := by
  simpa [seed1, mul_assoc] using
    (hF.mul_const (D x₂ * D x₃))

theorem hasDerivAt_seed2
    (F D : ℝ → ℝ) (x₁ x₂ x₃ : ℝ)
    (hF : HasDerivAt F (D x₂) x₂) :
    HasDerivAt (fun y => seed2 F D x₁ y x₃)
      (D x₁ * D x₂ * D x₃) x₂ := by
  simpa [seed2, mul_assoc] using
    ((hF.const_mul (D x₁)).mul_const (D x₃))

theorem hasDerivAt_seed3
    (F D : ℝ → ℝ) (x₁ x₂ x₃ : ℝ)
    (hF : HasDerivAt F (D x₃) x₃) :
    HasDerivAt (fun y => seed3 F D x₁ x₂ y)
      ((-2 * D x₁ * D x₂) * D x₃) x₃ := by
  simpa [seed3] using
    (hF.const_mul (-2 * D x₁ * D x₂))

theorem seed_divergence_zero
    (F D : ℝ → ℝ) (x₁ x₂ x₃ : ℝ)
    (hF1 : HasDerivAt F (D x₁) x₁)
    (hF2 : HasDerivAt F (D x₂) x₂)
    (hF3 : HasDerivAt F (D x₃) x₃) :
    deriv (fun y => seed1 F D y x₂ x₃) x₁ +
    deriv (fun y => seed2 F D x₁ y x₃) x₂ +
    deriv (fun y => seed3 F D x₁ x₂ y) x₃ = 0 := by
  rw [(hasDerivAt_seed1 F D x₁ x₂ x₃ hF1).deriv,
      (hasDerivAt_seed2 F D x₁ x₂ x₃ hF2).deriv,
      (hasDerivAt_seed3 F D x₁ x₂ x₃ hF3).deriv]
  ring

/-- On the three coordinate-zero faces, each component vanishes provided
both F and its nominated derivative D vanish at zero. -/
theorem seed_zero_faces
    (F D : ℝ → ℝ) (x₁ x₂ x₃ : ℝ)
    (hF : F 0 = 0) (hD : D 0 = 0) :
    (seed1 F D 0 x₂ x₃ = 0 ∧
     seed2 F D 0 x₂ x₃ = 0 ∧
     seed3 F D 0 x₂ x₃ = 0) ∧
    (seed1 F D x₁ 0 x₃ = 0 ∧
     seed2 F D x₁ 0 x₃ = 0 ∧
     seed3 F D x₁ 0 x₃ = 0) ∧
    (seed1 F D x₁ x₂ 0 = 0 ∧
     seed2 F D x₁ x₂ 0 = 0 ∧
     seed3 F D x₁ x₂ 0 = 0) := by
  simp [seed1, seed2, seed3, hF, hD]

/-- On the three coordinate-T faces, each component vanishes provided
both F and D vanish at the chosen endpoint T. -/
theorem seed_upper_faces
    (F D : ℝ → ℝ) (T x₁ x₂ x₃ : ℝ)
    (hF : F T = 0) (hD : D T = 0) :
    (seed1 F D T x₂ x₃ = 0 ∧
     seed2 F D T x₂ x₃ = 0 ∧
     seed3 F D T x₂ x₃ = 0) ∧
    (seed1 F D x₁ T x₃ = 0 ∧
     seed2 F D x₁ T x₃ = 0 ∧
     seed3 F D x₁ T x₃ = 0) ∧
    (seed1 F D x₁ x₂ T = 0 ∧
     seed2 F D x₁ x₂ T = 0 ∧
     seed3 F D x₁ x₂ T = 0) := by
  simp [seed1, seed2, seed3, hF, hD]

/-!
## Exact formal derivative-factor algebra

If a(y) = y(y-T), h(y)=a(y)^(qPred+1) and
rho(y)=a(y)^(rhoPred+1), the chain/product rules give
h' - h rho' = a^qPred a' * ((qPred+1) -
                             (rhoPred+1)*a^(rhoPred+1)).
For the paper's p and q, take qPred=q-1 and
rhoPred=2(p+1)-1. This lemma pays the universal algebra,
but identifying the actual HasDerivAt source expressions
still requires differential-calculus lemmas and is not
silently inferred.
-/

theorem derivative_factor_ring_identity
    (z zPrime : ℝ) (qPred rhoPred : ℕ) :
    (((qPred + 1 : ℕ) : ℝ) * z ^ qPred * zPrime) -
      z ^ (qPred + 1) *
        (((rhoPred + 1 : ℕ) : ℝ) * z ^ rhoPred * zPrime)
      =
    z ^ qPred * zPrime *
      (((qPred + 1 : ℕ) : ℝ) -
        ((rhoPred + 1 : ℕ) : ℝ) * z ^ (rhoPred + 1)) := by
  rw [pow_succ z qPred, pow_succ z rhoPred]
  ring

end RequestProject.NavierStokes.YanRadulescuCubeSeed
