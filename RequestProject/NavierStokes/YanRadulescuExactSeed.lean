import Mathlib
import RequestProject.NavierStokes.YanRadulescuCubeSeed

/-!
# Yan–Rădulescu 2021, Corollary 1.1: exact printed cube seed

Original mathematical source:
Weiping Yan and Vicenţiu D. Rădulescu, "Sobolev regular solutions for the
incompressible Navier–Stokes equations in higher dimensions: asymptotics and
representation formulae", Rend. Circ. Mat. Palermo (2021),
DOI 10.1007/s12215-020-00540-3, **printed page 998**, Corollary 1.1.

This file reconstructs the actual exponential-polynomial *initial seed*
rather than an arbitrary separable F,D pattern. Here the original paper's
integer p>1 and q>2 are encoded as p=pExtra+2 and q=qExtra+3,
so no singular q-1 exponent or unjustified endpoint assumption is hidden.

Put a(y)=y(y-T), h(y)=a(y)^q, rho(y)=a(y)^(2(p+1)),
g(y)=a(y)^(q-1)(2y-T)[q-2(p+1)a(y)^(2(p+1))],
F(y)=h(y) exp(-rho(y)), D(y)=g(y) exp(-rho(y)).
The original displayed U⁽⁰⁾ is ε times the 3-component seed
(F₁D₂D₃,D₁F₂D₃,-2D₁D₂F₃), with all later n-3 components zero.

**Already proved here by reduction:** F,D vanish on both cube endpoints,
hence each 3-vector component vanishes on every coordinate face. The
divergence corollary requires the exact source derivative F'=D *as a
HasDerivAt hypothesis*; it is not automatically identified by the
printed formula or by an external symbolic Python check. A new generic
exponential-envelope chain-rule lemma supplies a reusable subproof.

The existence of an exact seed does not prove a stationary solution:
pressure consistency, forcing, Nash–Moser iteration and remainder are
all independent proof obligations.
-/

namespace RequestProject.NavierStokes.YanRadulescuExactSeed

open RequestProject.NavierStokes.YanRadulescuCubeSeed

def polynomialBase (T y : ℝ) : ℝ := y * (y - T)

/-- h(y)=y^q(y-T)^q, represented as [y(y-T)]^q. -/
def h (T : ℝ) (qExtra : ℕ) (y : ℝ) : ℝ :=
  polynomialBase T y ^ (qExtra + 3)

/-- rho(y)=[y(y-T)]^(2(p+1)), where p=pExtra+2. -/
def rho (T : ℝ) (pExtra : ℕ) (y : ℝ) : ℝ :=
  polynomialBase T y ^ (2 * (pExtra + 3))

/-- g as *printed* on page 998, with p>=2 and q>=3. -/
def g (T : ℝ) (pExtra qExtra : ℕ) (y : ℝ) : ℝ :=
  polynomialBase T y ^ (qExtra + 2) * (2 * y - T) *
    ((((qExtra + 3 : ℕ) : ℝ)) -
     (((2 * (pExtra + 3) : ℕ) : ℝ)) *
       polynomialBase T y ^ (2 * (pExtra + 3)))

def F (T : ℝ) (pExtra qExtra : ℕ) (y : ℝ) : ℝ :=
  h T qExtra y * Real.exp (-rho T pExtra y)

def D (T : ℝ) (pExtra qExtra : ℕ) (y : ℝ) : ℝ :=
  g T pExtra qExtra y * Real.exp (-rho T pExtra y)

theorem F_zero_at_zero (T : ℝ) (pExtra qExtra : ℕ) :
    F T pExtra qExtra 0 = 0 := by
  simp [F, h, polynomialBase]

theorem D_zero_at_zero (T : ℝ) (pExtra qExtra : ℕ) :
    D T pExtra qExtra 0 = 0 := by
  simp [D, g, polynomialBase]

theorem F_zero_at_upper (T : ℝ) (pExtra qExtra : ℕ) :
    F T pExtra qExtra T = 0 := by
  simp [F, h, polynomialBase]

theorem D_zero_at_upper (T : ℝ) (pExtra qExtra : ℕ) :
    D T pExtra qExtra T = 0 := by
  simp [D, g, polynomialBase]

/-- A derivative lemma for the exponential envelope; this applies to the
source F as soon as the derivatives of h and rho have been established.
It is classical analysis, reconstructed in DASHI; not a new theorem
attributed to the 2021 paper's authors. -/
theorem hasDerivAt_envelope
    (hh hr : ℝ → ℝ) (y dh dr : ℝ)
    (hDeriv : HasDerivAt hh dh y)
    (rDeriv : HasDerivAt hr dr y) :
    HasDerivAt (fun z => hh z * Real.exp (-hr z))
      ((dh - hh y * dr) * Real.exp (-hr y)) y := by
  convert hDeriv.mul (rDeriv.neg.exp) using 1 <;> ring

/-- The exact F/D identity follows from the two physical scalar-factor
derivative obligations and the source-specific algebraic identity.
Unlike an assumption F'=D, all quantities here are the *printed* ones. -/
theorem hasDerivAt_sourceF_from_factors
    (T : ℝ) (pExtra qExtra : ℕ) (y : ℝ)
    (hDerivative :
      HasDerivAt (h T qExtra)
        ((((qExtra + 3 : ℕ) : ℝ)) *
          polynomialBase T y ^ (qExtra + 2) * (2 * y - T)) y)
    (rhoDerivative :
      HasDerivAt (rho T pExtra)
        ((((2 * (pExtra + 3) : ℕ) : ℝ)) *
          polynomialBase T y ^ (2 * (pExtra + 3) - 1) *
          (2 * y - T)) y) :
    HasDerivAt (F T pExtra qExtra)
      (D T pExtra qExtra y) y := by
  have hProduct :=
    hasDerivAt_envelope
      (h T qExtra) (rho T pExtra) y
      ((((qExtra + 3 : ℕ) : ℝ)) *
        polynomialBase T y ^ (qExtra + 2) * (2 * y - T))
      ((((2 * (pExtra + 3) : ℕ) : ℝ)) *
        polynomialBase T y ^ (2 * (pExtra + 3) - 1) *
        (2 * y - T))
      hDerivative rhoDerivative
  convert hProduct using 1
  · rfl
  · simp only [F, D, g]
    have hPositive : 2 * (pExtra + 3) = (2 * (pExtra + 3) - 1) + 1 := by omega
    rw [hPositive, pow_succ]
    ring

/-- Exact printed F,D supply all six Dirichlet faces independently of
any derivative assertion. No PDE existence claim follows. -/
theorem printed_seed_zero_faces
    (T : ℝ) (pExtra qExtra : ℕ) (x₁ x₂ x₃ : ℝ) :
    ((seed1 (F T pExtra qExtra) (D T pExtra qExtra) 0 x₂ x₃ = 0 ∧
      seed2 (F T pExtra qExtra) (D T pExtra qExtra) 0 x₂ x₃ = 0 ∧
      seed3 (F T pExtra qExtra) (D T pExtra qExtra) 0 x₂ x₃ = 0) ∧
     (seed1 (F T pExtra qExtra) (D T pExtra qExtra) x₁ 0 x₃ = 0 ∧
      seed2 (F T pExtra qExtra) (D T pExtra qExtra) x₁ 0 x₃ = 0 ∧
      seed3 (F T pExtra qExtra) (D T pExtra qExtra) x₁ 0 x₃ = 0) ∧
     (seed1 (F T pExtra qExtra) (D T pExtra qExtra) x₁ x₂ 0 = 0 ∧
      seed2 (F T pExtra qExtra) (D T pExtra qExtra) x₁ x₂ 0 = 0 ∧
      seed3 (F T pExtra qExtra) (D T pExtra qExtra) x₁ x₂ 0 = 0)) := by
  exact seed_zero_faces
    (F T pExtra qExtra) (D T pExtra qExtra) x₁ x₂ x₃
    (F_zero_at_zero T pExtra qExtra)
    (D_zero_at_zero T pExtra qExtra)

/-- The same printed seed vanishes on xᵢ=T. -/
theorem printed_seed_upper_faces
    (T : ℝ) (pExtra qExtra : ℕ) (x₁ x₂ x₃ : ℝ) :
    ((seed1 (F T pExtra qExtra) (D T pExtra qExtra) T x₂ x₃ = 0 ∧
      seed2 (F T pExtra qExtra) (D T pExtra qExtra) T x₂ x₃ = 0 ∧
      seed3 (F T pExtra qExtra) (D T pExtra qExtra) T x₂ x₃ = 0) ∧
     (seed1 (F T pExtra qExtra) (D T pExtra qExtra) x₁ T x₃ = 0 ∧
      seed2 (F T pExtra qExtra) (D T pExtra qExtra) x₁ T x₃ = 0 ∧
      seed3 (F T pExtra qExtra) (D T pExtra qExtra) x₁ T x₃ = 0) ∧
     (seed1 (F T pExtra qExtra) (D T pExtra qExtra) x₁ x₂ T = 0 ∧
      seed2 (F T pExtra qExtra) (D T pExtra qExtra) x₁ x₂ T = 0 ∧
      seed3 (F T pExtra qExtra) (D T pExtra qExtra) x₁ x₂ T = 0)) := by
  exact seed_upper_faces
    (F T pExtra qExtra) (D T pExtra qExtra) T x₁ x₂ x₃
    (F_zero_at_upper T pExtra qExtra)
    (D_zero_at_upper T pExtra qExtra)

/-- Conditional divergence of the *exact printed* seed. The remaining
P0 leaf is supplying the actual `HasDerivAt_sourceF` uniformly, not
re-proving the already generic divergence cancellation. -/
theorem printed_seed_divergence_zero_of_source_derivatives
    (T : ℝ) (pExtra qExtra : ℕ) (x₁ x₂ x₃ : ℝ)
    (h1 : HasDerivAt (F T pExtra qExtra) (D T pExtra qExtra x₁) x₁)
    (h2 : HasDerivAt (F T pExtra qExtra) (D T pExtra qExtra x₂) x₂)
    (h3 : HasDerivAt (F T pExtra qExtra) (D T pExtra qExtra x₃) x₃) :
    deriv (fun y =>
      seed1 (F T pExtra qExtra) (D T pExtra qExtra) y x₂ x₃) x₁ +
    deriv (fun y =>
      seed2 (F T pExtra qExtra) (D T pExtra qExtra) x₁ y x₃) x₂ +
    deriv (fun y =>
      seed3 (F T pExtra qExtra) (D T pExtra qExtra) x₁ x₂ y) x₃ = 0 :=
  seed_divergence_zero
    (F T pExtra qExtra) (D T pExtra qExtra)
    x₁ x₂ x₃ h1 h2 h3

end RequestProject.NavierStokes.YanRadulescuExactSeed
