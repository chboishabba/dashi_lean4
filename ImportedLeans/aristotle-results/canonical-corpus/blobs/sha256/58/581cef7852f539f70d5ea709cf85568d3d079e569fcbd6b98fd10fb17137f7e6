/-
# The source-facing chain: constrained Gaussian → trace → Brillouin scalar → beta

This module welds the four pieces built in this round into the single chain a
one-loop coupling coefficient has to travel:

    log Z(U) = −½ log det Â(U)
      ⟶ (TraceLogHessian)         D² log Z = ½ Tr(G V₁ G V₂) − ½ Tr(G S)
      ⟶ (ConstrainedPropagator)   longitudinal directions cancel: Q G = 0, G Qᵀ = 0
      ⟶ (BrillouinReduction)      one scalar momentum sum ∑_q ( ½ g² v₁ v₂ − ½ g s )
      ⟶ (BetaProjection)          the p = 0 second jet ignores the third-order remainder.

Two theorems are proved here.

* `gaussianHessian_brillouin` — the Gaussian Hessian of a Fourier-diagonalised
  constrained operator jet *equals* an explicit scalar Brillouin sum.  Nothing
  is assumed about the sum: it is computed from the operator data.

* `beta_readoff_of_thirdOrder_remainder` — for a polarisation written as
  `Π = β·M + R` with `R` third order in lattice derivatives on the slice, the
  beta projection of `Π` is `β` times the beta projection of the marginal term.
  So the irrelevant remainder is invisible to the coefficient, and no global
  control of `Π` over the whole Brillouin zone is needed to determine it.

**What is still missing, stated precisely.**  These theorems consume, and do not
supply: the literal constrained operator `Â^{(j)}(U)` of the source, hence the
literal first and second variations `V_μ`, `S_{μν}`, hence the literal symbols
`g, v₁, v₂, s` of the diagonalised operators, and the literal marginal term `M`.
Until those are constructed, the scalar Brillouin sum below is an exact identity
about whatever operators are supplied, not a numerical value of a beta
coefficient, and nothing here asserts positivity of any beta coefficient.

**Provenance.**  No external source text was available in this environment, and
no formula here is presented as a transcription of one.  Every statement below
is a theorem about operators and functions supplied as hypotheses; the reader
who supplies literal operators from a source obtains a literal conclusion.  In
particular the universal coefficient `11/24 C_A` used elsewhere in this
development is *not* derived here, and no normalisation convention for a
physical beta function is imposed by these theorems.
-/
import RequestProject.YangMills.BrillouinReduction
import RequestProject.YangMills.ConstrainedPropagator
import RequestProject.YangMills.BetaProjection

namespace YangMills

open Matrix Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The constrained Gaussian Hessian as one scalar Brillouin sum.**
For `log Z(s,t) = −½ log det A(s,t) + c` with the second-order operator jet
`A(s,t) = A + s•V₁ + t•V₂ + (s·t)•S`, all of whose data are diagonalised by the
same Fourier transform `F` with symbols `g` (for `G = A⁻¹`), `v₁, v₂, s`,

    ∂_s ∂_t log Z |₀ = ∑_q ( ½ g q² v₁ q v₂ q − ½ g q s q ). -/
theorem gaussianHessian_brillouin {F : Matrix ι ι ℝ} (hF : F.det ≠ 0)
    {A V₁ V₂ S : Matrix ι ι ℝ} (hA : A.det ≠ 0) (c : ℝ)
    (g v₁ v₂ s : ι → ℝ)
    (hG : A⁻¹ = F * diagonal g * F⁻¹) (hV₁ : V₁ = F * diagonal v₁ * F⁻¹)
    (hV₂ : V₂ = F * diagonal v₂ * F⁻¹) (hS : S = F * diagonal s * F⁻¹) :
    deriv (fun x : ℝ => deriv (fun t : ℝ =>
      -(1 / 2 : ℝ) * Real.log ((A + x • V₁ + t • V₂ + (x * t) • S).det) + c) 0) 0
      = ∑ q, (1 / 2 * (g q * g q * v₁ q * v₂ q) - 1 / 2 * (g q * s q)) := by
  rw [gaussianHessian_eq_betaTrace A V₁ V₂ S hA c]
  exact betaTrace_brillouin hF g v₁ v₂ s hG hV₁ hV₂ hS

/-- **Reading the coefficient off the marginal term.**  If the polarisation
splits as `Π = β·M + R` and the remainder `R` is annihilated by the beta
projection (which `BetaProjection.mixedMomentumD_eq_zero_of_thirdOrder` supplies
for a third-order lattice-derivative remainder), then

    ∂_{p_μ}∂_{p_ν} Π (0) = β · ∂_{p_μ}∂_{p_ν} M (0).

No control of `Π` away from `p = 0` enters. -/
theorem beta_readoff_of_thirdOrder_remainder
    {Pi M R : (Fin 4 → ℝ) → ℝ} {mu nu : Fin 4} {beta : ℝ}
    (hdec : ∀ p, Pi p = beta * M p + R p)
    (hM : ∀ x : ℝ, DifferentiableAt ℝ (fun t => M (momentumSlice mu nu x t)) 0)
    (hR : ∀ x : ℝ, DifferentiableAt ℝ (fun t => R (momentumSlice mu nu x t)) 0)
    (hM' : DifferentiableAt ℝ
      (fun x => deriv (fun t => M (momentumSlice mu nu x t)) 0) 0)
    (hR' : DifferentiableAt ℝ
      (fun x => deriv (fun t => R (momentumSlice mu nu x t)) 0) 0)
    (hRzero : mixedMomentumD R mu nu = 0) :
    mixedMomentumD Pi mu nu = beta * mixedMomentumD M mu nu := by
  have hslice : (fun x t => Pi (momentumSlice mu nu x t))
      = fun x t => beta * M (momentumSlice mu nu x t) + R (momentumSlice mu nu x t) := by
    funext x t; exact hdec _
  have hbM : ∀ x : ℝ,
      DifferentiableAt ℝ (fun t => beta * M (momentumSlice mu nu x t)) 0 :=
    fun x => (hM x).const_mul _
  have hbM' : DifferentiableAt ℝ
      (fun x => deriv (fun t => beta * M (momentumSlice mu nu x t)) 0) 0 := by
    have he : (fun x : ℝ => deriv (fun t => beta * M (momentumSlice mu nu x t)) 0)
        = fun x : ℝ => beta * deriv (fun t => M (momentumSlice mu nu x t)) 0 := by
      funext x; exact deriv_const_mul_field _
    rw [he]
    exact hM'.const_mul _
  rw [mixedMomentumD, hslice, mixedD_add hbM hR hbM' hR',
    mixedD_const_mul beta fun x t => M (momentumSlice mu nu x t)]
  rw [mixedMomentumD] at hRzero
  rw [hRzero, add_zero, mixedMomentumD]

/-- **The read-off, end to end for a literal third-order remainder.**  If the
polarisation splits as `Π = β·M + R` and, on the slice spanned by the two
differentiated directions, the remainder is a product of three literal lattice
factors `p̂` with a smooth prefactor, then

    ∂_{p_μ}∂_{p_ν} Π (0) = β · ∂_{p_μ}∂_{p_ν} M (0)

with no hypothesis on `R` away from `p = 0`.  All differentiability side
conditions on `R` are discharged from the third-order structure itself. -/
theorem beta_readoff_thirdOrder
    {Pi M R : (Fin 4 → ℝ) → ℝ} {mu nu : Fin 4} {beta : ℝ} {g : ℝ → ℝ → ℝ} {a b : ℕ}
    (hdec : ∀ p, Pi p = beta * M p + R p) (hab : a + b = 3)
    (hRslice : ∀ x t : ℝ, R (momentumSlice mu nu x t) = phat x ^ a * (phat t ^ b * g x t))
    (hg : ∀ x, DifferentiableAt ℝ (fun t => g x t) 0)
    (hdg : DifferentiableAt ℝ (fun x => deriv (fun t => g x t) 0) 0)
    (hg0 : DifferentiableAt ℝ (fun x => g x 0) 0)
    (hM : ∀ x : ℝ, DifferentiableAt ℝ (fun t => M (momentumSlice mu nu x t)) 0)
    (hM' : DifferentiableAt ℝ
      (fun x => deriv (fun t => M (momentumSlice mu nu x t)) 0) 0) :
    mixedMomentumD Pi mu nu = beta * mixedMomentumD M mu nu := by
  have hR : ∀ x : ℝ, DifferentiableAt ℝ (fun t => R (momentumSlice mu nu x t)) 0 := by
    intro x
    have he : (fun t => R (momentumSlice mu nu x t))
        = fun t => phat x ^ a * (phat t ^ b * g x t) := by
      funext t; exact hRslice x t
    rw [he]
    exact slice_differentiableAt (differentiableAt_phat 0) hg a b x
  have hR' : DifferentiableAt ℝ
      (fun x => deriv (fun t => R (momentumSlice mu nu x t)) 0) 0 := by
    have he : (fun x : ℝ => deriv (fun t => R (momentumSlice mu nu x t)) 0)
        = fun x : ℝ => deriv (fun t => phat x ^ a * (phat t ^ b * g x t)) 0 := by
      funext x
      exact congrArg (fun f : ℝ → ℝ => deriv f 0) (funext fun t => hRslice x t)
    rw [he]
    exact thirdOrder_innerDeriv_differentiableAt phat_zero (differentiableAt_phat 0)
      hg hdg hg0 a b
  have hRzero : mixedMomentumD R mu nu = 0 :=
    mixedMomentumD_eq_zero_of_thirdOrder hab hRslice hg hdg hg0
  exact beta_readoff_of_thirdOrder_remainder hdec hM hR hM' hR' hRzero

end YangMills
