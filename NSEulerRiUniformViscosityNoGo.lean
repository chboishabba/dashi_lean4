import Mathlib

/-!
# Viscosity-uniform A3 estimate versus unforced Euler blowup

**Attribution.** Myong-Hwan Ri, arXiv:2601.15685v1 (2026-01-22),
Theorem 1.1, claimed (1.3) with C(s) independent of viscosity;
OpenAI, "Finite time blowup for the Euler equation" (2026-09-08),
released theorem `Euler.exists_compact_smooth_euler_singularity`,
https://github.com/openai/NavierStokesAndEuler.

This file proves ONLY the elementary **conditional incompatibility**:
pointwise inviscid convergence of a scalar H^s norm + uniform upper
bound for all viscosities contradict an unbounded Euler norm.
It does not manufacture the inviscid-limit theorem, embed H^s into C¹,
import OpenAI's Euler theorem, or establish/refute unforced NS A/B.
Those source-attachment obligations remain separate.
-/

namespace NSEulerRiUniformViscosityNoGo

/-- The limiting Euler norm inherits any viscosity-uniform bound at
every pre-singularity time when the corresponding viscous norms
converge to it there. -/
theorem limit_bound_from_uniform_viscosity
    {Time : Type*}
    (eulerNorm : Time → ℝ)
    (viscousNorm : ℕ → Time → ℝ)
    (bound : ℝ)
    (hviscous : ∀ n t, viscousNorm n t ≤ bound)
    (hinviscid : ∀ t, Filter.Tendsto
      (fun n => viscousNorm n t)
      Filter.atTop (nhds (eulerNorm t))) :
    ∀ t, eulerNorm t ≤ bound := by
  intro t
  exact le_of_tendsto (hinviscid t)
    (Filter.Eventually.of_forall (fun n => hviscous n t))

/-- If the Euler norm is unbounded along pre-blowup times, the claimed
universal upper bound and the stated inviscid-limit bridge cannot
both hold. This is *not* Euler blowup implying viscous blowup. -/
theorem euler_blowup_blocks_uniform_viscosity_bound
    {Time : Type*}
    (eulerNorm : Time → ℝ)
    (viscousNorm : ℕ → Time → ℝ)
    (bound : ℝ)
    (hviscous : ∀ n t, viscousNorm n t ≤ bound)
    (hinviscid : ∀ t, Filter.Tendsto
      (fun n => viscousNorm n t)
      Filter.atTop (nhds (eulerNorm t)))
    (heulerUnbounded : ∀ M : ℝ, ∃ t, M < eulerNorm t) :
    False := by
  have hbound := limit_bound_from_uniform_viscosity
    eulerNorm viscousNorm bound hviscous hinviscid
  obtain ⟨t, ht⟩ := heulerUnbounded bound
  exact (not_lt_of_ge (hbound t)) ht

end NSEulerRiUniformViscosityNoGo
