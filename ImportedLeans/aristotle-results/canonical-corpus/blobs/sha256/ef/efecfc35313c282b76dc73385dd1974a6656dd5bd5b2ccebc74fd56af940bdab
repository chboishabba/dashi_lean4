/-
# Trace/norm descent: the canonical real-valued observer on the ternary phase

The `C₃` phase carrier `{1, ζ, ζ²}` is not real.  The two elementary invariants
of the conjugation involution — trace `z ↦ z + z̄` and norm `z ↦ z z̄` — are the
canonical descent maps to `ℝ`, and both are degree ≤ 2 in the transverse
coordinate.

Model.  `ℚ(ζ₃) = {u + vζ : u, v ∈ ℚ}`, realised concretely inside `ℂ`.  In these
coordinates

    conj (u + vζ) = (u − v) − vζ,   Tr = 2u − v,   N = u² − uv + v².

Main results.

* `Spine.Cyc.conj_mk`, `Spine.Cyc.trace_mk`, `Spine.Cyc.norm_mk` — the formulas.
* `Spine.Cyc.mul_conj_eq_norm` — `z z̄` lands on the rational (fixed) axis.
* `Spine.Cyc.norm_nonneg`, `Spine.Cyc.norm_eq_zero_iff` — the norm form is
  positive definite, so it is a genuine amplitude, not a degenerate observable.
* `Spine.Cyc.conj_fixed_iff_rational` — **the sharp caveat, proved rather than
  asserted**: the elements fixed by conjugation are exactly the rationals.  The
  maximal real subfield of `ℚ(ζ₃)` is `ℚ`, so phases alone give nothing
  continuous; a real-valued continuum has to come from amplitudes.
-/
import Mathlib
import Spine.TernaryPhase

open Complex ComplexConjugate

namespace Spine
namespace Cyc

/-- `u + vζ`, the generic element of `ℚ(ζ₃)` in the basis `{1, ζ}`. -/
noncomputable def mk (u v : ℚ) : ℂ := (u : ℂ) + (v : ℂ) * zeta

theorem zeta_sq_eq : zeta ^ 2 = -1 - zeta := by linear_combination zeta_sum

theorem zeta_re : zeta.re = -(1 / 2) := by
  simp [zeta]
  norm_num

theorem zeta_im : zeta.im = Real.sqrt 3 / 2 := by
  simp [zeta]

theorem mk_re (u v : ℚ) : (mk u v).re = (u : ℝ) - (v : ℝ) / 2 := by
  simp [mk, zeta_re]; ring

theorem mk_im (u v : ℚ) : (mk u v).im = (v : ℝ) * (Real.sqrt 3 / 2) := by
  simp [mk, zeta_im, zeta_re]

/-- `{1, ζ}` is a basis: the coordinates are determined by the element. -/
theorem mk_injective {u v u' v' : ℚ} (h : mk u v = mk u' v') : u = u' ∧ v = v' := by
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  rw [mk_im, mk_im] at him
  rw [mk_re, mk_re] at hre
  have hs : (Real.sqrt 3 / 2 : ℝ) ≠ 0 := by positivity
  have hv : (v : ℝ) = (v' : ℝ) := mul_right_cancel₀ hs him
  have hv' : v = v' := by exact_mod_cast hv
  refine ⟨?_, hv'⟩
  rw [hv] at hre
  have : (u : ℝ) = (u' : ℝ) := by linarith
  exact_mod_cast this

/-- Conjugation in coordinates. -/
theorem conj_mk (u v : ℚ) : conj (mk u v) = mk (u - v) (-v) := by
  have h2 : zeta ^ 2 = -1 - zeta := zeta_sq_eq
  simp only [mk, map_add, map_mul, conj_zeta, h2, map_ratCast]
  push_cast
  ring

/-- The trace observable `z + z̄ = 2u − v`, a rational number. -/
theorem trace_mk (u v : ℚ) : mk u v + conj (mk u v) = ((2 * u - v : ℚ) : ℂ) := by
  rw [conj_mk]
  simp only [mk]
  push_cast
  ring

/-- The norm observable `z z̄ = u² − uv + v²`, a rational number: multiplying by
the conjugate lands on the fixed axis. -/
theorem mul_conj_eq_norm (u v : ℚ) :
    mk u v * conj (mk u v) = ((u ^ 2 - u * v + v ^ 2 : ℚ) : ℂ) := by
  have h2 : zeta ^ 2 = -1 - zeta := zeta_sq_eq
  rw [conj_mk]
  simp only [mk]
  push_cast
  linear_combination ((v : ℂ) * (-v)) * h2

/-- The norm form is positive semidefinite. -/
theorem norm_nonneg (u v : ℚ) : 0 ≤ u ^ 2 - u * v + v ^ 2 := by
  nlinarith [sq_nonneg (u - v), sq_nonneg (u + v), sq_nonneg u, sq_nonneg v]

/-- …and positive definite: the norm is a nondegenerate amplitude observable. -/
theorem norm_eq_zero_iff (u v : ℚ) : u ^ 2 - u * v + v ^ 2 = 0 ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (u - v), sq_nonneg (u + v), sq_nonneg u, sq_nonneg v]
  · rintro ⟨hu, hv⟩; subst hu; subst hv; ring

/-- **The sharp caveat.**  An element of `ℚ(ζ₃)` is fixed by conjugation exactly
when its transverse coordinate vanishes, i.e. exactly when it is rational.  So
the maximal real subfield of `ℚ(ζ₃)` is `ℚ`: the ternary phases alone produce no
continuum of real observables — that requires amplitudes. -/
theorem conj_fixed_iff_rational (u v : ℚ) : conj (mk u v) = mk u v ↔ v = 0 := by
  constructor
  · intro h
    rw [conj_mk] at h
    have := (mk_injective h).2
    linarith
  · intro h
    subst h
    rw [conj_mk]
    norm_num

/-- Equivalently: `mk u v` is a real number exactly when `v = 0`. -/
theorem im_eq_zero_iff (u v : ℚ) : (mk u v).im = 0 ↔ v = 0 := by
  rw [mk_im]
  constructor
  · intro h
    have hs : Real.sqrt 3 ≠ 0 := by positivity
    have : (v : ℝ) = 0 := by
      rcases mul_eq_zero.mp h with h1 | h1
      · exact h1
      · exact absurd (by linarith [h1] : Real.sqrt 3 = 0) hs
    exact_mod_cast this
  · intro h; subst h; simp

end Cyc
end Spine
