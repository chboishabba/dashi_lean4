import Mathlib.Analysis.ODE.ExistUnique

/-!
# R830 standard local ODE existence max-cut

Mathlib already proves the analytic local-existence theorem needed by R830:
a C¹ autonomous vector field on a real Banach space has a local integral
curve through every initial state.

This file exposes exactly that theorem in the shape consumed by the rational
3-4-5 Navier--Stokes decision route.  The only remaining R830 ODE-specific
task is therefore to prove that the concrete radius-four Galerkin polynomial
vector field is C¹ at the selected initial state and to connect the quantitative
bootstrap constants to that solution.
-/

open Set

namespace NSBControl
namespace Rational345LocalODE

/-- Generic real-Banach local solution for an autonomous C¹ field. -/
theorem exists_local_solution
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {field : E → E} {u₀ : E}
    (hfield : ContDiffAt ℝ 1 field u₀) :
    ∃ (u : ℝ → E),
      u 0 = u₀ ∧
      ∃ ε > 0,
        ∀ t ∈ Ioo (-ε) ε,
          HasDerivAt u (field (u t)) t := by
  simpa using
    hfield.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0

/-- The local solution supplied by the C¹ theorem is continuous on its
existence interval. -/
theorem local_solution_continuousOn
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {field : E → E} {u : ℝ → E} {ε : ℝ}
    (hderiv :
      ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt u (field (u t)) t) :
    ContinuousOn u (Ioo (-ε) ε) := by
  intro t ht
  exact (hderiv t ht).continuousAt.continuousWithinAt

end Rational345LocalODE
end NSBControl
