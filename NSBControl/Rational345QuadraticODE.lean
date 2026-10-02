import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.Comp
import NSBControl.Rational345LocalODE

/-!
# R830 quadratic-vector-field max-cut

Round71 already constructs the autonomous finite Galerkin vector field. Its
remaining standard analytic obligation is to exhibit the real-coordinate field
as linear plus bilinear (hence degree at most two). Mathlib's bounded-linear and
bounded-bilinear calculus then makes the field C¹ automatically, and the
Picard--Lindelöf owner supplies a local integral curve.

Thus the Navier--Stokes-specific residue after this file is only the concrete
coordinate identification and the explicit R828 bootstrap constants.
-/

namespace NSBControl
namespace Rational345QuadraticODE

/-- A linear plus bounded-bilinear diagonal field is C¹. -/
theorem contDiff_quadraticField
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (linear : E →L[ℝ] E)
    (bilinear : E × E → E)
    (hbilinear : IsBoundedBilinearMap ℝ bilinear) :
    ContDiff ℝ 1 (fun x : E => linear x + bilinear (x, x)) := by
  have hdiag : ContDiff ℝ 1 (fun x : E => (x, x)) :=
    contDiff_id.prodMk contDiff_id
  have hquad : ContDiff ℝ 1 (fun x : E => bilinear (x, x)) :=
    hbilinear.contDiff.comp hdiag
  exact linear.contDiff.add hquad

/-- Local real-time solution for every linear+quadratic finite-dimensional
Galerkin template. -/
theorem exists_local_solution_quadraticField
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (linear : E →L[ℝ] E)
    (bilinear : E × E → E)
    (hbilinear : IsBoundedBilinearMap ℝ bilinear)
    (u₀ : E) :
    ∃ (u : ℝ → E),
      u 0 = u₀ ∧
      ∃ ε > 0,
        ∀ t ∈ Set.Ioo (-ε) ε,
          HasDerivAt u (linear (u t) + bilinear (u t, u t)) t := by
  apply Rational345LocalODE.exists_local_solution
  exact (contDiff_quadraticField linear bilinear hbilinear).contDiffAt

end Rational345QuadraticODE
end NSBControl
