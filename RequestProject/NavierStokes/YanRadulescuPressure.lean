import Mathlib

/-!
# Yan–Rădulescu (2021): source-audited stationary pressure obligation

Source: Weiping Yan and Vicenţiu D. Rădulescu,
"Sobolev regular solutions for the incompressible Navier–Stokes
equations in higher dimensions: asymptotics and representation formulae",
Rend. Circ. Mat. Palermo II. Ser. 70 (2021), 995–1021.
DOI 10.1007/s12215-020-00540-3. Compare Eqs. (1.1) and (1.3).

The steady *forced* equation gives
  -ν Δ(div U) + div((U·∇)U) + ΔP = div f.
With div U = 0, the force-divergence term generally survives.
The paper displays the pressure identity without this term even
though Theorem 1.1 as printed allows generic small forcing.

This file certifies the finite scalar algebra required by the
pressure consistency check. It does NOT claim to have formalised
differential operators, the existence theorem, elliptic boundary
conditions or the full Nash–Moser iteration.
-/

namespace RequestProject.NavierStokes.YanRadulescu

/-- The forced stationary divergence balance cannot discard div(f)
without an additional hypothesis. The variables represent separately
typed analytic quantities only AFTER the PDE-facing bridge pays for them. -/
theorem forced_stationary_pressure_balance
    (ν lapDivU convectionDiv pressureLap forceDiv : ℝ)
    (hSteady :
      -ν * lapDivU + convectionDiv + pressureLap = forceDiv)
    (hSolenoidal : lapDivU = 0) :
    pressureLap = forceDiv - convectionDiv := by
  rw [hSolenoidal] at hSteady
  nlinarith

/-- The printed zero-divergence-forcing formula is a conditional corollary. -/
theorem stationary_pressure_balance_if_solenoidal_force
    (ν lapDivU convectionDiv pressureLap forceDiv : ℝ)
    (hSteady :
      -ν * lapDivU + convectionDiv + pressureLap = forceDiv)
    (hSolenoidal : lapDivU = 0)
    (hDivForce : forceDiv = 0) :
    pressureLap = -convectionDiv := by
  have h := forced_stationary_pressure_balance ν lapDivU
    convectionDiv pressureLap forceDiv hSteady hSolenoidal
  rw [hDivForce] at h
  linarith

/-- A force-divergence-free conclusion implies force divergence must
actually vanish if the same pressure and convection quantities satisfy
the general forced equation. -/
theorem unqualified_pressure_simplification_requires_divFree_force
    (ν lapDivU convectionDiv pressureLap forceDiv : ℝ)
    (hSteady :
      -ν * lapDivU + convectionDiv + pressureLap = forceDiv)
    (hSolenoidal : lapDivU = 0)
    (hSimplified : pressureLap = -convectionDiv) :
    forceDiv = 0 := by
  have h := forced_stationary_pressure_balance ν lapDivU
    convectionDiv pressureLap forceDiv hSteady hSolenoidal
  linarith

/-- The chosen coefficients (1,1,-2) make the three displayed
coordinate derivatives cancel if they share the same product. This
is the finite algebraic precursor to the concrete cube witness of
Corollary 1.1, NOT the missing analytic derivative/boundary proof. -/
theorem symmetric_cyclic_derivative_cancellation (g ε : ℝ) :
    ε * g + ε * g + (-2 * ε) * g = 0 := by
  ring

end RequestProject.NavierStokes.YanRadulescu
