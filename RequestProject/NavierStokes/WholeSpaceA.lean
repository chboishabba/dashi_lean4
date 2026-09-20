import RequestProject.NavierStokes.WholeSpaceCubatureBoundaryDefect
import RequestProject.NavierStokes.WholeSpaceL1BochnerCompletion
import RequestProject.NavierStokes.WholeSpaceL1Tail

/-!
# Navier–Stokes whole-space A analytic producer

This opt-in Lean library owns only concrete Mathlib analysis for the independent
R³ construction of Clay alternative A.  The canonical statement and semantic
firewall remain in dashi_agda.

Current payments:
* finite weighted translation-boundary defect:
  |Δₙ| ≤ Eₙ τₙ;
* scalar energy integral convergence from L¹ approximation;
* coherent six-real-coordinate C³ Bochner integral convergence from L¹
  approximation.

No global regularity or Clay inhabitant is asserted here.
-/
