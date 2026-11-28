/-!
Section 21 native replay entrypoint for the original NS pressure path.

Compile this whole file under the original Lean/Mathlib lockfile.
All imports are in the same NS PR branch; no shadow axioms, sorry or
new theorem assumptions are introduced by this acceptance root.

Build failure is a genuine source issue, not permission to weaken a
theorem. Full physical PDE and critical regularity remain separate.
-/
import Synthesis.NavierStokesOriginalJointModalWitnessExact
import Synthesis.NavierStokesOriginalModalPressureEnvelopeExact
import Synthesis.NavierStokesOriginalRawConvectionSummabilityExact
import Synthesis.NavierStokesPressureCellBilinearDifferenceExact
import Synthesis.NavierStokesPressureCellSeriesExact

#print axioms DASHI.NavierStokes.PhysicalMixed.original_energy_product_summable
#print axioms DASHI.NavierStokes.PhysicalMixed.original_modal_pressure_envelope_from_energy
#print axioms DASHI.NavierStokes.PhysicalMixed.original_raw_convection_summable
#print axioms DASHI.NavierStokes.EuclideanMidpoint.pressureCell_bilinear_difference
#print axioms DASHI.NavierStokes.EuclideanMidpoint.pressure_series_split
