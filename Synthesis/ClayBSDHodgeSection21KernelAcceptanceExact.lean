/-!
Section 21 native replay entrypoint for BSD/Hodge same-source owners.

This tests the actual general Weierstrass halving and genuine H¹
quotient dependency chain, alongside the schematic (not merely
pointwise) Hodge cone h-chart dependency chain.

It does NOT prove BSD analytic rank or the global Hodge conjecture.
-/
import Synthesis.MillenniumBSDGeneralGeometricDoublingExact
import Synthesis.MillenniumBSDGeneralPlaceKummerNaturalityExact
import Synthesis.MillenniumBSDGeneralKummerCosetExact
import Synthesis.MillenniumBSDActualTorsionTranslationCommutationExact
import Synthesis.MillenniumHodgeDicksonOriginalChartGeneratorExact
import Synthesis.MillenniumHodgeDicksonConeComponentKernelExact

#print axioms BSDCohomology.general_geometric_doubling_onto
#print axioms BSDCohomology.general_rationalKummer_sameCoset
#print axioms BSDCohomology.general_originalKummerExactAtH1
#print axioms DASHI.BSD.SplitTangent.splitRoot_translation_twice
#print axioms DASHI.Hodge.DicksonCoupled.original_cone_ideal_iff_degreewise_evaluation
#print axioms DASHI.Hodge.DicksonCoupled.original_chart_coordinate_has_homogeneous_lift
