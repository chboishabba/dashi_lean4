/-!
Section35 original-source Hodge/BSD acceptance root.
Hodge: original affine saturation stable under chart-denominator
multiplication, but projective Chow globalization remains open.
BSD: strict original two-crossing Mellin m(n+2)>a*m(n+1), conditional
on original signed integral source and m0=0,m1>=0.
Actual Lean kernel and transitive axiom audit pending.
-/
import Synthesis.MillenniumHodgeDicksonOriginalDenominatorSaturationGlueExact
import Synthesis.MillenniumBSDOriginalTwoCrossingMellinGeometricFloorExact
#check DASHI.Hodge.DicksonCoupled.actual_affine_saturation_mul_denominator_iff
#check DASHI.Hodge.DicksonCoupled.actual_affine_saturation_has_original_denominator_glue
#check DASHI.BSD.SignedCrossing.original_two_crossing_moment_strict_a_growth
#check DASHI.BSD.SignedCrossing.original_two_crossing_no_sub_a_growth
#print axioms DASHI.Hodge.DicksonCoupled.actual_affine_saturation_has_original_denominator_glue
#print axioms DASHI.BSD.SignedCrossing.original_two_crossing_moment_strict_a_growth
