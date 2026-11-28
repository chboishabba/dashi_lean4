import RHAdmission
import MillenniumExternal.AlpogeRHBoundaryExact

/-!
# Direct same-kernel exact Clay admission

Use the original pinned LeanDojo target and its OWN Mathlib RH equivalence
and entire-xi zero correspondence. This is the same constructor used by
MillenniumExternal/ExactTargetSurface.lean, without importing that file's
unrelated BSD/NS/PvNP dependencies. The target source is re-elaborated in
the selected original or licensed proof toolchain, never imported as an
incompatible olean. Its unproved final challenge declaration is not used.
The admission runner rejects any transitive sorryAx in these endpoints.
-/

namespace DASHI.AlpogeRH

theorem original_clay_rh : Millennium.ClayRiemannHypothesis :=
  MillenniumExternal.AlpogeRH.clay_of_admitted_mathlib original_mathlib_rh

theorem original_clay_xi : Millennium.ClayRiemannHypothesis.Formulations.XiZeros :=
  Millennium.ClayRiemannHypothesis.xi_zeros original_clay_rh

theorem original_clay_mathlib_roundtrip : _root_.RiemannHypothesis :=
  MillenniumExternal.AlpogeRH.mathlib_of_clay original_clay_rh

#print axioms original_clay_rh
#print axioms original_clay_xi
#print axioms original_clay_mathlib_roundtrip

end DASHI.AlpogeRH
