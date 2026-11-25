import Main
import Problems.RiemannHypothesis.Millennium

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
  Millennium.ClayRiemannHypothesis.of_mathlib _root_.riemannHypothesis

theorem original_clay_xi : Millennium.ClayRiemannHypothesis.Formulations.XiZeros :=
  Millennium.ClayRiemannHypothesis.xi_zeros original_clay_rh

theorem original_clay_mathlib_roundtrip : _root_.RiemannHypothesis :=
  Millennium.ClayRiemannHypothesis.mathlib original_clay_rh

#print axioms original_clay_rh
#print axioms original_clay_xi
#print axioms original_clay_mathlib_roundtrip

end DASHI.AlpogeRH
