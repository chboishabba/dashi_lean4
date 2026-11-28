import RHAdmission
import MillenniumExternal.AlpogeRHBoundaryExact
import MillenniumExternal.AlpogeRHUniversalXiZetaBidiExact

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

/-- Actual universal subtype endpoints, consuming the pinned source
theorem rather than the earlier conditional zero-carrier equivalence. -/
theorem original_all_zeta_subtype_critical :
    ∀ s : {s : ℂ // Millennium.IsNontrivialZero s}, s.1.re=(1/2:ℝ) :=
  fun s => original_clay_rh.zero_re_eq_half s.2

theorem original_all_xi_subtype_axis :
    ∀ t : {t : ℂ // Millennium.xi t=0},t.1.im=0 :=
  MillenniumExternal.AlpogeRH.originalAllXiZerosAxis_iff_allNontrivialZetaCritical.mpr
    original_all_zeta_subtype_critical

#print axioms original_all_zeta_subtype_critical
#print axioms original_all_xi_subtype_axis
#print axioms original_clay_rh
#print axioms original_clay_xi
#print axioms original_clay_mathlib_roundtrip

end DASHI.AlpogeRH
