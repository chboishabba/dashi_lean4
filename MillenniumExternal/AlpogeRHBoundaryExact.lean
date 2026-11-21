import MillenniumExternal.ExactTargetSurface

/-!
# RH/Clay precise terminal handoff — source-independent and bidirectional

The external Alpöge Lean v4.33.1 submission defines
`Main.riemannHypothesis : Mathlib.RiemannHypothesis`.
This local file deliberately **does not import the unlicensed submission**,
nor assume that a theorem name in another toolchain is a proof.

Once the source-pinned v4.33.1 module has been independently admitted and
a trusted *same-theorem* witness is made available in this environment, the
existing pinned Millennium target compiler closes the original Clay statement.
Both directions use the existing LeanDojo ↔ Mathlib weld, not another RH
proposition or a substitute zero carrier.

Source owner: MillenniumExternal.ExactTargetSurface.
-/-

namespace MillenniumExternal.AlpogeRH

/-- Forward solve: a real Mathlib RH proof pays the existing exact Clay target. -/
theorem clay_of_admitted_mathlib
    (admitted : _root_.RiemannHypothesis) :
    Millennium.ClayRiemannHypothesis :=
  MillenniumExternal.clayRiemannHypothesis_of_mathlib admitted

/-- Reverse solve: the exact Clay target returns to the *same* Mathlib RH. -/
theorem mathlib_of_clay
    (clay : Millennium.ClayRiemannHypothesis) :
    _root_.RiemannHypothesis :=
  MillenniumExternal.mathlibRiemannHypothesis_of_clay clay

/-- Actual two-way statement identity; no missing analytic premise is smuggled in. -/
theorem clay_iff_mathlib :
    Millennium.ClayRiemannHypothesis ↔ _root_.RiemannHypothesis :=
  MillenniumExternal.clayRiemannHypothesis_iff_mathlib

#print axioms clay_of_admitted_mathlib
#print axioms mathlib_of_clay
#print axioms clay_iff_mathlib

end MillenniumExternal.AlpogeRH
