import Problems.PVersusNP.Millennium
import Problems.RiemannHypothesis.Millennium
import Problems.NavierStokes.Millennium
import Problems.BirchSwinnertonDyer.Millennium

/-!
# Exact pinned Millennium target surface under the DASHI kernel

This file is elaborated only with the pinned `vendor/LeanMillenniumPrizeProblems`
root added to `LEAN_PATH`.  The imported files are the exact upstream source at
commit `603053dc267cf3efe422f438eb78098c0ececd6f`; they are not copied or
restated here.

The purpose of this module is to distinguish a package/toolchain seam from a
mathematical seam.  If this file elaborates under the DASHI kernel, the exact
upstream propositions themselves are available in the same kernel as future
DASHI adapters.
-/

namespace MillenniumExternal

#check Millennium.ClayPVersusNP.Formulations.NegativeBranch
#check Millennium.ClayRiemannHypothesis
#check MillenniumNavierStokes.FeffermanA
#check MillenniumNavierStokes.FeffermanB
#check MillenniumNavierStokes.FeffermanC
#check MillenniumNavierStokes.FeffermanD
#check MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer

/-!
## Riemann-Hypothesis same-object target weld

LeanDojo proves its exact Clay critical-line proposition equivalent to
Mathlib's root `RiemannHypothesis`.  Hence no DASHI-specific zero carrier or
observer bridge is required at this boundary: once the standard Mathlib theorem
is produced, the exact pinned Clay proposition follows directly.
-/

theorem clayRiemannHypothesis_of_mathlib
    (h : _root_.RiemannHypothesis) :
    Millennium.ClayRiemannHypothesis :=
  Millennium.ClayRiemannHypothesis.of_mathlib h

theorem mathlibRiemannHypothesis_of_clay
    (h : Millennium.ClayRiemannHypothesis) :
    _root_.RiemannHypothesis :=
  Millennium.ClayRiemannHypothesis.mathlib h

theorem clayRiemannHypothesis_iff_mathlib :
    Millennium.ClayRiemannHypothesis ↔ _root_.RiemannHypothesis :=
  ⟨mathlibRiemannHypothesis_of_clay, clayRiemannHypothesis_of_mathlib⟩

#print axioms clayRiemannHypothesis_of_mathlib
#print axioms mathlibRiemannHypothesis_of_clay
#print axioms clayRiemannHypothesis_iff_mathlib

end MillenniumExternal
