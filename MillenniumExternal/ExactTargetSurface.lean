import Problems.PVersusNP.Millennium
import Problems.RiemannHypothesis.Millennium
import Problems.NavierStokes.Millennium
import Problems.BirchSwinnertonDyer.Millennium
import Synthesis.RiemannSelectedRHMaxCutFrontier
import Synthesis.MillenniumBSDUniversalRankWeld
import NSBControl.CombinedCurrentEndgame

/-!
# Exact pinned Millennium target surface under the DASHI kernel

This file is elaborated only with the pinned `vendor/LeanMillenniumPrizeProblems`
root added to `LEAN_PATH`. The imported `Problems.*` files are the exact upstream
source at commit `603053dc267cf3efe422f438eb78098c0ececd6f`; they are not copied
or restated here.

The same elaboration also imports the strongest root-package DASHI donors. Thus
successful elaboration proves more than registry-name agreement: the exact
external propositions and the DASHI theorem surfaces coexist in one Lean
environment, ready for literal same-object adapter terms.
-/

namespace MillenniumExternal

/-! ## Exact external declarations -/

#check Millennium.ClayPVersusNP.Formulations.NegativeBranch
#check Millennium.ClayRiemannHypothesis
#check MillenniumNavierStokes.FeffermanA
#check MillenniumNavierStokes.FeffermanB
#check MillenniumNavierStokes.FeffermanC
#check MillenniumNavierStokes.FeffermanD
#check MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer

/-! ## Existing DASHI same-object / terminal donors in the same elaboration -/

#check Synthesis.QuarticFourSignedPolePair.RHMaxCutRoute.signedFifth_terminalPositive
#check Synthesis.Millennium.BSD.universalBSDRankTheorem_of_background
#check Synthesis.Millennium.BSD.universalBSDRankTheorem_of_producers
#check NSBControl.CombinedCurrentEndgame.current_three_coordinate_endgame

/-!
## Riemann-Hypothesis exact statement weld

LeanDojo proves its exact Clay critical-line proposition equivalent to
Mathlib's root `RiemannHypothesis`. Hence no DASHI-specific zero carrier or
observer bridge is required at this boundary: once the standard Mathlib theorem
is produced, the exact pinned Clay proposition follows directly, and conversely.
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

/-!
## Exact remaining target shapes

These checks keep the external endpoint visible beside the existing producer.
No extra implication is manufactured here: P-vs-NP currently has its strongest
Clay-core producer in Agda; Navier-Stokes has a stronger independent literal C/D
nested Lean project; and BSD's local universal rank weld must still be composed
with the exact external continuation/Taylor-data surface.
-/

#check Millennium.ClayPVersusNP.Formulations.NegativeBranch
#check MillenniumNavierStokes.FeffermanC
#check MillenniumNavierStokes.FeffermanD
#check MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer
#check MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer.iff_rank_existence_and_finite_rank

end MillenniumExternal
