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
## Birch--Swinnerton-Dyer exact target compiler

Upstream already proves that its exact Clay Taylor statement is equivalent to
rank-existence plus finite Mordell--Weil rank.  DASHI already owns the actual
same-curve analytic/algebraic rank weld.  What remains at this boundary is
therefore typed explicitly as two same-object transports:

1. compile the DASHI core rank equality into LeanDojo's integral-model
   `Rank.Existence` carrier (including its exact analytic-continuation data);
2. identify DASHI's finite-generation/free-rank carrier with LeanDojo's
   projective Mordell--Weil `ENat` rank sufficiently to prove it is not `top`.

No Taylor-series argument is duplicated here.
-/

abbrev LeanDojoBSDFiniteRank : Prop :=
  ∀ W : WeierstrassCurve ℤ, ∀ _hΔ : W.Δ ≠ 0,
    WeierstrassCurve.rank (W.baseChange ℚ) ≠ (⊤ : ℕ∞)

structure BSDLeanDojoSameObjectWeld
    (bg : Synthesis.Millennium.BSD.BSDEstablishedBackground) : Prop where
  rankExistence_of_dashi :
    Synthesis.Millennium.BSD.BSDClayCoreObligation bg →
      MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer.Formulations.Rank.Existence
  finiteRank : LeanDojoBSDFiniteRank

/-- Once the existing DASHI BSD core theorem is transported onto LeanDojo's
literal integral/L-series carrier, upstream's own equivalence closes the exact
Clay target. -/
theorem clayBirchSwinnertonDyer_of_dashi
    {bg : Synthesis.Millennium.BSD.BSDEstablishedBackground}
    (w : BSDLeanDojoSameObjectWeld bg)
    (hRank : Synthesis.Millennium.BSD.BSDClayCoreObligation bg) :
    MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer :=
  MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer.of_rank_existence_and_finite_rank
    ⟨w.rankExistence_of_dashi hRank, w.finiteRank⟩

#print axioms clayBirchSwinnertonDyer_of_dashi

/-!
## Exact remaining target shapes

These checks keep the external endpoint visible beside the existing producer.
No extra implication is manufactured here: P-vs-NP currently has its strongest
Clay-core producer in Agda; Navier-Stokes has a stronger independent literal C/D
nested Lean project; and BSD's remaining adapter is the same-object weld above.
-/

#check Millennium.ClayPVersusNP.Formulations.NegativeBranch
#check MillenniumNavierStokes.FeffermanC
#check MillenniumNavierStokes.FeffermanD
#check MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer
#check MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer.iff_rank_existence_and_finite_rank

end MillenniumExternal
