import Problems.PVersusNP.Millennium
import Problems.RiemannHypothesis.Millennium
import Problems.NavierStokes.Millennium
import Problems.Hodge.Millennium
import Problems.BirchSwinnertonDyer.Millennium
import Problems.YangMills.Millennium
import Problems.Poincare.Millennium
import Synthesis.RiemannSelectedRHMaxCutFrontier
import Synthesis.MillenniumBSDUniversalRankWeld
import Synthesis.MillenniumBSDProjectiveRankWeld
import NSBControl.CombinedCurrentEndgame
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Exact pinned Millennium target surface under the DASHI kernel

This file is elaborated only with the pinned `vendor/LeanMillenniumPrizeProblems`
root added to `LEAN_PATH`. The imported `Problems.*` files are the exact upstream
source at commit `603053dc267cf3efe422f438eb78098c0ececd6f`; they are not copied
or restated here.
-/

namespace MillenniumExternal

#check Millennium.ClayPVersusNP.Formulations.NegativeBranch
#check Millennium.ClayRiemannHypothesis
#check MillenniumNavierStokes.FeffermanA
#check MillenniumNavierStokes.FeffermanB
#check MillenniumNavierStokes.FeffermanC
#check MillenniumNavierStokes.FeffermanD
#check MillenniumHodge.ClayHodge
#check MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer
#check MillenniumYangMills.ClayYangMills
#check MillenniumPoincare.ClayPoincareConjecture

#check Synthesis.QuarticFourSignedPolePair.RHMaxCutRoute.signedFifth_terminalPositive
#check Synthesis.Millennium.BSD.universalBSDRankTheorem_of_background
#check Synthesis.Millennium.BSD.universalBSDRankTheorem_of_producers
#check Synthesis.Millennium.BSD.projective_rank_carrier_paid
#check NSBControl.CombinedCurrentEndgame.current_three_coordinate_endgame

/-! ## P versus NP exact negative-branch compiler -/

theorem clayPNotEqualsNP_of_language_outside_p
    {alphabet : Type} [Fintype alphabet] [Nontrivial alphabet]
    (L : Millennium.Language (List alphabet))
    (hNP : Millennium.InNondeterministicPolynomialTime
      (Millennium.fin_encoding_string alphabet) L)
    (hNotP : Millennium.InPolynomialTime
      (Millennium.fin_encoding_string alphabet) L → False) :
    Millennium.ClayPVersusNP.Formulations.NegativeBranch := by
  change ¬ Millennium.ClayPVersusNP.Formulations.ClassEquality
  intro hEq
  exact hNotP ((hEq alphabet L).2 hNP)

#print axioms clayPNotEqualsNP_of_language_outside_p

/-! ## Riemann-Hypothesis exact statement weld -/

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

/-! ## Birch--Swinnerton-Dyer exact target compiler -/

abbrev LeanDojoBSDFiniteRank : Prop :=
  ∀ W : WeierstrassCurve ℤ, ∀ _hΔ : W.Δ ≠ 0,
    WeierstrassCurve.rank (W.baseChange ℚ) ≠ (⊤ : ℕ∞)

/-- A finitely generated projective Mordell--Weil group has finite LeanDojo
`ENat` rank.  This is pure Mathlib algebra: finite generation descends to the
torsion quotient, scalar extension to `ℚ` is finite, hence the vector-space
rank is below `aleph0`, exactly the condition for `Cardinal.toENat ≠ top`. -/
theorem leanDojoRank_finite_of_projective_fg
    (E : WeierstrassCurve ℚ)
    (hFG : AddGroup.FG E.toProjective.Point) :
    WeierstrassCurve.rank E ≠ (⊤ : ℕ∞) := by
  let G : Type := E.toProjective.Point
  letI : AddCommGroup G := inferInstance
  letI : AddGroup.FG G := by simpa [G] using hFG
  let T : AddSubgroup G := AddCommGroup.torsion G
  letI : AddGroup.FG (G ⧸ T) :=
    AddGroup.fg_of_surjective (QuotientAddGroup.mk' T)
      (QuotientAddGroup.mk'_surjective T)
  letI : Module.Finite ℤ (G ⧸ T) :=
    (Module.Finite.iff_addGroup_fg).2 (by infer_instance)
  letI : Module.Finite ℚ (TensorProduct ℤ ℚ (G ⧸ T)) :=
    Module.Finite.base_change ℤ ℚ (G ⧸ T)
  unfold WeierstrassCurve.rank WeierstrassCurve.MordellWeilGroup
  change Cardinal.toENat (Module.rank ℚ (TensorProduct ℤ ℚ (G ⧸ T))) ≠ ⊤
  exact Cardinal.toENat_ne_top.mpr (Module.rank_lt_aleph0 ℚ _)

/-- The existing DASHI Mordell--Weil binding therefore pays LeanDojo's entire
finite-rank side.  The affine/projective same-object transport is consumed via
`projective_fg`; no independent finite-rank hypothesis remains. -/
theorem leanDojoBSDFiniteRank_of_dashi
    (m : Synthesis.Millennium.BSD.BSDMordellWeilRankBinding) :
    LeanDojoBSDFiniteRank := by
  intro W hΔ
  let E : Synthesis.Millennium.BSD.RationalEllipticCurve :=
    ⟨W.baseChange ℚ,
      WeierstrassCurve.is_elliptic_base_change_q W hΔ⟩
  apply leanDojoRank_finite_of_projective_fg (W.baseChange ℚ)
  simpa [E] using m.projective_fg E

/-- Only the rank-existence/analytic-continuation transport remains in the BSD
same-object compiler.  Finite rank is derived automatically from the algebraic
binding already carried by `bg`. -/
structure BSDLeanDojoSameObjectWeld
    (bg : Synthesis.Millennium.BSD.BSDEstablishedBackground) : Prop where
  rankExistence_of_dashi :
    Synthesis.Millennium.BSD.BSDClayCoreObligation bg →
      MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer.Formulations.Rank.Existence

/-- Once the existing DASHI BSD core theorem is transported onto LeanDojo's
literal integral/L-series carrier, upstream's own equivalence closes the exact
Clay target.  Finite Mordell--Weil rank is no longer a field of the adapter. -/
theorem clayBirchSwinnertonDyer_of_dashi
    {bg : Synthesis.Millennium.BSD.BSDEstablishedBackground}
    (w : BSDLeanDojoSameObjectWeld bg)
    (hRank : Synthesis.Millennium.BSD.BSDClayCoreObligation bg) :
    MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer :=
  MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer.of_rank_existence_and_finite_rank
    ⟨w.rankExistence_of_dashi hRank,
      leanDojoBSDFiniteRank_of_dashi bg.algebraic⟩

#print axioms leanDojoRank_finite_of_projective_fg
#print axioms leanDojoBSDFiniteRank_of_dashi
#print axioms clayBirchSwinnertonDyer_of_dashi

#check Millennium.ClayPVersusNP.Formulations.NegativeBranch
#check MillenniumNavierStokes.FeffermanC
#check MillenniumNavierStokes.FeffermanD
#check MillenniumHodge.ClayHodge
#check MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer
#check MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer.iff_rank_existence_and_finite_rank
#check MillenniumYangMills.ClayYangMills
#check MillenniumPoincare.ClayPoincareConjecture

end MillenniumExternal
