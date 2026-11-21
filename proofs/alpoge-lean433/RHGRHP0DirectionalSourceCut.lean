import Statements
import Formalism.GammaFactorNonvanishing.CritLine
import Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip
import Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacter
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VwinOfRow
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc

/-!
# P0 directional source bridge: original all-character target → exact RH

This is a source-level recomposition of existing pinned Alpöge/Claude
Lean 4.33.1 declarations (no imported source code is redistributed).

The original Claim.HalfPlane / UpperTheory.EveryCharacter share a
definition; Claim.Zeta is exactly equivalent to Mathlib RH. By contrast
RH does NOT have a sourced reverse implication to EveryCharacter/GRH.
The statements here use ORIGINAL number-theoretic targets, not
cyclotomic C3 zero labels, Monster VOA 3B characters or G2 replacements.

The source row and theta/Galois witnesses remain the original fork's.
Their compatible 4.33.1 kernel replay is not performed here.
-/-

namespace DASHI.AlpogeRH.P0Directional

/-- Same *original* all-character statement under its two source names. -/
theorem halfplane_iff_original_all_character :
    Claim.HalfPlane ↔ UpperTheory.EveryCharacter := Iff.rfl

/-- Original plain zeta claim is the precise Mathlib RH proposition. -/
theorem original_zeta_iff_rh :
    Claim.Zeta ↔ RiemannHypothesis := Claim.zeta_iff

/-- All-character nonvanishing is sufficient for the ordinary zeta claim. -/
theorem zeta_of_every_character (h : UpperTheory.EveryCharacter) :
    Claim.Zeta :=
  original_zeta_iff_rh.mpr (Formalism.VW.rh_of_every h)

/-- Reverse ONLY at the zeta/RH target: does not infer all characters. -/
theorem rh_of_original_zeta (h : Claim.Zeta) :
    RiemannHypothesis := original_zeta_iff_rh.mp h

theorem original_zeta_of_rh (h : RiemannHypothesis) :
    Claim.Zeta := original_zeta_iff_rh.mpr h

/-- The original indexed RowSrc source yields the all-character premise
through the same source combinator as MainConclusion. -/
theorem every_character_of_original_galois_row :
    UpperTheory.EveryCharacter :=
  UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin
    ⟨ UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
    , UpperTheory.Zero.LLC.recTExists
    , UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter ⟩
    (UpperTheory.One.vwin_of_row
      UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter)

/-- Terminal P0 ordinary RH from the actual original all-character row. -/
theorem rh_of_original_galois_row : RiemannHypothesis :=
  Formalism.VW.rh_of_every every_character_of_original_galois_row

/-- Terminal P0 source zeta target, on the same source claim. -/
theorem zeta_of_original_galois_row : Claim.Zeta :=
  zeta_of_every_character every_character_of_original_galois_row

/-- The original all-character source, not merely zeta GRH-like notation,
also supplies the original Dirichlet right-half nonvanishing target. -/
theorem dirichlet_right_half_of_original_galois_row :
    DirichletLNonvanishingRightOfHalf :=
  every_character_of_original_galois_row

/-- The precise original strip consumer, retaining every-character scope. -/
theorem dirichlet_strip_of_original_galois_row :
    DirichletLZerosOnLine :=
  Claim.strip every_character_of_original_galois_row

/-- The precise primitive Dirichlet critical-line consumer. -/
theorem primitive_strip_of_original_galois_row :
    PrimitiveDirichletLZerosOnLine :=
  Formalism.VW.critLine every_character_of_original_galois_row

#print axioms halfplane_iff_original_all_character
#print axioms original_zeta_iff_rh
#print axioms every_character_of_original_galois_row
#print axioms rh_of_original_galois_row
#print axioms dirichlet_right_half_of_original_galois_row
#print axioms dirichlet_strip_of_original_galois_row
#print axioms primitive_strip_of_original_galois_row

end DASHI.AlpogeRH.P0Directional
