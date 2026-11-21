import Statements
import Formalism.GammaFactorNonvanishing.CritLine
import Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VwinOfRow
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc

/-!
# Source-identical SELECTIVE producer composition (P0 experiment)

The original `MainConclusion` adds an import of
`RiemannHypothesisOfEveryCharacter` (whose own source imports a very
large number of files). This candidate imports only the named actual
providers of the `everyCharacter_of_row` proof and the finite final
`VW.rh_of_every`, `Claim.strip`, and `Claim.zeta` steps.

This does NOT reprove the automorphic/theta theorem and does NOT replace
`galoisLocalGlobalStrong_recParameter`: it consumes exactly the
original fork's existing producer and the *same term structure*
of `MainConclusion.everyCharacter_of_row`.

It is a **selective direct-import experiment, NOT typechecked yet**.
Lean may reveal hidden needed dependencies; fail closed and record the
exact missing module rather than manufacturing assumptions.
-/

namespace DASHI.AlpogeRH.Selective

/-- Same underlying source theorem term as
`UpperTheory.FinalTheorems.everyCharacter_of_row`, but without importing
that wrapper's unrelated RiemannHypothesisOfEveryCharacter module. -/
theorem every_character_from_original_row :
    UpperTheory.EveryCharacter :=
  UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin
    ⟨ UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
    , UpperTheory.Zero.LLC.recTExists
    , UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter ⟩
    (UpperTheory.One.vwin_of_row
      UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter)

/-- Original `Formalism.VW.rh_of_every` specializes the character theorem
to modulus one; no new zeta/critical-line implementation is introduced. -/
theorem rh_from_original_row : RiemannHypothesis :=
  Formalism.VW.rh_of_every every_character_from_original_row

theorem zeta_zero_location : RiemannZetaZerosOnLine :=
  rh_from_original_row

theorem dirichlet_right_half : DirichletLNonvanishingRightOfHalf :=
  every_character_from_original_row

theorem dirichlet_critical_strip : DirichletLZerosOnLine :=
  Claim.strip every_character_from_original_row

theorem primitive_dirichlet_strip : PrimitiveDirichletLZerosOnLine :=
  Formalism.VW.critLine every_character_from_original_row

#print axioms every_character_from_original_row
#print axioms rh_from_original_row
#print axioms zeta_zero_location
#print axioms dirichlet_right_half
#print axioms dirichlet_critical_strip
#print axioms primitive_dirichlet_strip

end DASHI.AlpogeRH.Selective
