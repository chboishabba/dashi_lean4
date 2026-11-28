import Mathlib
import YangMills.CMP119LiteralDyadicResidualWeld

/-!
# Exact CMP119 source-to-literal residual dictionary

The dyadic residual compiler is already theorem-bearing, but it consumes one
same-object equality between the selected complete residual and the localized
shell tail.  This file factors that equality into the source dictionary leaves
that must be checked against CMP119 while keeping all evaluations on the same
literal periodic link carrier.

No field below is discharged automatically from notation.  In particular,
regular-E, R-operation, boundary-B and vacuum each have an explicit
source-to-literal equality, additive source semantics is explicit, and the
localized-tail identity is explicit.
-/

namespace RequestProject.YangMills

structure CMP119LiteralResidualSourceDictionary
    (L : ℕ) where
  sourceRegular sourceROperation sourceBoundary sourceVacuum :
    SU2TorusLinks L → ℝ
  literalRegular literalROperation literalBoundary literalVacuum :
    SU2TorusLinks L → ℝ
  sourceResidual : SU2TorusLinks L → ℝ
  shellContribution : ℕ → SU2TorusLinks L → ℝ
  depth count : ℕ

  regularSourceEqLiteral : sourceRegular = literalRegular
  rOperationSourceEqLiteral : sourceROperation = literalROperation
  boundarySourceEqLiteral : sourceBoundary = literalBoundary
  vacuumSourceEqLiteral : sourceVacuum = literalVacuum

  additiveEvaluatorSemantics :
    sourceResidual = fun links =>
      sourceRegular links + sourceROperation links +
        sourceBoundary links + sourceVacuum links

  sourceResidualIsLocalizedTail :
    sourceResidual =
      fun links =>
        finiteLocalizedResidualTail shellContribution depth count links

  shellOscillation :
    ∀ shellDepth x y,
      |shellContribution shellDepth x -
        shellContribution shellDepth y| ≤
          cmp119DyadicShell shellDepth

namespace CMP119LiteralResidualSourceDictionary

/--
The complete literal residual is exactly the selected source residual once the
four source dictionaries and additive evaluator semantics are paid.
-/
theorem literalResidualEqSourceResidual
    {L : ℕ}
    (dict : CMP119LiteralResidualSourceDictionary L) :
    su2FullResidual
      dict.literalRegular dict.literalROperation
      dict.literalBoundary dict.literalVacuum =
      dict.sourceResidual := by
  funext links
  rw [← dict.regularSourceEqLiteral,
    ← dict.rOperationSourceEqLiteral,
    ← dict.boundarySourceEqLiteral,
    ← dict.vacuumSourceEqLiteral]
  rw [dict.additiveEvaluatorSemantics]
  rfl

/--
Exact constructor of the already-existing dyadic weld.  No localization
machinery is duplicated here: once the source dictionary is supplied, all
oscillation and normalized-expectation theorems downstream are inherited from
`CMP119LiteralDyadicResidualWeld`.
-/
def toDyadicResidualWeld
    {L : ℕ}
    (dict : CMP119LiteralResidualSourceDictionary L) :
    CMP119LiteralDyadicResidualWeld L where
  regular := dict.literalRegular
  rOperation := dict.literalROperation
  boundary := dict.literalBoundary
  vacuum := dict.literalVacuum
  shellContribution := dict.shellContribution
  depth := dict.depth
  count := dict.count
  residualIsLocalizedTail := by
    intro links
    have hSame := congrFun dict.literalResidualEqSourceResidual links
    rw [hSame]
    exact congrFun dict.sourceResidualIsLocalizedTail links
  shellOscillation := dict.shellOscillation

/-- The source dictionary inherits the exact dyadic pairwise oscillation bound. -/
theorem literalResidualPairwiseOscillation
    {L : ℕ}
    (dict : CMP119LiteralResidualSourceDictionary L)
    (x y : SU2TorusLinks L) :
    |su2FullResidual
        dict.literalRegular dict.literalROperation
        dict.literalBoundary dict.literalVacuum x -
      su2FullResidual
        dict.literalRegular dict.literalROperation
        dict.literalBoundary dict.literalVacuum y| ≤
      cmp119DyadicTailMajorant dict.depth := by
  exact cmp119_literal_residual_pairwise_oscillation
    dict.toDyadicResidualWeld x y

end CMP119LiteralResidualSourceDictionary

end RequestProject.YangMills
