import Integration.TeleodynamicsExceptionalWeylExperiment
import Integration.RationalAlbertF4CartanNative
import Integration.RationalAlbertF4SplitRootDatumReceipt
import Mathlib

/-!
# Teleodynamics / LILA exceptional-Lie evidence ladder

The finite-Weyl experiment owner deliberately stops at generator/Coxeter action.
The Albert/F4 programme now has stronger but still graded evidence:

  finite Weyl action
    < native same-object Cartan action
    < exact split-root grading over Q(i)
    < original-field/rational-form classification
    < algebraic-group recognition
    < empirical infinitesimal/model equivariance
    < target/mechanism realization.

This matters experimentally.  A latent representation may fit a finite root
codebook or even approximate selected Lie generators without thereby realizing
the rational F4 form, the continuous/algebraic group, or any physical or
phenomenal mechanism.

The split-root datum currently uses a companion exact Agda producer receipt for
the Q(i) spectral/root grading.  That receipt is not Lean theorem authority.
-/

namespace Integration.TeleodynamicsExceptionalLieExperiment

open Integration.TeleodynamicsExceptionalWeylExperiment
open Integration.RationalAlbertF4CartanNative
open Integration.RationalAlbertF4SplitRootDatumReceipt

structure ExceptionalLieEvidenceGrade where
  candidate : ExceptionalSymmetryCandidate
  finiteWeylActionPaid : Bool
  nativeCartanActionPaid : Bool
  splitRootDatumPaid : Bool
  splitRootDatumLeanInternal : Bool
  rationalFormClassificationPaid : Bool
  algebraicGroupRecognitionPaid : Bool
  empiricalInfinitesimalEquivariancePaid : Bool
  empiricalFiniteFlowCompositionPaid : Bool
  targetRealizationPaid : Bool
  deriving Repr

/-- F4 currently reaches an actual native Cartan and exact split-root-datum
receipt on the same rational Albert programme.  The Q-form/group theorem and
empirical realization remain separate. -/
def canonicalF4LieGrade : ExceptionalLieEvidenceGrade where
  candidate := .f4FoldedAlbert
  finiteWeylActionPaid := true
  nativeCartanActionPaid := true
  splitRootDatumPaid := true
  splitRootDatumLeanInternal := false
  rationalFormClassificationPaid := false
  algebraicGroupRecognitionPaid := false
  empiricalInfinitesimalEquivariancePaid := false
  empiricalFiniteFlowCompositionPaid := false
  targetRealizationPaid := false

/-- Existing finite exceptional candidates do not inherit Lie-level evidence by
sharing ranks/root counts with F4. -/
def finiteOnlyGrade (c : ExceptionalSymmetryCandidate) : ExceptionalLieEvidenceGrade where
  candidate := c
  finiteWeylActionPaid := true
  nativeCartanActionPaid := false
  splitRootDatumPaid := false
  splitRootDatumLeanInternal := false
  rationalFormClassificationPaid := false
  algebraicGroupRecognitionPaid := false
  empiricalInfinitesimalEquivariancePaid := false
  empiricalFiniteFlowCompositionPaid := false
  targetRealizationPaid := false

/-- Exact local theorem: the four selected native Albert Cartan operators commute.
This is stronger than a root/codebook receipt and weaker than full F4 group
recognition. -/
theorem f4_native_cartan_commutes :
    ∀ i j X,
      cartanDerivation i (cartanDerivation j X) =
        cartanDerivation j (cartanDerivation i X) :=
  cartan_commute

/-- Model-facing infinitesimal test surface.  The model supplies a latent vector
field for each declared generator and a derivative/action residual.  A small
residual is empirical evidence only; it is not an exact representation theorem. -/
structure InfinitesimalEquivarianceReceipt where
  candidate : ExceptionalSymmetryCandidate
  generatorCount : Nat
  trainInterventions : Nat
  heldOutInterventions : Nat
  generatorDerivativeResidualsMeasured : Bool
  commutatorResidualsMeasured : Bool
  rootWeightResidualsMeasured : Bool
  finiteFlowCompositionResidualsMeasured : Bool
  decoderCompatibilityMeasured : Bool
  futureConsumerMeasured : Bool
  sameDataUsedForFitAndHoldout : Bool
  deriving Repr

/-- Stronger empirical protocol for the F4 candidate: test the four commuting
Cartan directions, selected root-space actions, brackets, and exponentiated
finite-flow composition on held-out interventions. -/
def f4InfinitesimalProtocol : InfinitesimalEquivarianceReceipt where
  candidate := .f4FoldedAlbert
  generatorCount := 4
  trainInterventions := 0
  heldOutInterventions := 0
  generatorDerivativeResidualsMeasured := false
  commutatorResidualsMeasured := false
  rootWeightResidualsMeasured := false
  finiteFlowCompositionResidualsMeasured := false
  decoderCompatibilityMeasured := false
  futureConsumerMeasured := false
  sameDataUsedForFitAndHoldout := false

structure Boundary where
  finiteWeylOwnerReused : Bool
  nativeAlbertCartanOwnerReused : Bool
  exactSplitRootReceiptReused : Bool
  finiteWeylFitCreatesLieEquivariance : Bool
  nativeCartanFitCreatesRationalF4Form : Bool
  splitRootDatumCreatesAlgebraicGroup : Bool
  splitRootDatumCreatesPhysicalMechanism : Bool
  splitRootDatumCreatesPhenomenology : Bool
  crossKernelReceiptCreatesLeanTheorem : Bool
  empiricalLieFitEliminatesHeldOutTesting : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  finiteWeylOwnerReused := true
  nativeAlbertCartanOwnerReused := true
  exactSplitRootReceiptReused := true
  finiteWeylFitCreatesLieEquivariance := false
  nativeCartanFitCreatesRationalF4Form := false
  splitRootDatumCreatesAlgebraicGroup := false
  splitRootDatumCreatesPhysicalMechanism := false
  splitRootDatumCreatesPhenomenology := false
  crossKernelReceiptCreatesLeanTheorem := false
  empiricalLieFitEliminatesHeldOutTesting := false

inductive FiniteWeylFitCreatesLieEquivariance : Prop
inductive SplitRootDatumCreatesMechanism : Prop
inductive LieFitCreatesPhenomenology : Prop

theorem finite_weyl_fit_does_not_create_lie_equivariance :
    ¬ FiniteWeylFitCreatesLieEquivariance := by intro h; cases h

theorem split_root_datum_does_not_create_mechanism :
    ¬ SplitRootDatumCreatesMechanism := by intro h; cases h

theorem lie_fit_does_not_create_phenomenology :
    ¬ LieFitCreatesPhenomenology := by intro h; cases h

end Integration.TeleodynamicsExceptionalLieExperiment
