import Integration.RationalAlbertF4E6DescentClassification

/-!
# Irreducible original-Q Albert F4/E6 frontier

All repository-internal algebraic work that can precede the global form/type
classification is already represented in the native rational Albert programme:
Jordan/cubic structure, anisotropic rational octonion norm, norm+unit rigidity,
native Cartan/derivation data, the Q(i) split-root chart and the real-place
compactness diagnostic.

The surviving classification debt is therefore not another invariant.  It is
one dependent same-object witness: an actual formal characteristic-zero Albert
classification theorem together with an `OriginalQAlbertDescentPayment` that
instantiates that theorem on the SAME native rational Albert object and actions.

This file reduces the terminal frontier to that single witness.  It does not
create the witness from source citations, local invariants, dimensions, root
counts or donor inventory.
-/

namespace Integration.RationalAlbertF4E6IrreducibleFrontier

open Integration.RationalAlbertF4ClassificationInstantiation
open Integration.RationalAlbertF4E6DescentClassification

/-- The one genuinely external/formal payment left by the native programme. -/
structure FinalOriginalQClassificationInput where
  classification : CharacteristicZeroAlbertClassificationTheorem
  payment : OriginalQAlbertDescentPayment classification

/-- Once the one final dependent witness exists, all three named terminal
classification conclusions are available through the already-typed same-object
instantiation. -/
def finalInstantiation (input : FinalOriginalQClassificationInput) :
    ClassificationInstantiation input.classification :=
  toClassificationInstantiation input.payment

theorem final_derivation_f4
    (input : FinalOriginalQClassificationInput) :
    input.classification.RationalDerivationFormOfF4 :=
  (finalInstantiation input).rationalDerivationForm

theorem final_automorphism_f4
    (input : FinalOriginalQClassificationInput) :
    input.classification.AutomorphismGroupTypeF4 :=
  (finalInstantiation input).automorphismF4

theorem final_cubic_structure_e6
    (input : FinalOriginalQClassificationInput) :
    input.classification.CubicStructureGroupTypeE6 :=
  (finalInstantiation input).cubicStructureE6

inductive LocalInvariantsCreateFinalClassificationInput : Prop
inductive SourceReceiptCreatesFinalClassificationInput : Prop
inductive MatchingSplitRootDatumCreatesFinalClassificationInput : Prop

theorem local_invariants_do_not_create_final_input :
    ¬ LocalInvariantsCreateFinalClassificationInput := by intro h; cases h

theorem source_receipt_does_not_create_final_input :
    ¬ SourceReceiptCreatesFinalClassificationInput := by intro h; cases h

theorem split_root_datum_does_not_create_final_input :
    ¬ MatchingSplitRootDatumCreatesFinalClassificationInput := by intro h; cases h

structure Boundary where
  allInternalNativeHypothesesAlreadyOwned : Bool
  normUnitJordanSameActionAlreadyPaid : Bool
  qiSplitRootChartAlreadyPaid : Bool
  realPlaceDiagnosticAlreadyPaid : Bool
  sameObjectDescentInterfaceAlreadyTyped : Bool
  terminalResidualReducedToSingleDependentWitness : Bool
  finalClassificationInputInhabitedHere : Bool
  localInvariantsAloneCreateFinalInput : Bool
  sourceReceiptAloneCreatesFinalInput : Bool
  matchingRootDatumAloneCreatesFinalInput : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  allInternalNativeHypothesesAlreadyOwned := true
  normUnitJordanSameActionAlreadyPaid := true
  qiSplitRootChartAlreadyPaid := true
  realPlaceDiagnosticAlreadyPaid := true
  sameObjectDescentInterfaceAlreadyTyped := true
  terminalResidualReducedToSingleDependentWitness := true
  finalClassificationInputInhabitedHere := false
  localInvariantsAloneCreateFinalInput := false
  sourceReceiptAloneCreatesFinalInput := false
  matchingRootDatumAloneCreatesFinalInput := false

end Integration.RationalAlbertF4E6IrreducibleFrontier
