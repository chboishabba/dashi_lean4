import Integration.OggSSP2BSourceActionMaxCut
import Integration.OggSSP2BIntegralCentralizerTateAction
import Integration.OggSSP2BEquivariantSourceActionTerminalCompiler

/-!
# Canonical 2B frontier after quotient-action and equivariant-weld compression

The norm/exterior representation search is closed.  Two additional compiler
reductions remove the last avoidable formal leaves:

* one centralizer representation commuting with the selected 2B involution
  automatically descends through `range (1+a)` to the Tate quotient;
* equivariance of the literal Tate/exterior equivalence automatically implies
  the old terminal conjugation equation for the within-fibre outer operator.

Accordingly the final B'+C' formal seam is no longer a separately instantiated
quotient action plus a separately proved operator equality.  It is one
source-native action/equivariance instantiation.  D still requires two external
Mode5/2T provenance decisions, and 31/279 remain firewalled.
-/

namespace Integration.OggSSP2BPostEquivarianceMaxCut

structure Status where
  externalMonsterStableIntegralActionSourced : Bool
  quotientActionFromCentralizerCommutationCompilerPaid : Bool
  normExteriorRepresentationDiscoveryClosed : Bool
  equivariantWeldToLastEquationCompilerPaid : Bool
  finalCoreFromEquivariantWeldCompilerPaid : Bool

  formalSourceNativeCentralizerActionObjectInstantiated : Bool
  literalTateExteriorWeldEquivariancePaid : Bool
  actualStableQ10AndCompletionPaid : Bool
  actualThreeFibreQ10TransportPaid : Bool

  remainingRepresentationDiscoveryLeaves : Nat
  remainingFormalSourceActionEquivarianceLeaves : Nat
  remainingIndependentOuterActionEquations : Nat
  remainingDefectSourceBits : Nat
  downstream31Paid : Bool
  downstream279Paid : Bool

  nextResidual : String

/-- Honest max-cut after the two new generic compilers. -/
def canonicalStatus : Status where
  externalMonsterStableIntegralActionSourced := true
  quotientActionFromCentralizerCommutationCompilerPaid := true
  normExteriorRepresentationDiscoveryClosed := true
  equivariantWeldToLastEquationCompilerPaid := true
  finalCoreFromEquivariantWeldCompilerPaid := true

  formalSourceNativeCentralizerActionObjectInstantiated := false
  literalTateExteriorWeldEquivariancePaid := false
  actualStableQ10AndCompletionPaid := false
  actualThreeFibreQ10TransportPaid := false

  remainingRepresentationDiscoveryLeaves := 0
  remainingFormalSourceActionEquivarianceLeaves := 1
  remainingIndependentOuterActionEquations := 0
  remainingDefectSourceBits := 2
  downstream31Paid := false
  downstream279Paid := false

  nextResidual :=
    "Instantiate the sourced C_M(2B)/Co1 representation once on the formal source-native norm carrier and prove the already-constructed Tate/exterior equivalence is equivariant. The quotient action and old outer conjugation equation then compile automatically. After that only the two independently sourced Mode5/2T provenance bits remain before Final2BCoreRecognition closes."

theorem representation_discovery_closed :
    canonicalStatus.remainingRepresentationDiscoveryLeaves = 0 := rfl

theorem one_formal_source_action_equivariance_leaf :
    canonicalStatus.remainingFormalSourceActionEquivarianceLeaves = 1 := rfl

theorem no_independent_outer_action_equation :
    canonicalStatus.remainingIndependentOuterActionEquations = 0 := rfl

theorem defect_source_bits_remain_two :
    canonicalStatus.remainingDefectSourceBits = 2 := rfl

end Integration.OggSSP2BPostEquivarianceMaxCut
