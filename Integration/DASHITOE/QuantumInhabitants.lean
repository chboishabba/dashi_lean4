import Integration.DASHITOE.ConcreteInhabitants

namespace DASHITOE

/-- Actual finite g-TPS projector theorem value exists on Lean PR #76.  This
receipt imports its formal-source authority without pretending the theorem term
is present on the TOE branch. -/
def lean76GTPSProjectionInhabitant : FormalInhabitantReceipt :=
  { prover := "Lean4"
    repository := "chboishabba/dashi_lean4"
    pullRequest := 76
    headCommit := "7749ed96f03aeb0a8b59c108d8b3902b059acf0a"
    moduleName := "QuantumMereology.GTPSProjectionProducer"
    declaration := "localPlusCommutantProjection"
    propositionScope := "Every finite source g-TPS has the canonical Hilbert-Schmidt orthogonal projection onto A+A', yielding a fully instantiated finite short-time scrambling score."
    authority := .importedFormalInhabitant }

/-- Actual finite unitary-family g-TPS metric theorem value on Lean PR #76. -/
def lean76GTPSMetricInhabitant : FormalInhabitantReceipt :=
  { prover := "Lean4"
    repository := "chboishabba/dashi_lean4"
    pullRequest := 76
    headCommit := "7749ed96f03aeb0a8b59c108d8b3902b059acf0a"
    moduleName := "QuantumMereology.GTPSUnitaryMetric2026"
    declaration := "metricElementSq_eq_source_formula"
    propositionScope := "Finite source unitary-family g-TPS metric element equals kappa^2 times the canonical projected Hilbert-Schmidt residual norm on an explicit same-object tangent receipt."
    authority := .importedFormalInhabitant }

structure QuantumFormalInhabitantBundle where
  projector : FormalInhabitantReceipt
  unitaryMetric : FormalInhabitantReceipt


def canonicalQuantumFormalInhabitantBundle : QuantumFormalInhabitantBundle :=
  { projector := lean76GTPSProjectionInhabitant
    unitaryMetric := lean76GTPSMetricInhabitant }

end DASHITOE
