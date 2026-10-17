import RequestProject.QuantumMereology

/-!
# 2026 quantum-mereology SOTA source boundary

External source only:
Arsalan Adil, Manuel S. Rudolph, Andrew Arrasmith, Zoë Holmes,
Andreas Albrecht, and Andrew Sornborger,
"Search for classical subsystems in quantum worlds",
Phys. Rev. D 113, 103535 (2026), DOI 10.1103/vj4x-96fk.

The published source reports that, for a fixed Hamiltonian, several tensor-product
factorizations can admit quasiclassical subsystems with pointer states robust to
entanglement; its algorithm explores a multitude of such factorizations and the
paper emphasizes that decohering subsystems need not coincide with intuitive
spatial locality.

This file is deliberately an attribution/source-boundary owner only.  It does
not turn the paper's analytic/numerical results into a DASHI kernel theorem, does
not identify the paper's optimization objective with the Carroll--Singh
Schwinger score, and does not prove non-uniqueness for every Hamiltonian or every
candidate family.
-/

namespace QuantumMereology
namespace SOTA2026

structure Boundary where
  sourceReportsSeveralQuasiclassicalFactorizations : Bool := true
  sourceReportsPointerRobustnessCriterion : Bool := true
  sourceSaysDecoheringSubsystemsNeedNotMatchClassicalLocality : Bool := true
  sourceCreatesLocalNonuniquenessTheorem : Bool := false
  sourceCreatesUniquePreferredTPS : Bool := false
  sourceObjectiveIdentifiedWithCarrollSinghSchwingerScore : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem source_does_not_create_unique_preferred_tps :
    canonicalBoundary.sourceCreatesUniquePreferredTPS = false := rfl

theorem source_does_not_create_local_nonuniqueness_theorem :
    canonicalBoundary.sourceCreatesLocalNonuniquenessTheorem = false := rfl

/-- Exact external-source attribution. -/
def adilEtAl2026 : SourceReceipt where
  authors := "Arsalan Adil; Manuel S. Rudolph; Andrew Arrasmith; Zoë Holmes; Andreas Albrecht; Andrew Sornborger"
  title := "Search for classical subsystems in quantum worlds"
  venue := "Physical Review D 113, 103535"
  year := "2026"
  identifier := "doi:10.1103/vj4x-96fk"
  supports := "For fixed Hamiltonians, reports several tensor-product factorizations admitting quasiclassical subsystems with pointer states robust to entanglement, explores a multitude of such factorizations algorithmically, and shows that decohering subsystems need not align with intuitive classical locality."

def adilEtAl2026Claim : AttributionReceipt where
  role := .externalSourceClaim
  owner := "Arsalan Adil et al., Phys. Rev. D 113, 103535 (2026)"
  claim := "The source reports that a fixed Hamiltonian can admit several quasiclassical tensor-product factorizations and that decohering subsystems need not coincide with intuitive locality. DASHI does not attribute to this source a universal local non-uniqueness theorem, uniqueness result, or identification with the Carroll--Singh Schwinger score."

end SOTA2026
end QuantumMereology
