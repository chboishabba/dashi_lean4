import Integration.OggSSP2BBinaryTetrahedralDefectSource

/-!
# Finite ambiguity left by the sourced (3,3,2,1,1) defect profile

The independently sourced binary-tetrahedral defect invariant does not by
itself identify the five Completion10 mode labels.  But it cuts the search
sharply.

Both sides have one unique depth-2 object, two depth-3 objects and two depth-1
objects.  Hence a defect-preserving bijection has exactly

  2! * 1! * 2! = 4

possibilities.

This turns D from an arbitrary 5! = 120 label-recognition problem into a
four-candidate source-selection problem.  No one of the four is promoted here
without independent source provenance.
-/

namespace Integration.OggSSP2BDefectRecognitionAmbiguity

namespace F := Integration.OggSSP2BFiveByTwoDefectArchitecture
namespace D := Integration.OggSSP2BBinaryTetrahedralDefectSource

/-- The exact property required of the underlying chart in a D-receipt. -/
def DefectCompatible (e : F.Mode5 ≃ D.OrderStratum) : Prop :=
  ∀ m, F.defectDepth m = D.centralizerTwoAdicExponent (e m)

instance (e : F.Mode5 ≃ D.OrderStratum) : Decidable (DefectCompatible e) := by
  unfold DefectCompatible
  infer_instance

abbrev DefectCompatibleChart :=
  { e : F.Mode5 ≃ D.OrderStratum // DefectCompatible e }

instance : Fintype DefectCompatibleChart := Fintype.ofFinite _

/-- Defect data alone leaves exactly four possible mode/stratum charts. -/
theorem defect_compatible_chart_count :
    Fintype.card DefectCompatibleChart = 4 := by
  native_decide

/-- The repository's numerical candidate is one of the four, but the count
proves that matching the defect vector cannot source-select it uniquely. -/
def numericalCandidate : DefectCompatibleChart :=
  ⟨D.numericalCandidateChart, D.numericalCandidateChart_matches_profile⟩

theorem defect_profile_does_not_determine_unique_chart :
    Fintype.card DefectCompatibleChart ≠ 1 := by
  rw [defect_compatible_chart_count]
  decide

/-- Semantic firewall: finite reduction to four candidates is not provenance. -/
inductive FourCompatibleChartsSelectTheSourceChart : Prop

theorem four_candidates_do_not_select_source_chart :
    ¬ FourCompatibleChartsSelectTheSourceChart := by
  intro h
  cases h

end Integration.OggSSP2BDefectRecognitionAmbiguity
