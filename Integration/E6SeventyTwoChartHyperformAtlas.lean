import Integration.Ternary27A5SixFaceReorganisation
import Integration.E6F3OrbitTransitivity
import Integration.E6F3GeneratedGroupClosure
import Mathlib

/-!
# E6 as a 72-chart hyperformal atlas with S6 chart stabilizer

A single 6+15+6 Schlaefli presentation is adapted to a selected E6 root.  The
paid A5 subsystem is the stabilizer geometry of that selected root and acts on
the raw ternary 27 as the full S6 six-face reorganisation.

The full E6 image should therefore not be expected to preserve one fixed chart:
it acts transitively on the 72 Q=2/root indices.  This owner records the atlas
shape already forced by the paid finite theorems:

  |W(E6)| = 51840 = 72 * 720,

with 72 root-selected chart indices and an S6 stabilizer action inside the
selected chart.

What remains is not another cardinality theorem but the transition/cocycle
receipt identifying the independently selected matrix stabilizer with the
six-face S6 action and transporting the selected chart coherently across the 72
root indices.
-/

namespace Integration.E6SeventyTwoChartHyperformAtlas

open Integration.E6F3OrbitTransitivity
open Integration.E6F3GeneratedGroupClosure
open Integration.E6RootStabilizerA5SixSet
open Integration.Ternary27HyperformSchlafliRecognition
open Integration.Ternary27A5SixFaceReorganisation

/-- Root-selected chart indices are the already-paid Q=2/root orbit. -/
abbrev RootChartIndex := StandardQ2

 theorem root_chart_index_card : Fintype.card RootChartIndex = 72 := by
  simpa using standardQ2_card

/-- The same six E6 simple generators move between root charts transitively. -/
def moveRootChart (s : E6SimpleReflection) (r : RootChartIndex) : RootChartIndex :=
  reflectQ2 s r

 theorem root_chart_indices_transitive_from_existing_seed : q2Orbit = Finset.univ :=
  q2_orbit_full

/-- One selected chart is the already-realized typed ternary 27. -/
abbrev SelectedChartCarrier := Ternary27Point

/-- Its internal stabilizer generators are the directly realized A5 face
reorganisations, not an action transported from minuscule weights. -/
def selectedChartStabilizerGenerator
    (a : A5Simple) (p : SelectedChartCarrier) : SelectedChartCarrier :=
  actPoint a p

 theorem selected_chart_stabilizer_preserves_schlafli :
    ∀ a x y,
      pointSchlafli (selectedChartStabilizerGenerator a x)
          (selectedChartStabilizerGenerator a y) = pointSchlafli x y :=
  a5_point_reorganisation_preserves_schlafli

 theorem selected_chart_stabilizer_six_action_is_full_sym6 :
    a5GeneratedTables = allSym6Tables :=
  raw_face_generators_close_to_all_sym6

 theorem e6_order_is_chart_count_times_stabilizer :
    generatedMatrixSet.card = 72 * q2SeedStabilizer.card :=
  generated_order_eq_root_orbit_times_stabilizer

/-- Exact remaining same-object receipt at the selected chart.  It must identify
the independently enumerated 720-element matrix stabilizer with the already
realized six-face S6 action, not merely compare their orders. -/
structure SelectedMatrixStabilizerFaceWeld : Set where
  matrixStabilizerActsOnSelectedChart :
    {M : Mat5 // M ∈ q2SeedStabilizer} → SelectedChartCarrier → SelectedChartCarrier
  matrixStabilizerToSixPermutation :
    {M : Mat5 // M ∈ q2SeedStabilizer} → Table6
  sixPermutationBijectionReceipt : Prop
  selectedChartActionIntertwinerReceipt : Prop
  a5GeneratorCompatibilityReceipt : Prop

/-- Once the selected stabilizer weld is known, full E6 atlas recognition still
requires coherent transition maps between root-selected charts.  The cocycle
condition is stated explicitly so path-dependent chart transport cannot be
silently collapsed. -/
structure RootChartTransitionReceipt : Set where
  transition : RootChartIndex → RootChartIndex → SelectedChartCarrier → SelectedChartCarrier
  identityTransitionReceipt : Prop
  inverseTransitionReceipt : Prop
  compositionCocycleReceipt : Prop
  e6GeneratorMovesChartReceipt : Prop
  schlafliRelationTransportReceipt : Prop

inductive FullE6RawTernaryAtlasPaid : Prop

 theorem current_data_does_not_manufacture_full_atlas : ¬ FullE6RawTernaryAtlasPaid := by
  intro h
  cases h

structure Boundary where
  rootChartCount72Paid : Bool
  fullE6RootChartTransitivityPaid : Bool
  selectedChartRawTernaryCarrierPaid : Bool
  selectedChartA5FaceActionPaid : Bool
  selectedChartS6ClosurePaid : Bool
  orbitStabilizer51840Eq72Times720Paid : Bool
  selectedMatrixStabilizerFaceWeldPaid : Bool
  rootChartTransitionCocyclePaid : Bool
  fullE6RawTernaryAtlasPaid : Bool
  deriving Repr


def canonicalBoundary : Boundary where
  rootChartCount72Paid := true
  fullE6RootChartTransitivityPaid := true
  selectedChartRawTernaryCarrierPaid := true
  selectedChartA5FaceActionPaid := true
  selectedChartS6ClosurePaid := true
  orbitStabilizer51840Eq72Times720Paid := true
  selectedMatrixStabilizerFaceWeldPaid := false
  rootChartTransitionCocyclePaid := false
  fullE6RawTernaryAtlasPaid := false

end Integration.E6SeventyTwoChartHyperformAtlas
