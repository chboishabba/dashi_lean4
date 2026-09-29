import Mathlib

/-!
# Earth embeddings × Woogaroo: representation and evidence firewalls

The 64/128 coordinate values represent each sampled cell/year, not the whole
Earth. Neither embedding similarity nor co-location constitutes ecological or
statutory proof. This module proves structural statements only; empirical
performance and source identification require external receipts.
-/

namespace EarthEmbeddingWoogaroo

inductive Sensor
  | sentinel1 | sentinel2 | landsat | lidar | inSitu
  deriving DecidableEq, Repr

structure Observation where
  sensor : Sensor
  year : Nat
  cell : String
  payloadRef : String
  qualityRef : String

inductive Model
  | alphaEarth | tessera | tesseraV2
  deriving DecidableEq, Repr

def dimension : Model → Nat
  | .alphaEarth => 64
  | .tessera => 128
  | .tesseraV2 => 128

structure Embedding (m : Model) where
  cell : String
  year : Nat
  vectorRef : String
  modelVersion : String
  provenanceRef : String

structure MatchedObservation (a b : Model) where
  left : Embedding a
  right : Embedding b
  sameCell : left.cell = right.cell
  sameWindow : left.year = right.year

structure HeldOutSplit where
  trainCells : String
  validationCells : String
  trainYears : String
  validationYears : String
  disjointnessReceipt : String

inductive EvidenceStage
  | modelOutput | calibratedObservation | validatedPrediction
  | ecologicalInterpretation | legalConsumer

inductive Evidence : EvidenceStage → Type
  | produced (source : String) : Evidence .modelOutput
  | calibrated (source : String) : Evidence .calibratedObservation
  | validated (model : String) (split : HeldOutSplit) (metrics : String) :
      Evidence .validatedPrediction
  | interpreted (base : Evidence .validatedPrediction) (receipt : String) :
      Evidence .ecologicalInterpretation
  | legallyReviewed (base : Evidence .ecologicalInterpretation)
      (sourceInstrument review : String) : Evidence .legalConsumer

inductive Waterway
  | springfieldLakes | opossumCreek | mountainCreek
  | woogarooCreek | brisbaneRiver
  deriving DecidableEq, Repr

inductive Connection : Waterway → Waterway → Prop
  | lakesOpossum : Connection .springfieldLakes .opossumCreek
  | opossumWoogaroo : Connection .opossumCreek .woogarooCreek
  | mountainWoogaroo : Connection .mountainCreek .woogarooCreek
  | woogarooBrisbane : Connection .woogarooCreek .brisbaneRiver

inductive Downstream : Waterway → Waterway → Prop
  | direct {a b} : Connection a b → Downstream a b
  | trans {a b c} : Downstream a b → Downstream b c → Downstream a c

theorem springfield_to_brisbane :
    Downstream .springfieldLakes .brisbaneRiver :=
  .trans (.direct .lakesOpossum)
    (.trans (.direct .opossumWoogaroo) (.direct .woogarooBrisbane))

/-- Model prefix coordinates are purely geometric and say nothing about accuracy. -/
def prefix {n : Nat} (v : Fin n → ℝ) (k : Nat) (hk : k ≤ n) :
    Fin k → ℝ :=
  fun i => v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩

theorem prefix_compose {n k j : Nat} (v : Fin n → ℝ)
    (hk : k ≤ n) (hj : j ≤ k) :
    prefix (prefix v k hk) j hj =
      prefix v j (Nat.le_trans hj hk) := by
  funext i
  rfl

/-- Coordinate distance expansion: no unit-length assumption needed. -/
theorem coordinate_distance_identity (u v : ℝ) :
    (u - v) ^ 2 = u ^ 2 + v ^ 2 - 2 * u * v := by
  ring

structure WoogarooExperiment where
  selectedRegion : String
  baselineAttributes : String
  alphaEarthSamples : String
  tesseraSamples : String
  groundTruth : String
  splitPlan : HeldOutSplit
  measuredOutputs : String
  independentValidation : String

inductive Target
  | riparianChange | canopyStructure | runoff | sediment
  | waterQuality | habitat
  deriving DecidableEq, Repr

structure CandidatePrediction where
  target : Target
  experiment : WoogarooExperiment
  outputReceipt : String
  validated : Bool

end EarthEmbeddingWoogaroo
