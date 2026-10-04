import Mathlib
import EarthEmbeddingWoogaroo

/-!
# Source-oriented finite geometry for Earth embeddings

Theorems here are mathematical; reported values 13.3, ~10 and 0.97 are
study-specific observations and intentionally do NOT inhabit theorem fields.

References:
- Rahman (2026) https://arxiv.org/abs/2602.10354
- Rahman et al. (2026) https://arxiv.org/abs/2604.18715
- Brown et al. (2025) https://arxiv.org/abs/2507.22291
- Feng et al. (2026) https://arxiv.org/abs/2607.03949
- Ou & Zheng (2026) https://doi.org/10.1029/2025GL121604
- Liu et al. (2026) https://doi.org/10.1029/2026GL122814
-/

namespace EarthEmbeddingGeometry

abbrev Vector (n : Nat) := Fin n → ℝ

def dot {n : Nat} (u v : Vector n) : ℝ :=
  ∑ i, u i * v i

def squaredDistance {n : Nat} (u v : Vector n) : ℝ :=
  ∑ i, (u i - v i) ^ 2

def squaredNorm {n : Nat} (u : Vector n) : ℝ :=
  dot u u

def OnSphere {n : Nat} (u : Vector n) : Prop :=
  squaredNorm u = 1

theorem squaredDistance_expand {n : Nat} (u v : Vector n) :
    squaredDistance u v =
      squaredNorm u + squaredNorm v - 2 * dot u v := by
  unfold squaredDistance squaredNorm dot
  calc
    (∑ i, (u i - v i) ^ 2) =
        ∑ i, (u i * u i + v i * v i - 2 * (u i * v i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = (∑ i, u i * u i) + (∑ i, v i * v i) -
        2 * (∑ i, u i * v i) := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
              ← Finset.mul_sum]

theorem unit_squaredDistance {n : Nat} (u v : Vector n)
    (hu : OnSphere u) (hv : OnSphere v) :
    squaredDistance u v = 2 - 2 * dot u v := by
  rw [squaredDistance_expand, hu, hv]
  ring

theorem cosine_distance_order {n : Nat} (query a b : Vector n)
    (hq : OnSphere query) (ha : OnSphere a) (hb : OnSphere b) :
    squaredDistance query a ≤ squaredDistance query b ↔
    dot query b ≤ dot query a := by
  rw [unit_squaredDistance query a hq ha,
      unit_squaredDistance query b hq hb]
  constructor <;> intro h <;> linarith

/-- Quantisation error is an *assumption or certified measurement*;
    it is never inferred from model dimension alone. -/
structure QuantisationCertificate (n : Nat) where
  reference : Vector n
  encoded : Vector n
  perCoordinateBound : ℝ
  bound_nonnegative : 0 ≤ perCoordinateBound
  coordinate_error : ∀ i, |encoded i - reference i| ≤ perCoordinateBound
  sourceReceipt : String

theorem coordinate_error_sq {n : Nat} (q : QuantisationCertificate n) (i : Fin n) :
    (q.encoded i - q.reference i) ^ 2 ≤ q.perCoordinateBound ^ 2 := by
  nlinarith [q.coordinate_error i, abs_nonneg (q.encoded i - q.reference i),
    sq_nonneg (q.encoded i - q.reference i)]

/-- Coordinate-count, effective dimension and decoded-variable count
    have distinct types, deliberately with no automatic coercions. -/
structure DimensionalityReport where
  ambient : Nat
  participationRatioEstimate : ℝ
  localIntrinsicEstimate : ℝ
  decodedVariables : Nat
  samplePopulation : String
  estimator : String
  uncertaintyReceipt : String
  source : String

/-- Spectral participation ratio; no statement that it measures manifold dimension. -/
def participationRatio {n : Nat} (spectrum : Vector n) : ℝ :=
  (∑ i, spectrum i) ^ 2 / (∑ i, (spectrum i) ^ 2)

/-- Discrete observation support is NOT promoted to a smooth manifold. -/
structure ObservedEmbeddingField (Location Time : Type) (n : Nat) where
  encode : Location → Time → Vector n
  datasetVersion : String
  region : String
  interval : String

def observedRange {L T : Type} {n : Nat}
    (field : ObservedEmbeddingField L T n) : Set (Vector n) :=
  Set.range (fun p : L × T => field.encode p.1 p.2)

/-- A local decoder requires a chosen neighborhood and empirical validation. -/
structure LocalDecoder (n m : Nat) where
  center : Vector n
  neighborhood : Set (Vector n)
  decode : Vector n → Vector m
  validationReceipt : String

/-- Differential geometry is conditional on a differentiable model.
    This interface intentionally does not assert that AlphaEarth is smooth. -/
structure SmoothSurrogate (n k : Nat) where
  parameterToEmbedding : Vector k → Vector n
  tangentAt : Vector k → (Vector k →ₗ[ℝ] Vector n)
  tangentJustification : String
  fitReceipt : String

/-- Matched geography is not proof of semantic equivalence. -/
structure CrossModelAlignment (Location Time : Type) where
  alpha : ObservedEmbeddingField Location Time 64
  tessera : ObservedEmbeddingField Location Time 128
  latentDimension : Nat
  projectAlpha : Vector 64 → Vector latentDimension
  projectTessera : Vector 128 → Vector latentDimension
  calibrationReceipt : String
  validationReceipt : String

def alignmentResidual {L T : Type} (a : CrossModelAlignment L T)
    (location : L) (time : T) : ℝ :=
  squaredDistance (a.projectAlpha (a.alpha.encode location time))
    (a.projectTessera (a.tessera.encode location time))

theorem alignmentResidual_nonnegative {L T : Type}
    (a : CrossModelAlignment L T) (location : L) (time : T) :
    0 ≤ alignmentResidual a location time := by
  unfold alignmentResidual squaredDistance
  exact Finset.sum_nonneg (fun i hi => sq_nonneg _)

/-- A physically interpreted prediction has a dedicated evidence receipt. -/
structure PhysicalDecoderValidation (n m : Nat) where
  decoder : Vector n → Vector m
  variableNames : Fin m → String
  observedLabelsReceipt : String
  regionHeldOutReceipt : String
  timeHeldOutReceipt : String
  performanceReceipt : String
  uncertaintyReceipt : String

/-- An actual split predicate is stronger than a textual assertion. -/
structure LeakageControlledSplit (Cell : Type) where
  train : Set Cell
  test : Set Cell
  disjoint : Disjoint train test
  trainingYears : Set Nat
  testYears : Set Nat
  disjointYears : Disjoint trainingYears testYears
  bufferedSpatialSeparationReceipt : String

/-- Research claims remain attributed results; this is not a trained model. -/
structure StudyClaim where
  doiOrUrl : String
  geographicPopulation : String
  measurementDefinition : String
  reportedValue : String
  estimatorAndValidation : String

def rahmanPhysical : StudyClaim where
  doiOrUrl := "https://arxiv.org/abs/2602.10354"
  geographicPopulation := "12.1 million CONUS records, 2017–2023"
  measurementDefinition := "26 environmental variables; 12 reported R2 > 0.90"
  reportedValue := "temperature and elevation near R2 0.97"
  estimatorAndValidation := "spatial block CV and temporal stability; consult paper"

def rahmanGeometry : StudyClaim where
  doiOrUrl := "https://arxiv.org/abs/2604.18715"
  geographicPopulation := "12.1 million CONUS records, 2017–2023"
  measurementDefinition := "spectral participation ratio vs local dimension"
  reportedValue := "effective 13.3, local intrinsic about 10"
  estimatorAndValidation := "local tangent rotations; method-specific"

def ouAustralianCatchments : StudyClaim where
  doiOrUrl := "https://doi.org/10.1029/2025GL121604"
  geographicPopulation := "455 Australian catchments, 2017–2022"
  measurementDefinition := "median relative error reduction in disturbed regions"
  reportedValue := "11.5 percent"
  estimatorAndValidation := "published GRL study; not a Woogaroo result"

def liuGlobalCatchments : StudyClaim where
  doiOrUrl := "https://doi.org/10.1029/2026GL122814"
  geographicPopulation := "531 CAMELS basins; 3434 global basins"
  measurementDefinition := "AlphaEarth catchment descriptor benchmark"
  reportedValue := "reported median NSE values; not a Woogaroo result"
  estimatorAndValidation := "published GRL study; population-dependent"

end EarthEmbeddingGeometry
