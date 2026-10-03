import Mathlib
import EarthEmbeddingGeometry

/-!
# Conditional semantics of embedding fields and error budgets

Distinguish pure algebra and empirical sensor observations. Neither a
measurable encoder nor a study's PCA finding constructs a global smooth
manifold. Validation receipts do not prove environmental truth.
-/

namespace EarthEmbeddingAdvanced
open MeasureTheory
open EarthEmbeddingGeometry

/-- Sampling distribution on space-time, pushed forward by a measurable
    finite-dimensional encoder. It may have arbitrary support. -/
structure MeasuredEmbedding (Location Time : Type*)
    [MeasurableSpace Location] [MeasurableSpace Time] (n : Nat) where
  encoder : Location × Time → Vector n
  measurable_encoder : Measurable encoder
  version : String
  acquisitionMetadata : String

def pushforward {Location Time : Type*}
    [MeasurableSpace Location] [MeasurableSpace Time] {n : Nat}
    (m : MeasuredEmbedding Location Time n)
    (μ : Measure (Location × Time)) :
    Measure (Vector n) :=
  μ.map m.encoder

/-- The support of this distribution is not assumed to be a manifold. -/
def embeddedSupport {Location Time : Type*}
    [MeasurableSpace Location] [MeasurableSpace Time] {n : Nat}
    (m : MeasuredEmbedding Location Time n)
    (μ : Measure (Location × Time)) :
    Set (Vector n) :=
  (pushforward m μ).support

/-- Global affine decoding is in general too restrictive: even the
    scalar physical law y=x² cannot agree with an affine law at 0,1,2. -/
theorem no_global_affine_square :
    ¬ ∃ a b : ℝ, ∀ x : ℝ, a * x + b = x ^ 2 := by
  rintro ⟨a, b, h⟩
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  norm_num at h0 h1 h2
  nlinarith

/-- A pointwise encoded embedding need not have zero quantisation error.
    The bound must be independently certified. -/
structure QuantisationBound (n : Nat) where
  truth : Vector n
  bytesDecoded : Vector n
  epsilon : ℝ
  nonnegative : 0 ≤ epsilon
  each_coordinate : ∀ i, |bytesDecoded i - truth i| ≤ epsilon
  acquisitionVersion : String

theorem quantisation_square_bound {n : Nat}
    (q : QuantisationBound n) (i : Fin n) :
    (q.bytesDecoded i - q.truth i) ^ 2 ≤ q.epsilon ^ 2 := by
  have habs := q.each_coordinate i
  have hpos : 0 ≤ q.epsilon - (q.bytesDecoded i - q.truth i) := by
    have := (abs_le.mp habs).2
    linarith
  have hneg : 0 ≤ q.epsilon + (q.bytesDecoded i - q.truth i) := by
    have := (abs_le.mp habs).1
    linarith
  have hprod := mul_nonneg hpos hneg
  nlinarith

theorem quantisation_total_square_bound {n : Nat} (q : QuantisationBound n) :
    squaredDistance q.bytesDecoded q.truth ≤ ∑ _ : Fin n, q.epsilon ^ 2 := by
  unfold squaredDistance
  apply Finset.sum_le_sum
  intro i hi
  exact quantisation_square_bound q i

/-- A prefix relation is an algebraic identity, not a theorem on
    downstream predictive performance. -/
structure MatryoshkaHead (k : Nat) where
  parent : Vector 128
  validLength : k ≤ 128
  projected : Vector k := EarthEmbeddingWoogaroo.prefix parent k validLength
  benchmarkVersion : String

/-- Local derivative hypotheses are explicitly owned by the surrogate
    and do not turn a discrete dataset into a differentiable manifold. -/
structure InterpretedLocalChart (n intrinsic outputs : Nat) where
  surrogate : SmoothSurrogate n intrinsic
  observedCenter : Vector n
  targetNeighborhood : Set (Vector n)
  localDecode : Vector n → Vector outputs
  calibrationPopulation : String
  localErrorReceipt : String
  tangentRotationReceipt : String

/-- The required original physical observation is kept separate from a
    representation and any model-generated estimate. -/
structure CalibratedPhysicalOutcome (n m : Nat) where
  embedding : Vector n
  measured : Vector m
  predicted : Vector m
  calibrationMethod : String
  measurementSource : String
  studyWindow : String
  heldOutReceipt : String

end EarthEmbeddingAdvanced
