import Mathlib
import EarthEmbeddingInterpretability

/-!
# Fixed-mask and acquisition-index semantics of TESSERA gradient probes

Upstream v2 students use discrete per-pixel valid counts and sequence bins.
Backpropagation is through the selected tensor and fixed standardisation,
not through cloud filtering, integer day-of-year, source selection or
the padding/binning decision. These are explicitly a *frozen* selection.

Source: https://github.com/ucam-eo/tessera/blob/master/tessera_infer_v2/student/infer.py
-/

namespace EarthEmbeddingAcquisition

abbrev Signal (n : Nat) := Fin n → ℝ

structure FixedAcquisition (n k : Nat) where
  selectedIndex : Fin k → Fin n
  originalSource : String
  cloudMaskReceipt : String
  dayOfYearReceipt : String
  binningVersion : String

def selectedSignal {n k : Nat} (a : FixedAcquisition n k)
    (signal : Signal n) : Signal k :=
  fun j => signal (a.selectedIndex j)

/-- Modifying only observations not selected by the frozen preprocessing
    cannot change the input tensor passed to the student. -/
theorem selected_invariance {n k : Nat} (a : FixedAcquisition n k)
    (x y : Signal n)
    (h : ∀ j, x (a.selectedIndex j) = y (a.selectedIndex j)) :
    selectedSignal a x = selectedSignal a y := by
  funext j
  exact h j

/-- The selected representation and any downstream decoder share that
    invariance, irrespective of the decoder architecture. -/
theorem decoder_selection_invariance {n k : Nat}
    (a : FixedAcquisition n k)
    (x y : Signal n) (decoder : Signal k → ℝ)
    (h : ∀ j, x (a.selectedIndex j) = y (a.selectedIndex j)) :
    decoder (selectedSignal a x) = decoder (selectedSignal a y) := by
  rw [selected_invariance a x y h]

/-- Normalisation is source-specific, with a strictly positive denominator.
    The discrete mask itself is *not* differentiated. -/
structure CalibratedBand where
  mean : ℝ
  scale : ℝ
  scalePositive : 0 < scale
  bandName : String
  sourceOrbit : String

def standardize (band : CalibratedBand) (raw : ℝ) : ℝ :=
  (raw - band.mean) / band.scale

theorem standardize_difference (band : CalibratedBand) (x y : ℝ) :
    standardize band x - standardize band y =
      (x - y) / band.scale := by
  unfold standardize
  ring

/-- A fixed local affine probe has an exact linear response on selected
    input vectors. The statement does not interpret the coefficient physically. -/
theorem affine_probe_difference {n : Nat}
    (w x y : Signal n) (bias : ℝ) :
    ((∑ i, w i * x i) + bias) - ((∑ i, w i * y i) + bias) =
      ∑ i, w i * (x i - y i) := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- Method metadata for an actual gradient producer; no populated receipts
    or successful runs are constructed automatically from this structure. -/
structure GradientReceipt where
  checkpointSha256 : String
  preprocessingSourceRevision : String
  sensorObservationSha256 : String
  sourceBandOrder : String
  fixedMaskAndBinningReceipt : String
  gradientOrIG : String
  completenessResidual : String
  independentFieldLabels : String
  withheldSpatialAndTemporalBlocks : String

end EarthEmbeddingAcquisition
