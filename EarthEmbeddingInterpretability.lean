import Mathlib
import EarthEmbeddingGeometry

/-!
# Interpretability of learned Earth-observation coordinates

This module does NOT label a learned coordinate as a physical variable.
It distinguishes (1) linear probe sensitivity, (2) decoder Jacobians,
(3) the full encoder-decoder chain, (4) tangent-restricted sensitivity,
(5) observational calibration, and (6) non-identifiability under invertible
coordinate reparameterisation.

References:
* Rahman, arXiv:2602.10354 (2026), empirical variable decoding.
* Rahman et al., arXiv:2604.18715 (2026), local tangent rotations.
* Feng et al., arXiv:2607.03949 (2026), nested TESSERA v2 outputs.
* University of Cambridge, https://github.com/ucam-eo/tessera

No automatic transfer of CONUS empirical accuracy to Woogaroo is asserted.
-/

namespace EarthEmbeddingInterpretability

abbrev V (d : Nat) := Fin d → ℝ

/-- Each learned coordinate has an index. A physical meaning must be
    established separately by a probe and external calibration. -/
structure LearnedEncoder (Input : Type*) (d : Nat) where
  encode : Input → V d
  modelIdentifier : String
  checkpointHash : String
  preprocessingReceipt : String

structure EnvironmentalTarget (m : Nat) where
  variableName : Fin m → String
  unit : Fin m → String
  groundTruthSource : String
  acquisitionInterval : String

/-- A linear probe and its weights are model parameters, not causal effects. -/
structure LinearProbe (d m : Nat) where
  weights : V d →ₗ[ℝ] V m
  offset : V m
  fitReceipt : String
  holdoutReceipt : String

def LinearProbe.predict {d m : Nat} (p : LinearProbe d m) (e : V d) : V m :=
  p.weights e + p.offset

/-- A nonlinear decoder is carried together with a proposed local
    derivative. The derivative field is *not* trusted as true without a
    differentiability certificate. -/
structure LocalPhysicalDecoder (d m : Nat) where
  predict : V d → V m
  jacobian : V d → (V d →L[ℝ] V m)
  derivativeValid : ∀ e, HasFDerivAt predict (jacobian e) e
  calibrationSource : String
  calibrationDomain : Set (V d)
  validationReceipt : String

/-- The encoder is smooth only when a separate mathematical certificate
    identifies its Fréchet derivative at each input in this typed domain. -/
structure DifferentiableEncoder (p d : Nat) where
  encode : V p → V d
  jacobian : V p → (V p →L[ℝ] V d)
  derivativeValid : ∀ x, HasFDerivAt encode (jacobian x) x
  checkpointHash : String
  preprocessingReceipt : String

/-- Source-code-only chain rule: a differentiable open-weight encoder and
    a differentiable supervised decoder compose, with a composed Jacobian. -/
theorem encoder_decoder_chain {p d m : Nat}
    (encoder : DifferentiableEncoder p d)
    (decoder : LocalPhysicalDecoder d m)
    (x : V p) :
    HasFDerivAt (decoder.predict ∘ encoder.encode)
      ((decoder.jacobian (encoder.encode x)).comp (encoder.jacobian x)) x := by
  exact (decoder.derivativeValid (encoder.encode x)).comp x
    (encoder.derivativeValid x)

/-- Sensor-space sensitivity is the decoder's local Jacobian composed
    with the encoder Jacobian, not the derivative of the decoder alone. -/
def sensorSensitivity {p d m : Nat}
    (encoder : DifferentiableEncoder p d)
    (decoder : LocalPhysicalDecoder d m) (x : V p) :
    V p →L[ℝ] V m :=
  (decoder.jacobian (encoder.encode x)).comp (encoder.jacobian x)

theorem sensorSensitivity_apply {p d m : Nat}
    (encoder : DifferentiableEncoder p d)
    (decoder : LocalPhysicalDecoder d m)
    (x δ : V p) :
    sensorSensitivity encoder decoder x δ =
      decoder.jacobian (encoder.encode x) (encoder.jacobian x δ) := by
  rfl

/-- Given a tangent map, attribute only displacements that are actually
    reachable through the local chart. This does not certify the chart. -/
def tangentRestrictedSensitivity {d k m : Nat}
    (decoder : LocalPhysicalDecoder d m) (center : V d)
    (tangent : V k →L[ℝ] V d) : V k →L[ℝ] V m :=
  (decoder.jacobian center).comp tangent

theorem tangentRestrictedSensitivity_apply {d k m : Nat}
    (decoder : LocalPhysicalDecoder d m) (center : V d)
    (tangent : V k →L[ℝ] V d) (direction : V k) :
    tangentRestrictedSensitivity decoder center tangent direction =
      decoder.jacobian center (tangent direction) := by
  rfl

/-- Reparameterisation makes individual learned coordinate meanings
    non-identifiable without a chosen basis or further constraints.
    This is an exact algebraic observation, not a hypothesis about a model. -/
theorem invertible_coordinates_same_predictions
    {Input A B Output : Type*}
    (encoder : Input → A)
    (coordinateChange : A → B)
    (undoChange : B → A)
    (decoder : A → Output)
    (hundo : Function.LeftInverse undoChange coordinateChange)
    (x : Input) :
    (decoder ∘ undoChange) ((coordinateChange ∘ encoder) x) =
      (decoder ∘ encoder) x := by
  exact congrArg decoder (hundo (encoder x))

/-- The TESSERA Matryoshka prefix selects a smaller carrier but carries
    no automatic accuracy or physical identifiability guarantee. -/
def matryoshkaPrefix (k : Nat) (hk : k ≤ 128) (e : V 128) : V k :=
  EarthEmbeddingWoogaroo.prefix e k hk

theorem nested_matryoshka {j k : Nat}
    (hj : j ≤ k) (hk : k ≤ 128) (e : V 128) :
    EarthEmbeddingWoogaroo.prefix (matryoshkaPrefix k hk e) j hj =
      matryoshkaPrefix j (Nat.le_trans hj hk) e := by
  exact EarthEmbeddingWoogaroo.prefix_compose e hk hj

/-- Empirical interpretability experiment, with honest separate receipts.
    Measured R² or decoder performance is not inferred from a Jacobian. -/
structure InterpretationExperiment (d m : Nat) where
  target : EnvironmentalTarget m
  decoder : LocalPhysicalDecoder d m
  spatialHoldoutReceipt : String
  temporalHoldoutReceipt : String
  uncertaintyAndCalibrationReceipt : String
  outOfRegionTransferReceipt : String
  modelAndInputVersion : String

/-- A counterfactual perturbation is marked as physically admissible by
    a separate predicate. Arbitrary embedding edits are not interventions
    in climate, habitat or hydrology. -/
structure AdmissiblePerturbation (Input : Type*) where
  admissible : Input → Input → Prop
  physicalJustificationReceipt : String
  validationReceipt : String

/-- Conditional paired intervention analysis at the encoder level. -/
def InterventionResponse {Input : Type*} {d m : Nat}
    (encoder : LearnedEncoder Input d)
    (decoder : V d → V m)
    (before after : Input) : V m :=
  decoder (encoder.encode after) - decoder (encoder.encode before)

end EarthEmbeddingInterpretability
