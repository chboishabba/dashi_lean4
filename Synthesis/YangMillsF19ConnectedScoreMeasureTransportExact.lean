import Mathlib

/-!
The original F19 adjacent-pair log-source transport must retain the
connected score covariance when integrating the linked spectator. This
module uses the real measure integral, rather than independent products
of one-pair partition functions. Differentiation under the integral and
the original constrained Haar measure are explicit upstream obligations.

Wilson/Bałaban source: original 1536-face L=4 F19 two-pair Cartan slice
S = (2/N) [11(1-cos θ)+11(1-cos φ)+(1-cos(φ-θ))].
DASHI contribution: connected-score transport on the same measure.
-/
namespace DASHI.YangMills.F19
open MeasureTheory

def action (N θ φ : ℝ) : ℝ :=
  2/N * (11*(1-Real.cos θ)+11*(1-Real.cos φ)+(1-Real.cos (φ-θ)))

def thetaLogScore (N β θ φ : ℝ) : ℝ :=
  -β* (2/N) * (11*Real.sin θ-Real.sin (φ-θ))

def phiLogScore (N β θ φ : ℝ) : ℝ :=
  -β* (2/N) * (11*Real.sin φ+Real.sin (φ-θ))

def mixedLogScore (N β θ φ : ℝ) : ℝ :=
  β*(2/N)*Real.cos (φ-θ)

/-- The literal shared plaquette produces nonzero mixed log curvature at
the origin for every positive rank and positive inverse temperature. -/
theorem mixedLogScore_origin (N β : ℝ) (hN : 0 < N) (hβ : 0 < β) :
    0 < mixedLogScore N β 0 0 := by
  simp [mixedLogScore]
  positivity

/-- Conditional partition derivative identity. The second derivative of
the weight contains BOTH the mixed log derivative and the score product.
The log derivative after eliminating a spectator thus contains a connected
covariance, not just the average of the local mixed derivative. -/
theorem connected_score_transport {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (w a b c : X → ℝ)
    (Z Zθ Zφ Zθφ : ℝ)
    (hZ : Z ≠ 0)
    (hθ : Zθ = ∫ x, w x*a x ∂μ)
    (hφ : Zφ = ∫ x, w x*b x ∂μ)
    (hmix : Zθφ = ∫ x, w x*c x + w x*(a x*b x) ∂μ)
    (hc : Integrable (fun x => w x*c x) μ)
    (hab : Integrable (fun x => w x*(a x*b x)) μ) :
    (Z*Zθφ-Zθ*Zφ)/Z^2 =
      (∫ x, w x*c x ∂μ)/Z +
      ((∫ x, w x*(a x*b x) ∂μ)/Z -
        ((∫ x, w x*a x ∂μ)/Z)*((∫ x, w x*b x ∂μ)/Z)) := by
  rw [hθ,hφ,hmix,integral_add hc hab]
  field_simp [hZ] <;> ring

end DASHI.YangMills.F19
