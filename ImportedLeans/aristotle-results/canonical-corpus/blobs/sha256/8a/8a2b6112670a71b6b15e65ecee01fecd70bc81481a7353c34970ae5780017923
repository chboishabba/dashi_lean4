/-
# Shared normalized narrow-window certificate

This is the Lean-side implementation of the cross-pollinated architecture:
construct the actual normalized windows once, then let all response, residual and
Schur consumers use the same exact object.

No existence theorem is claimed here.  The existing window-existence and future
normalization owners are producers of this certificate.
-/
import Zeta23Bridge.LiteralWeilWindowRatioSeparation

noncomputable section

open scoped Real
open MeasureTheory Set

namespace Zeta23Bridge
namespace NormalizedNarrowWindowCertificate

open Zeta23Bridge.LiteralWeilWindowRatioSeparation

/-- A window taper together with its exact unit-mass normalization receipt. -/
structure NormalizedWindowTaper (f : ℝ → ℝ) (lo hi : ℝ) : Prop where
  window : WindowTaper f lo hi
  unitMass : (∫ u : ℝ, f u) = 1

namespace NormalizedWindowTaper

variable {f : ℝ → ℝ} {lo hi : ℝ}

theorem continuous (h : NormalizedWindowTaper f lo hi) : Continuous f := h.window.cont

theorem compactSupport (h : NormalizedWindowTaper f lo hi) : HasCompactSupport f := h.window.cpt

theorem nonneg (h : NormalizedWindowTaper f lo hi) : ∀ u, 0 ≤ f u := h.window.nonneg

theorem positiveMass (h : NormalizedWindowTaper f lo hi) : 0 < ∫ u : ℝ, f u := h.window.mass

end NormalizedWindowTaper

/-- The one-zero Schur window geometry, represented once and shared by every consumer. -/
structure NormalizedNarrowWindowTriple where
  p : ℝ → ℝ
  q0 : ℝ → ℝ
  q1 : ℝ → ℝ
  al0 : ℝ
  be0 : ℝ
  al1 : ℝ
  be1 : ℝ
  al2 : ℝ
  be2 : ℝ
  pNorm : NormalizedWindowTaper p al0 be0
  q0Norm : NormalizedWindowTaper q0 al1 be1
  q1Norm : NormalizedWindowTaper q1 al2 be2
  lowPositive : 0 < al0
  lowOrdered : al0 ≤ be0
  lowMiddleSeparated : be0 < al1
  middleOrdered : al1 ≤ be1
  middleTopSeparated : be1 < al2

namespace NormalizedNarrowWindowTriple

variable (w : NormalizedNarrowWindowTriple)

theorem pWindow : WindowTaper w.p w.al0 w.be0 := w.pNorm.window

theorem q0Window : WindowTaper w.q0 w.al1 w.be1 := w.q0Norm.window

theorem q1Window : WindowTaper w.q1 w.al2 w.be2 := w.q1Norm.window

theorem allContinuous : Continuous w.p ∧ Continuous w.q0 ∧ Continuous w.q1 :=
  ⟨w.pNorm.continuous, w.q0Norm.continuous, w.q1Norm.continuous⟩

theorem allCompactSupport :
    HasCompactSupport w.p ∧ HasCompactSupport w.q0 ∧ HasCompactSupport w.q1 :=
  ⟨w.pNorm.compactSupport, w.q0Norm.compactSupport, w.q1Norm.compactSupport⟩

theorem allNonnegative :
    (∀ u, 0 ≤ w.p u) ∧ (∀ u, 0 ≤ w.q0 u) ∧ (∀ u, 0 ≤ w.q1 u) :=
  ⟨w.pNorm.nonneg, w.q0Norm.nonneg, w.q1Norm.nonneg⟩

end NormalizedNarrowWindowTriple

end NormalizedNarrowWindowCertificate
end Zeta23Bridge
