import Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition

/-!
# Exact projective-to-centered gauge bridge

The live reflection-pair high cut consumes the two-radius projective defect

  D_C(r) = C(2r) A_0(r) - C(r) A_0(2r),

where A_0(s)=evenResp g 0 s.

Most normalized Fourier/RvM machinery is naturally stated for radius-centered
differences C(s)-C(0).  These observables are related, but they are not
definitionally identical.

The correct bridge is the projective gauge invariance

  D_{C-c A_0}(r) = D_C(r)

for every scalar c.

If A_0(0) != 0, choose

  c = C(0)/A_0(0).

Then the gauged channel vanishes at radius zero.  Moreover

  (C-cA_0)(s)
    = (C(s)-C(0)) - c (A_0(s)-A_0(0)),

so the exact projective consumer is reconstructed from the centered radius
differences at r and 2r, with no balance theorem and no absolute-value loss.

This is the same-object interface required before one may reuse the normalized
centered Off/RvM machinery inside the projective reflection-pair cutset.
-/

noncomputable section

open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilEvenChannelTaper
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition

def onLineRadiusProfile (g : ℝ → ℝ) : ℝ → ℝ :=
  fun s => evenResp g 0 s

def radiusCenteredChannel (C : ℝ → ℝ) (s : ℝ) : ℝ :=
  C s - C 0

def projectiveGaugeChannel
    (C : ℝ → ℝ) (g : ℝ → ℝ) (c : ℝ) : ℝ → ℝ :=
  fun s => C s - c * onLineRadiusProfile g s

/--
Projective defects only see a channel modulo the one-dimensional on-line
profile.  This is the determinant identity det(C-cA,A)=det(C,A).
-/
theorem channelProjectiveDefect_projectiveGauge
    (C : ℝ → ℝ) (g : ℝ → ℝ) (c r : ℝ) :
    channelProjectiveDefect (projectiveGaugeChannel C g c) g r
      =
    channelProjectiveDefect C g r := by
  unfold channelProjectiveDefect projectiveGaugeChannel onLineRadiusProfile
  ring

/--
Choose the unique scalar gauge which kills the radius-zero value.
-/
theorem projectiveGaugeChannel_zero
    {C : ℝ → ℝ} {g : ℝ → ℝ}
    (hA0 : onLineRadiusProfile g 0 ≠ 0) :
    projectiveGaugeChannel C g
      (C 0 / onLineRadiusProfile g 0) 0 = 0 := by
  unfold projectiveGaugeChannel
  field_simp [hA0]

/--
After the radius-zero gauge choice, the gauged channel is exactly the centered
channel minus the same scalar multiple of the centered on-line profile.
-/
theorem projectiveGaugeChannel_eq_centered
    {C : ℝ → ℝ} {g : ℝ → ℝ}
    (hA0 : onLineRadiusProfile g 0 ≠ 0)
    (s : ℝ) :
    projectiveGaugeChannel C g
        (C 0 / onLineRadiusProfile g 0) s
      =
    radiusCenteredChannel C s
      -
    (C 0 / onLineRadiusProfile g 0)
      * radiusCenteredChannel (onLineRadiusProfile g) s := by
  unfold projectiveGaugeChannel radiusCenteredChannel
  have hnorm :
      (C 0 / onLineRadiusProfile g 0) * onLineRadiusProfile g 0
        = C 0 := by
    field_simp [hA0]
  linarith

/--
Exact projective-to-centered reconstruction.  No estimate occurs here.

The projective defect is the two-radius determinant of the gauge-centered
channel, and each gauged value is expressed only through radius-centered
differences.
-/
theorem channelProjectiveDefect_eq_centeredGauge
    {C : ℝ → ℝ} {g : ℝ → ℝ}
    (hA0 : onLineRadiusProfile g 0 ≠ 0)
    (r : ℝ) :
    channelProjectiveDefect C g r
      =
    (radiusCenteredChannel C (2*r)
        - (C 0 / onLineRadiusProfile g 0)
          * radiusCenteredChannel (onLineRadiusProfile g) (2*r))
        * onLineRadiusProfile g r
      -
    (radiusCenteredChannel C r
        - (C 0 / onLineRadiusProfile g 0)
          * radiusCenteredChannel (onLineRadiusProfile g) r)
        * onLineRadiusProfile g (2*r) := by
  rw [← channelProjectiveDefect_projectiveGauge
      C g (C 0 / onLineRadiusProfile g 0) r]
  unfold channelProjectiveDefect
  rw [projectiveGaugeChannel_eq_centered hA0,
      projectiveGaugeChannel_eq_centered hA0]
  rfl

/--
Specialization to the literal off-ordinate channel consumed by the reflection
pair signed cutset.
-/
theorem offOrdProjectiveDefect_eq_centeredGauge
    {g : ℝ → ℝ} {t r : ℝ}
    (hA0 : onLineRadiusProfile g 0 ≠ 0) :
    offOrdProjectiveDefect g t r
      =
    (radiusCenteredChannel (offOrdChannel g t) (2*r)
        - (offOrdChannel g t 0 / onLineRadiusProfile g 0)
          * radiusCenteredChannel (onLineRadiusProfile g) (2*r))
        * onLineRadiusProfile g r
      -
    (radiusCenteredChannel (offOrdChannel g t) r
        - (offOrdChannel g t 0 / onLineRadiusProfile g 0)
          * radiusCenteredChannel (onLineRadiusProfile g) r)
        * onLineRadiusProfile g (2*r) := by
  unfold offOrdProjectiveDefect
  exact channelProjectiveDefect_eq_centeredGauge hA0 r

end Synthesis
