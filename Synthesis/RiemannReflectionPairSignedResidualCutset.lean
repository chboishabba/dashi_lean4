import Synthesis.RiemannReflectionDoubledProjectiveGate

/-!
# Reflection-pair signed residual cutset

The same-ordinate fibre does not need to be finitely enumerated or recursively
Schur-deleted on the reflection-pair route.

For an off-line target rho at ordinate t, the functional-equation partner is a
distinct same-ordinate zero with exactly the same two-radius defect.  Every
other same-ordinate zero defect is nonnegative on GateData.  Hence

  2 * D_rho <= D_cluster.

The literal short-support balance already identifies the cluster defect with the
three external projective channels

  D_cluster = D_off + D_Gamma + D_pole.

Therefore a *signed* external upper strictly below the doubled target signal is
already contradictory:

  D_off + D_Gamma + D_pole < 2 * D_rho.

This cutset deliberately avoids:
  * finite/Fintype assumptions on SameOrd t;
  * nuisance selection;
  * Schur projection of the same-ordinate fibre;
  * absolute values on the combined external residual.

It is the consumer shape to which the normalized aggregate Off and canonical
Gamma machinery can be attached.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.LiteralWeilProjectiveSeparationGate
open Zeta23Bridge.LiteralWeilTwoRadiusSeparationGate

structure ReflectionPairSignedResidualPayment
    {g : ℝ → ℝ} {t r Lambda : ℝ}
    (rho : Zeros) where
  gate : GateData g t r Lambda
  targetOrdinate : (rho : ℂ).im = t
  targetOffLine : heightOf rho ≠ 0

  externalStrict :
    offOrdProjectiveDefect g t r
      + gammaProjectiveDefect g t r
      + poleProjectiveDefect g t r
      <
    2 * zeroHeightDefect g r rho

theorem false_of_reflectionPairSignedResidualPayment
    {g : ℝ → ℝ} {t r Lambda : ℝ} {rho : Zeros}
    (P : ReflectionPairSignedResidualPayment
      (g := g) (t := t) (r := r) (Lambda := Lambda) rho) :
    False := by
  have hlo :
      2 * zeroHeightDefect g r rho
        <= clusterHeightDefect g t r :=
    gateData_two_targetDefect_le_cluster
      P.gate P.targetOrdinate P.targetOffLine
  have hbal :
      clusterHeightDefect g t r
        =
      offOrdProjectiveDefect g t r
        + gammaProjectiveDefect g t r
        + poleProjectiveDefect g t r :=
    clusterHeightDefect_eq_threeProjectiveChannels
      P.gate.smooth P.gate.compactSupport P.gate.isEven
      P.gate.short t r
  rw [hbal] at hlo
  linarith

/--
A componentwise budget compiler for callers that still obtain separate signed
upper bounds.  The final contradiction itself remains signed and only sees their
sum.
-/
theorem false_of_reflectionPairSignedChannelBounds
    {g : ℝ → ℝ} {t r Lambda : ℝ} {rho : Zeros}
    (hd : GateData g t r Lambda)
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0)
    {Boff Bgamma Bpole : ℝ}
    (hoffBound : offOrdProjectiveDefect g t r <= Boff)
    (hgammaBound : gammaProjectiveDefect g t r <= Bgamma)
    (hpoleBound : poleProjectiveDefect g t r <= Bpole)
    (hstrict :
      Boff + Bgamma + Bpole < 2 * zeroHeightDefect g r rho) :
    False := by
  apply false_of_reflectionPairSignedResidualPayment
    (P := {
      gate := hd
      targetOrdinate := him
      targetOffLine := hoff
      externalStrict := by
        linarith
    })

/--
Prize-facing wrapper for this cutset.  The producer is asked for the exact
literal GateData and one signed external payment only under the off-line
hypothesis.
-/
structure HighReflectionPairSignedWitness (rho : Zeros) (t : ℝ) where
  g : ℝ → ℝ
  r : ℝ
  Lambda : ℝ
  payment :
    ReflectionPairSignedResidualPayment
      (g := g) (t := t) (r := r) (Lambda := Lambda) rho

theorem false_of_highReflectionPairSignedWitness
    {rho : Zeros} {t : ℝ}
    (W : HighReflectionPairSignedWitness rho t) :
    False :=
  false_of_reflectionPairSignedResidualPayment W.payment

theorem high_zero_realPart_eq_half_of_reflectionPairSignedProducer
    {rho : Zeros} {t : ℝ}
    (him : (rho : ℂ).im = t)
    (producer :
      heightOf rho ≠ 0 ->
        HighReflectionPairSignedWitness rho t) :
    (rho : ℂ).re = 1 / 2 := by
  by_contra hre
  have hoff : heightOf rho ≠ 0 := by
    intro hz
    apply hre
    unfold heightOf at hz
    linarith
  exact false_of_highReflectionPairSignedWitness (producer hoff)

end Synthesis
