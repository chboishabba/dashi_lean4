import Mathlib.Tactic

/-!
Corrected W2 orbit compiler. R745 identifies the complete pointwise orbit
residual with three times (combined work minus physical packet surplus);
R760 doubles it and R781 partitions it. The viscous contribution must
remain explicit, and the required signed payment is NONNEGATIVITY.
No analytic payment, all-cutoff estimate or Clay conclusion is claimed.
-/

namespace NSBControl
namespace SignedOrbitPacketWeld

structure Instant where
  separated : ℝ
  touched : ℝ
  twoNu : ℝ
  margin : ℝ
  dissipationRate : ℝ
  combinedRate : ℝ
  packetRate : ℝ

def orbitRate (s : Instant) : ℝ :=
  s.separated + s.touched +
    6 * (s.twoNu - s.margin) * s.dissipationRate

structure InstantWeld (s : Instant) : Prop where
  exact : orbitRate s = 6 * (s.combinedRate - s.packetRate)

theorem pointwiseW2 (s : Instant) (w : InstantWeld s)
    (payment : 0 ≤ orbitRate s) :
    s.packetRate ≤ s.combinedRate := by
  rw [w.exact] at payment
  linarith

structure Integrated where
  orbitPayment : ℝ
  integratedPacket : ℝ
  integratedCombined : ℝ
  initialCritical : ℝ
  terminalCritical : ℝ
  dissipation : ℝ
  margin : ℝ
  integratedWeighted : ℝ
  initialMixed : ℝ
  terminalMixed : ℝ
  uniformBound : ℝ

structure IntegratedWeld (s : Integrated) : Prop where
  orbit_to_packet :
    s.orbitPayment = 6 * (s.integratedCombined - s.integratedPacket)
  packet_to_growth :
    s.integratedPacket =
      s.terminalCritical - s.initialCritical + s.margin * s.dissipation
  combined_to_weighted :
    s.integratedCombined =
      12 * (s.integratedWeighted + s.terminalMixed - s.initialMixed)

theorem integratedW2 (s : Integrated) (w : IntegratedWeld s)
    (payment : 0 ≤ s.orbitPayment) :
    s.integratedPacket ≤ s.integratedCombined := by
  rw [w.orbit_to_packet] at payment
  linarith

theorem signedOrbitBarrier
    (s : Integrated) (w : IntegratedWeld s)
    (payment : 0 ≤ s.orbitPayment)
    (w1 : s.integratedWeighted + s.terminalMixed ≤ s.uniformBound)
    (initialMass : 0 ≤ s.initialMixed) :
    s.terminalCritical + s.margin * s.dissipation ≤
      s.initialCritical + 12 * s.uniformBound := by
  have h := integratedW2 s w payment
  rw [w.packet_to_growth, w.combined_to_weighted] at h
  linarith

theorem uniformMarginBarrier
    (s : Integrated) (w : IntegratedWeld s)
    (payment : 0 ≤ s.orbitPayment)
    (w1 : s.integratedWeighted + s.terminalMixed ≤ s.uniformBound)
    (initialMass : 0 ≤ s.initialMixed)
    (dissNonnegative : 0 ≤ s.dissipation)
    (uniformMargin : ℝ)
    (marginFloor : uniformMargin ≤ s.margin) :
    s.terminalCritical + uniformMargin * s.dissipation ≤
      s.initialCritical + 12 * s.uniformBound := by
  have h := signedOrbitBarrier s w payment w1 initialMass
  nlinarith

theorem allCutoffsBarrier
    {Time : Type*} (family : ℕ → Time → Integrated)
    (uniformMargin : ℝ)
    (hWeld : ∀ n t, IntegratedWeld (family n t))
    (hSigned : ∀ n t, 0 ≤ (family n t).orbitPayment)
    (hW1 : ∀ n t,
      (family n t).integratedWeighted +
        (family n t).terminalMixed ≤ (family n t).uniformBound)
    (hInitial : ∀ n t, 0 ≤ (family n t).initialMixed)
    (hDiss : ∀ n t, 0 ≤ (family n t).dissipation)
    (hMargin : ∀ n t, uniformMargin ≤ (family n t).margin) :
    ∀ n t,
      (family n t).terminalCritical +
        uniformMargin * (family n t).dissipation ≤
          (family n t).initialCritical + 12 * (family n t).uniformBound := by
  intro n t
  exact uniformMarginBarrier (family n t) (hWeld n t) (hSigned n t)
    (hW1 n t) (hInitial n t) (hDiss n t)
    uniformMargin (hMargin n t)


/-- Canonical retained-margin specialization.  If the physical viscosity nu is
    positive and the integrated slice uses margin = nu, the uniform-margin
    step needs no extra cutoff-wise lower-bound theorem: the common floor is
    literally nu. -/
theorem canonicalViscosityMarginBarrier
    (s : Integrated) (w : IntegratedWeld s)
    (payment : 0 ≤ s.orbitPayment)
    (w1 : s.integratedWeighted + s.terminalMixed ≤ s.uniformBound)
    (initialMass : 0 ≤ s.initialMixed)
    (dissNonnegative : 0 ≤ s.dissipation)
    (nu : ℝ)
    (nuPositive : 0 < nu)
    (marginIsNu : s.margin = nu) :
    s.terminalCritical + nu * s.dissipation ≤
      s.initialCritical + 12 * s.uniformBound := by
  have h := signedOrbitBarrier s w payment w1 initialMass
  rw [marginIsNu] at h
  exact h

/-- Direct complete-target compiler mirroring Agda R817.  The only analytic
    input is nonnegativity of the exact complete signed target; no separated
    cancellation is assumed. -/
structure CompleteSignedTarget (s : Integrated) : Prop where
  completeTarget : ℝ
  completeTarget_is_orbitPayment :
    completeTarget = s.orbitPayment

theorem completeTargetBarrier
    (s : Integrated) (w : IntegratedWeld s)
    (target : CompleteSignedTarget s)
    (targetNonnegative : 0 ≤ target.completeTarget)
    (w1 : s.integratedWeighted + s.terminalMixed ≤ s.uniformBound)
    (initialMass : 0 ≤ s.initialMixed) :
    s.terminalCritical + s.margin * s.dissipation ≤
      s.initialCritical + 12 * s.uniformBound := by
  have payment : 0 ≤ s.orbitPayment := by
    rwa [← target.completeTarget_is_orbitPayment]
  exact signedOrbitBarrier s w payment w1 initialMass

end SignedOrbitPacketWeld
end NSBControl
