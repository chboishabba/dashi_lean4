import Mathlib.Tactic
import Synthesis.RiemannG21ParityQuotientLinearAlgebra

/-!
# Literal G21 pole-parity transversality on one four-sample observer

Define the actual finite even/odd response entries from the same moment and
integrated-remainder objects used in the preceding determinant closures.  On
symmetric samples `r,-r,2r,-2r`, an off-line linear combination and a pole
nuisance combination agree iff the four scalar parity equations agree.

The common-radius strict even/odd minors force every such equality to have only
zero coefficients.  This proves rank-two transversality modulo the *literal
pole-parity span*.

Important firewall: this theorem does NOT assert that the eventual
post-explicit-formula/PNT nuisance span is definitionally this pole-parity span.
That transport is the next same-object obligation.
-/

noncomputable section

open MeasureTheory Set

namespace Synthesis

/-- Actual odd parity entry at one positive sample radius. -/
def literalOddResponseAt
    (R : ℝ) (w : ℝ → ℝ) (y r : ℝ) : ℝ :=
  oddCubicTrunc r (oddN1 R w y) (oddN3 R w y)
    + oddSixScaledRemainder R w y r

/-- Actual even parity entry at one positive sample radius. -/
def literalEvenResponseAt
    (R : ℝ) (w : ℝ → ℝ) (y r : ℝ) : ℝ :=
  evenQuadraticTrunc r (evenM0 R w y) (evenM2 R w y)
    + evenCosRemainder R w y r

/-- The determinant definitions are literally the 2x2 minors of these sampled
response pairs. -/
theorem literalOddFiniteDeterminant_eq_responseMinor
    {R : ℝ} {w : ℝ → ℝ} {a p r : ℝ} :
    literalOddFiniteDeterminant R w a p r =
      literalOddResponseAt R w a r * literalOddResponseAt R w p (2*r)
        - literalOddResponseAt R w a (2*r) * literalOddResponseAt R w p r := by
  rfl

theorem literalEvenFiniteDeterminant_eq_responseMinor
    {R : ℝ} {w : ℝ → ℝ} {a p r : ℝ} :
    literalEvenFiniteDeterminant R w a p r =
      literalEvenResponseAt R w a r * literalEvenResponseAt R w p (2*r)
        - literalEvenResponseAt R w a (2*r) * literalEvenResponseAt R w p r := by
  rfl

/-- Exact four-equation meaning of independence of the off-line even/odd pair
modulo the two pole-parity nuisance directions. -/
def PoleParityTransverseAt
    (R : ℝ) (w : ℝ → ℝ) (a p r : ℝ) : Prop :=
  ∀ c d lam mu : ℝ,
    c*literalEvenResponseAt R w a r + d*literalOddResponseAt R w a r
        = lam*literalEvenResponseAt R w p r + mu*literalOddResponseAt R w p r →
    c*literalEvenResponseAt R w a r - d*literalOddResponseAt R w a r
        = lam*literalEvenResponseAt R w p r - mu*literalOddResponseAt R w p r →
    c*literalEvenResponseAt R w a (2*r) + d*literalOddResponseAt R w a (2*r)
        = lam*literalEvenResponseAt R w p (2*r) + mu*literalOddResponseAt R w p (2*r) →
    c*literalEvenResponseAt R w a (2*r) - d*literalOddResponseAt R w a (2*r)
        = lam*literalEvenResponseAt R w p (2*r) - mu*literalOddResponseAt R w p (2*r) →
    c = 0 ∧ d = 0 ∧ lam = 0 ∧ mu = 0

/-- Two strict literal parity minors at the same radius give pole-parity
transversality at that observer. -/
theorem poleParityTransverseAt_of_negativeMinors
    {R : ℝ} {w : ℝ → ℝ} {a p r : ℝ}
    (he : literalEvenFiniteDeterminant R w a p r < 0)
    (ho : literalOddFiniteDeterminant R w a p r < 0) :
    PoleParityTransverseAt R w a p r := by
  intro c d lam mu h1 h2 h3 h4
  apply negativeParityMinors_force_modPole_independence
    (ea1 := literalEvenResponseAt R w a r)
    (ea2 := literalEvenResponseAt R w a (2*r))
    (ep1 := literalEvenResponseAt R w p r)
    (ep2 := literalEvenResponseAt R w p (2*r))
    (oa1 := literalOddResponseAt R w a r)
    (oa2 := literalOddResponseAt R w a (2*r))
    (op1 := literalOddResponseAt R w p r)
    (op2 := literalOddResponseAt R w p (2*r))
  · simpa [literalEvenFiniteDeterminant_eq_responseMinor] using he
  · simpa [literalOddFiniteDeterminant_eq_responseMinor] using ho
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- End-to-end pole-parity transversality witness from the literal taper
plateau/integrability hypotheses. -/
theorem exists_literalPoleParityTransverseAt
    {w : ℝ → ℝ} {a p R l m r0 : ℝ}
    (ha : 0 < a) (hap : a < p)
    (hl : 0 < l) (hlm : l < m) (hmr : m < r0) (hrR : r0 < R)
    (hwNonneg : ∀ x ∈ Icc (0:ℝ) R, 0 <= w x)
    (hwPos : ∀ x ∈ Ioo l r0, 0 < w x)
    (ho1a : Integrable (oddHeightWeight R w a) volume)
    (ho3a : Integrable (fun x => x^2 * oddHeightWeight R w a x) volume)
    (ho5a : Integrable (fun x => x^4 * oddHeightWeight R w a x) volume)
    (ho1p : Integrable (oddHeightWeight R w p) volume)
    (ho3p : Integrable (fun x => x^2 * oddHeightWeight R w p x) volume)
    (ho5p : Integrable (fun x => x^4 * oddHeightWeight R w p x) volume)
    (he0a : Integrable (evenHeightWeight R w a) volume)
    (he2a : Integrable (fun x => x^2 * evenHeightWeight R w a x) volume)
    (he4a : Integrable (fun x => x^4 * evenHeightWeight R w a x) volume)
    (he0p : Integrable (evenHeightWeight R w p) volume)
    (he2p : Integrable (fun x => x^2 * evenHeightWeight R w p x) volume)
    (he4p : Integrable (fun x => x^4 * evenHeightWeight R w p x) volume) :
    ∃ r : ℝ, 0 < r ∧ r <= 1 ∧ PoleParityTransverseAt R w a p r := by
  obtain ⟨r,hr,hr1,ho,he⟩ :=
    exists_commonRadius_literalParityMinors_neg
      ha hap hl hlm hmr hrR hwNonneg hwPos
      ho1a ho3a ho5a ho1p ho3p ho5p
      he0a he2a he4a he0p he2p he4p
  exact ⟨r,hr,hr1,poleParityTransverseAt_of_negativeMinors he ho⟩

end Synthesis
