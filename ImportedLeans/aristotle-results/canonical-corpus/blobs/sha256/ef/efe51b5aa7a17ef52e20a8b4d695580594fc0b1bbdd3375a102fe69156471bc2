/-
# Monotone endpoint transport for `detRestBound`

The quartic remainder bound is a polynomial with nonnegative coefficients in ten
nonnegative response quantities.  This file isolates that monotonicity once, so
window geometry can bound each response independently and then transport all bounds
into the literal `detRestBound`.

This is the concrete Lean version of the "detRestBound_mono" frontier recorded by
the Aristotle/Agda synchronization.
-/
import Zeta23Bridge.LiteralWeilWindowRatioSeparation

noncomputable section

namespace Zeta23Bridge
namespace LiteralWeilDetRestBoundMonotonicity

open Zeta23Bridge.LiteralWeilLeadingCoefficientCovariance
open Zeta23Bridge.LiteralWeilTargetDefectLeadingCoefficient
open Zeta23Bridge.LiteralWeilWindowRatioSeparation

/-- Endpoint/envelope copy of the literal quartic remainder polynomial. -/
def endpointDetRestBound
    (lam Pa Pb Q0a Q0b Q1a Q1b C0a C0b C1a C1b : ℝ) : ℝ :=
  2 * |lam| * (Pa * (C1b + C0b) + Pb * (C0a + C1a))
  + lam ^ 2 * (Pa * (Q1b + Q0b) + Pb * (Q0a + Q1a))
  + 2 * |lam| ^ 3 *
      (C0a * Q1b + C1a * Q0b + Q0a * C1b + Q1a * C0b)
  + lam ^ 4 * (Q0a * Q1b + Q1a * Q0b)

/-- `detRestBound` is monotone in every nonnegative response input. -/
theorem detRestBound_mono
    {p q0 q1 : ℝ → ℝ} {lam a b : ℝ}
    {Pa Pb Q0a Q0b Q1a Q1b C0a C0b C1a C1b : ℝ}
    (hp : Continuous p) (hpc : HasCompactSupport p)
    (hq0 : Continuous q0) (hq0c : HasCompactSupport q0)
    (hq1 : Continuous q1) (hq1c : HasCompactSupport q1)
    (hpn : ∀ u, 0 ≤ p u) (hq0n : ∀ u, 0 ≤ q0 u) (hq1n : ∀ u, 0 ≤ q1 u)
    (hPa : targetLeadingCoeff p a ≤ Pa)
    (hPb : targetLeadingCoeff p b ≤ Pb)
    (hQ0a : targetLeadingCoeff q0 a ≤ Q0a)
    (hQ0b : targetLeadingCoeff q0 b ≤ Q0b)
    (hQ1a : targetLeadingCoeff q1 a ≤ Q1a)
    (hQ1b : targetLeadingCoeff q1 b ≤ Q1b)
    (hC0a : covForm p q0 a ≤ C0a)
    (hC0b : covForm p q0 b ≤ C0b)
    (hC1a : covForm p q1 a ≤ C1a)
    (hC1b : covForm p q1 b ≤ C1b) :
    detRestBound p q0 q1 lam a b ≤
      endpointDetRestBound lam Pa Pb Q0a Q0b Q1a Q1b C0a C0b C1a C1b := by
  have hpA0 := targetLeadingCoeff_nonneg hp hpc hpn a
  have hpB0 := targetLeadingCoeff_nonneg hp hpc hpn b
  have hq0A0 := targetLeadingCoeff_nonneg hq0 hq0c hq0n a
  have hq0B0 := targetLeadingCoeff_nonneg hq0 hq0c hq0n b
  have hq1A0 := targetLeadingCoeff_nonneg hq1 hq1c hq1n a
  have hq1B0 := targetLeadingCoeff_nonneg hq1 hq1c hq1n b
  have hc0A0 := covForm_nonneg hp hpc hq0 hq0c hpn hq0n a
  have hc0B0 := covForm_nonneg hp hpc hq0 hq0c hpn hq0n b
  have hc1A0 := covForm_nonneg hp hpc hq1 hq1c hpn hq1n a
  have hc1B0 := covForm_nonneg hp hpc hq1 hq1c hpn hq1n b
  have hPa0 : 0 ≤ Pa := hpA0.trans hPa
  have hPb0 : 0 ≤ Pb := hpB0.trans hPb
  have hQ0a0 : 0 ≤ Q0a := hq0A0.trans hQ0a
  have hQ0b0 : 0 ≤ Q0b := hq0B0.trans hQ0b
  have hQ1a0 : 0 ≤ Q1a := hq1A0.trans hQ1a
  have hQ1b0 : 0 ≤ Q1b := hq1B0.trans hQ1b
  have hC0a0 : 0 ≤ C0a := hc0A0.trans hC0a
  have hC0b0 : 0 ≤ C0b := hc0B0.trans hC0b
  have hC1a0 : 0 ≤ C1a := hc1A0.trans hC1a
  have hC1b0 : 0 ≤ C1b := hc1B0.trans hC1b

  unfold detRestBound endpointDetRestBound
  gcongr

end LiteralWeilDetRestBoundMonotonicity
end Zeta23Bridge
