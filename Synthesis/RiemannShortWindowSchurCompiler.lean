import Synthesis.RiemannHighSchurFrontier
import Zeta23Bridge.LiteralWeilWindowSchurInstance
import Zeta23Bridge.NormalizedNarrowWindowCertificate

/-!
# Short-window compiler for the literal Schur high lane

The existing window-Schur construction proves response separation on normalized
window tapers.  The literal high explicit-formula lane additionally requires
every taper to be supported inside |u| < log 2 so that the prime channel
vanishes identically.

This file makes that transport structural.  A normalized window triple whose
three upper endpoints lie below log 2 automatically gives short support for
p, q0, q1 and for both polarized window-pair tapers p + lambda*qj.

No zero-distribution estimate enters here.
-/

noncomputable section

open scoped Real
open Set

namespace Synthesis

open Zeta23Bridge.LiteralWeilWindowRatioSeparation
open Zeta23Bridge.NormalizedNarrowWindowCertificate
open Zeta23Bridge.LiteralWeilWindowSchurAdmission

structure ShortNormalizedWindowTriple where
  triple : NormalizedNarrowWindowTriple
  pUpperShort : triple.be0 < Real.log 2
  q0UpperShort : triple.be1 < Real.log 2
  q1UpperShort : triple.be2 < Real.log 2

namespace ShortNormalizedWindowTriple

variable (w : ShortNormalizedWindowTriple)

theorem p_short :
    ∀ u, w.triple.p u ≠ 0 → |u| < Real.log 2 := by
  intro u hu
  have hs := w.triple.pWindow.supp u hu
  exact lt_of_le_of_lt hs.2 w.pUpperShort

theorem q0_short :
    ∀ u, w.triple.q0 u ≠ 0 → |u| < Real.log 2 := by
  intro u hu
  have hs := w.triple.q0Window.supp u hu
  exact lt_of_le_of_lt hs.2 w.q0UpperShort

theorem q1_short :
    ∀ u, w.triple.q1 u ≠ 0 → |u| < Real.log 2 := by
  intro u hu
  have hs := w.triple.q1Window.supp u hu
  exact lt_of_le_of_lt hs.2 w.q1UpperShort

/-- Each of the two polarized window tapers remains prime-invisible. -/
theorem windowPair_short (lam : ℝ) :
    ∀ j u,
      windowPair w.triple.p w.triple.q0 w.triple.q1 lam j u ≠ 0 →
      |u| < Real.log 2 := by
  intro j u hu
  fin_cases j
  · rw [windowPair_zero] at hu
    by_cases hp : w.triple.p u = 0
    · have hq : w.triple.q0 u ≠ 0 := by
        intro hq
        apply hu
        simp [hp, hq]
      exact w.q0_short u hq
    · exact w.p_short u hp
  · rw [windowPair_one] at hu
    by_cases hp : w.triple.p u = 0
    · have hq : w.triple.q1 u ≠ 0 := by
        intro hq
        apply hu
        simp [hp, hq]
      exact w.q1_short u hq
    · exact w.p_short u hp

/-- Prime invisibility for every sampling radius follows immediately. -/
theorem windowPair_primeInvisible
    (w : ShortNormalizedWindowTriple) (lam t r : ℝ) :
    ∀ j,
      Zeta23Bridge.LiteralWeilParityBalance.evenConeFunctional
        (Zeta23Bridge.LiteralWeilParityBalance.primeVec
          (Zeta23Bridge.LiteralWeilParityBalance.sampleFam
            (windowPair w.triple.p w.triple.q0 w.triple.q1 lam j) t r))
        = 0 := by
  intro j
  exact
    Zeta23Bridge.LiteralWeilPrimeEvenCone.primeConeValue_eq_zero_of_short_taper
      (w.windowPair_short lam j) t r

end ShortNormalizedWindowTriple

end Synthesis
