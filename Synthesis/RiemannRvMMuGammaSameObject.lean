import Zeta23.ExplicitFormula
import Zeta23Bridge.LiteralWeilParityBalance
import Synthesis.RiemannGammaCenteredKernelCompactBridge
import Synthesis.RiemannZeta23RvMProducerBridge

/-!
# Same-object weld: RvM smooth measure = literal Weil Gamma channel

The upstream Riemann--von Mangoldt proof uses the exact archimedean density
`Zeta23.mu`:

  N(T1,T2)
    = zeta-contour remainder + integral_{T1}^{T2} mu(tau) d tau.

The literal Weil explicit formula used by this RH branch defines its Gamma term as

  (1/(2*pi)) * integral paperFT(k)(r) * gammaBracket(r) dr.

Zeta23 proves these are exactly the same object:

  gammaTerm(k) = integral paperFT(k)(tau) * mu(tau) d tau.

This file imports that identity onto the literal Gamma term already used by the
four-sample/parity balance.  Consequently a spectral-measure decomposition of
the zero sum against the exact RvM smooth measure must use THIS Gamma channel;
it must not add an independent logarithmic-density main term on top of Gamma.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance

/--
The literal Weil Gamma term is exactly pairing against the RvM smooth density
`mu`.
-/
theorem literalGammaTerm_eq_rvMMuPair (k : ℝ → ℂ) :
    gammaTerm k
      =
    ∫ tau : ℝ, paperFT k tau * (Zeta23.mu tau : ℂ) := by
  unfold gammaTerm
  exact Zeta23.EF.gamma_term k

/--
Signed form matching the literal five-term balance, where the Gamma vector
enters as `-gammaTerm`.
-/
theorem neg_literalGammaTerm_eq_neg_rvMMuPair (k : ℝ → ℂ) :
    - gammaTerm k
      =
    - ∫ tau : ℝ, paperFT k tau * (Zeta23.mu tau : ℂ) := by
  rw [literalGammaTerm_eq_rvMMuPair]

/--
The RvM smooth measure and the explicit-formula Gamma channel use the same
literal zeta analytic package.  This theorem keeps the equality theorem-facing
so aggregate H2 cannot accidentally count the smooth main term twice.
-/
theorem rvMSmoothMeasure_is_literalGammaChannel :
    (fun k : ℝ → ℂ => gammaTerm k)
      =
    fun k : ℝ → ℂ =>
      ∫ tau : ℝ, paperFT k tau * (Zeta23.mu tau : ℂ) := by
  funext k
  exact literalGammaTerm_eq_rvMMuPair k

end Synthesis
