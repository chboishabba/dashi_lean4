import Zeta23.Final
import Zeta23.RvM.LocalCount

/-!
# Exact Zeta23 Riemann--von Mangoldt producer bridge

The upstream Zeta23 development proves the full Riemann--von Mangoldt package
for the SAME literal `zetaZeroConfig` consumed by the RH branch.

Its theorem is

  Zeta23.riemannVonMangoldt_zeta :
    RiemannVonMangoldt zetaZeroConfig

with fields

  main :
    exists C T0, forall T >= T0,
      |N(T,2T) - T/(2*pi) * ell1(T)| <= C log T

and

  local_count :
    exists A0 >= 1, forall t,
      N(t,t+1] <= A0 log(|t|+3).

This file exposes those theorem-bearing producers directly.  No replacement
hypothesis and no asymptotic-only surrogate is introduced.
-/

noncomputable section

open scoped Real

namespace Synthesis

open Zeta23

/-- Exact theorem-bearing analytic-input package for Mathlib's zeta zeros. -/
def literalZetaPaperInputs : PaperInputs zetaZeroConfig :=
  paperInputs_zeta

/-- Exact theorem-bearing Riemann--von Mangoldt package for the literal carrier. -/
def literalZetaRvM : RiemannVonMangoldt zetaZeroConfig :=
  riemannVonMangoldt_zeta

/-- The literal smooth dyadic RvM main term used by the upstream theorem. -/
def literalZetaRvMMainTerm (T : ℝ) : ℝ :=
  T / (2 * Real.pi) * ell1 T

/-- The theorem-bearing dyadic actual-minus-main discrepancy. -/
theorem literalZetaRvM_main :
    ∃ C T0 : ℝ, ∀ T : ℝ, T0 <= T ->
      |(zetaZeroConfig.N T (2 * T) : ℝ) - literalZetaRvMMainTerm T|
        <= C * Real.log T := by
  simpa [literalZetaRvMMainTerm] using literalZetaRvM.main

/-- The theorem-bearing two-sided unit-window local count on the same carrier. -/
theorem literalZetaRvM_local_count :
    ∃ A0 : ℝ, 1 <= A0 ∧ ∀ t : ℝ,
      (zetaZeroConfig.N t (t + 1) : ℝ)
        <= A0 * Real.log (|t| + 3) := by
  exact literalZetaRvM.local_count

/--
Same-object check: the older direct producer already used by the shell code is
exactly a local-count theorem on `zetaZeroConfig`; the full RvM package above
therefore strengthens the analytic information without changing carriers.
-/
def literalZetaLocalCountDirect :=
  Zeta23.RvM.zetaZeroConfig_local_count

end Synthesis
