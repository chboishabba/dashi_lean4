import Synthesis.RiemannRvMMuGammaSameObject
import Synthesis.RiemannNormalizedProjectiveOffTsumAttachment

/-!
# Projective same-object weld: RvM mu = literal Gamma on the actual consumer

The projective high cut is tested by the literal kernel

  sampleTest (projTaper g r) t 0.

The upstream Riemann--von Mangoldt producer and the literal Weil Gamma channel
are not two independent analytic objects.  Zeta23 proves for every test k that

  gammaTerm k = integral paperFT(k)(tau) * mu(tau) d tau.

Specializing that theorem to the actual projective test pays the same-object
weld before any asymptotic decomposition of mu into a constant/logarithmic
surrogate.

This is an accounting firewall: a proof may estimate the actual zero measure
relative to mu and then use the literal Gamma channel, but it must not charge an
independent smooth-RvM main contribution and the same Gamma contribution again.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilProjectiveTaper

/-- The exact projective test already consumed by the literal Off tsum. -/
def literalProjectiveSampleTest
    (g : ℝ → ℝ) (t r : ℝ) : ℝ → ℂ :=
  sampleTest (projTaper g r) t 0

/-- Pair the exact projective test against the theorem-bearing RvM density. -/
def projectiveRvMMuPair
    (g : ℝ → ℝ) (t r : ℝ) : ℂ :=
  ∫ tau : ℝ,
    paperFT (literalProjectiveSampleTest g t r) tau
      * (Zeta23.mu tau : ℂ)

/--
Exact projective specialization of the global mu/Gamma same-object theorem.
No q-grid, smooth-density approximation, or asymptotic expansion enters.
-/
theorem projectiveRvMMuPair_eq_literalGammaTerm
    (g : ℝ → ℝ) (t r : ℝ) :
    projectiveRvMMuPair g t r
      =
    gammaTerm (literalProjectiveSampleTest g t r) := by
  unfold projectiveRvMMuPair
  exact (literalGammaTerm_eq_rvMMuPair
    (literalProjectiveSampleTest g t r)).symm

/-- Signed real form matching the literal explicit-formula Gamma convention. -/
def projectiveRvMMuSignedPair
    (g : ℝ → ℝ) (t r : ℝ) : ℝ :=
  - reim (projectiveRvMMuPair g t r)

theorem projectiveRvMMuSignedPair_eq_literalGammaSignedPair
    (g : ℝ → ℝ) (t r : ℝ) :
    projectiveRvMMuSignedPair g t r
      =
    - reim (gammaTerm (literalProjectiveSampleTest g t r)) := by
  unfold projectiveRvMMuSignedPair
  rw [projectiveRvMMuPair_eq_literalGammaTerm]

/--
Consumer-level no-double-count statement: the projective smooth RvM measure
and the projective literal Gamma term are definitionally the same scalar after
the exact Zeta23 theorem is applied.
-/
theorem projectiveRvMMu_is_literalGamma
    (g : ℝ → ℝ) (t r : ℝ) :
    (∫ tau : ℝ,
      paperFT (sampleTest (projTaper g r) t 0) tau
        * (Zeta23.mu tau : ℂ))
      =
    gammaTerm (sampleTest (projTaper g r) t 0) := by
  simpa [literalProjectiveSampleTest, projectiveRvMMuPair] using
    projectiveRvMMuPair_eq_literalGammaTerm g t r

end Synthesis
