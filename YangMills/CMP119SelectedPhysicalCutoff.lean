import Mathlib
import YangMills.CMP119SelectedCanonicalGibbsProbability
import YangMills.LiteralSU2FiniteWilson

open MeasureTheory

/-!
# Preferred selected CMP119 physical finite cutoff

The selected finite law should not carry a free real Wilson coefficient.  The
physical literal SU(2) action already fixes the positive Wilson normalization

  beta = 4 / g^2.

Agda's finite-history source fixes the running coupling and its inverse-square
coefficient.  This Lean owner therefore stores one physical bare coupling `g`
and the corresponding source inverse coefficient `u` with the exact product
law `u * g^2 = 1`.  The coefficient used by the literal action is defined to be
`su2WilsonBeta g`, and elementary field algebra proves `beta = 4*u`.

The remaining cross-language/source obligation is only that these `g` and `u`
are the SAME finite-history quantities selected by CMP119/CMP109.
-/

namespace RequestProject.YangMills

structure CMP119SelectedPhysicalCutoff
    (n : ℕ) [NeZero n] where
  source : CMP119SelectedSourceInstantiation n
  bareCoupling : ℝ
  bareCouplingNeZero : bareCoupling ≠ 0
  sourceInverseCoupling : ℝ
  sourceInverseCouplingProduct :
    sourceInverseCoupling * bareCoupling ^ 2 = 1
  weightIntegrable :
    Integrable
      (selectedCMP119CompleteWeight source (su2WilsonBeta bareCoupling))
      (((literalSU2ProductLinkHaar (2 * n) :
        ProbabilityMeasure (SU2TorusLinks (2 * n))) :
        Measure (SU2TorusLinks (2 * n))))

namespace CMP119SelectedPhysicalCutoff

/-- The physical positive Wilson coefficient used by the literal action. -/
def beta
    {n : ℕ} [NeZero n]
    (cutoff : CMP119SelectedPhysicalCutoff n) : ℝ :=
  su2WilsonBeta cutoff.bareCoupling

/-- The physical SU(2) normalization is four times the same inverse-square source coefficient. -/
theorem beta_eq_four_mul_sourceInverseCoupling
    {n : ℕ} [NeZero n]
    (cutoff : CMP119SelectedPhysicalCutoff n) :
    cutoff.beta = 4 * cutoff.sourceInverseCoupling := by
  unfold beta su2WilsonBeta
  have hs : cutoff.bareCoupling ^ 2 ≠ 0 :=
    pow_ne_zero 2 cutoff.bareCouplingNeZero
  apply (div_eq_iff hs).2
  calc
    4 = 4 * 1 := by ring
    _ = 4 * (cutoff.sourceInverseCoupling * cutoff.bareCoupling ^ 2) := by
      rw [cutoff.sourceInverseCouplingProduct]
    _ = (4 * cutoff.sourceInverseCoupling) * cutoff.bareCoupling ^ 2 := by ring

/-- Canonical selected finite probability on the same literal links and source action. -/
noncomputable def gibbsLaw
    {n : ℕ} [NeZero n]
    (cutoff : CMP119SelectedPhysicalCutoff n) :
    ProbabilityMeasure (SU2TorusLinks (2 * n)) :=
  selectedCMP119CanonicalGibbsProbability
    cutoff.source cutoff.beta cutoff.weightIntegrable

/-- The cutoff law uses the same exact selected source action with the source-normalized beta. -/
theorem gibbsLaw_expectation_is_source_ratio
    {n : ℕ} [NeZero n]
    (cutoff : CMP119SelectedPhysicalCutoff n)
    (observable : SU2TorusLinks (2 * n) → ℝ) :
    (∫ links, observable links
      ∂((cutoff.gibbsLaw : ProbabilityMeasure (SU2TorusLinks (2 * n))) :
        Measure (SU2TorusLinks (2 * n)))) =
      (∫ links,
          selectedCMP119CompleteWeight cutoff.source cutoff.beta links *
            observable links
        ∂(((literalSU2ProductLinkHaar (2 * n) :
          ProbabilityMeasure (SU2TorusLinks (2 * n))) :
          Measure (SU2TorusLinks (2 * n))))) /
      (∫ links,
          selectedCMP119CompleteWeight cutoff.source cutoff.beta links
        ∂(((literalSU2ProductLinkHaar (2 * n) :
          ProbabilityMeasure (SU2TorusLinks (2 * n))) :
          Measure (SU2TorusLinks (2 * n))))) := by
  exact selected_cmp119_canonical_expectation_is_source_gibbs_ratio
    cutoff.source cutoff.beta cutoff.weightIntegrable observable

end CMP119SelectedPhysicalCutoff

end RequestProject.YangMills
