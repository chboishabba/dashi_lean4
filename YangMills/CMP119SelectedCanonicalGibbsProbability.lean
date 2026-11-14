import Mathlib
import YangMills.CMP119SelectedNativeGibbsProbability
import YangMills.LiteralSU2ProductHaar

open MeasureTheory

/-!
# Canonical selected CMP119 Gibbs law

The preferred physical finite law uses the canonical independent literal SU(2)
product Haar constructed on the same four-dimensional link carrier.  Therefore
the selected CMP119 Gibbs probability no longer carries an arbitrary reference
probability parameter.  The only remaining Haar obligation is source
provenance: the published CMP119 product-Haar convention must be identified
with `literalSU2ProductLinkHaar`.
-/

namespace RequestProject.YangMills

/--
The preferred selected finite Gibbs law: exact selected CMP119 complete action,
normalized against canonical finite product Haar on the same literal links.
-/
noncomputable def selectedCMP119CanonicalGibbsProbability
    {n : ℕ} [NeZero n]
    (source : CMP119SelectedSourceInstantiation n)
    (β : ℝ)
    (hWeightIntegrable :
      Integrable (selectedCMP119CompleteWeight source β)
        (((literalSU2ProductLinkHaar (2 * n) :
          ProbabilityMeasure (SU2TorusLinks (2 * n))) :
          Measure (SU2TorusLinks (2 * n))))) :
    ProbabilityMeasure (SU2TorusLinks (2 * n)) :=
  selectedCMP119NativeGibbsProbability source
    (literalSU2ProductLinkHaar (2 * n)) β hWeightIntegrable

/--
Expectation under the canonical selected law is the exact selected-source Gibbs
ratio over canonical product Haar.  No second normalization or measure object
is introduced.
-/
theorem selected_cmp119_canonical_expectation_is_source_gibbs_ratio
    {n : ℕ} [NeZero n]
    (source : CMP119SelectedSourceInstantiation n)
    (β : ℝ)
    (hWeightIntegrable :
      Integrable (selectedCMP119CompleteWeight source β)
        (((literalSU2ProductLinkHaar (2 * n) :
          ProbabilityMeasure (SU2TorusLinks (2 * n))) :
          Measure (SU2TorusLinks (2 * n)))))
    (observable : SU2TorusLinks (2 * n) → ℝ) :
    (∫ links, observable links
      ∂((selectedCMP119CanonicalGibbsProbability
          source β hWeightIntegrable :
        ProbabilityMeasure (SU2TorusLinks (2 * n))) :
        Measure (SU2TorusLinks (2 * n)))) =
      (∫ links,
          selectedCMP119CompleteWeight source β links * observable links
        ∂(((literalSU2ProductLinkHaar (2 * n) :
          ProbabilityMeasure (SU2TorusLinks (2 * n))) :
          Measure (SU2TorusLinks (2 * n))))) /
      (∫ links,
          selectedCMP119CompleteWeight source β links
        ∂(((literalSU2ProductLinkHaar (2 * n) :
          ProbabilityMeasure (SU2TorusLinks (2 * n))) :
          Measure (SU2TorusLinks (2 * n))))) := by
  exact selected_cmp119_native_expectation_is_source_gibbs_ratio
    source (literalSU2ProductLinkHaar (2 * n)) β
    hWeightIntegrable observable

end RequestProject.YangMills
