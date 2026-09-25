import NSBControl.SelectedSelfResolvedRecombination

namespace NSBControl
namespace CombinedSpacetimePayment

section

variable {Time : Type*}
variable (integrateTo : (Time → ℝ) → Time → ℝ)

def integrated
    (value : Time → ℝ)
    (terminal : Time) : ℝ :=
  integrateTo value terminal

theorem integrated_congr
    (integrationCongruent :
      ∀ (f g : Time → ℝ),
        (∀ t, f t = g t) →
        ∀ terminal, integrateTo f terminal = integrateTo g terminal)
    (combined nested : Time → ℝ)
    (hPointwise : ∀ t, combined t = nested t)
    (terminal : Time) :
    integrated integrateTo combined terminal =
      integrated integrateTo nested terminal := by
  exact integrationCongruent combined nested hPointwise terminal

theorem integrated_combined_is_twelve_commutator
    (integrationCongruent :
      ∀ (f g : Time → ℝ),
        (∀ t, f t = g t) →
        ∀ terminal, integrateTo f terminal = integrateTo g terminal)
    (combined nested : Time → ℝ)
    (globalIntegratedCommutator : Time → ℝ)
    (hPointwise : ∀ t, combined t = nested t)
    (hNested :
      ∀ terminal,
        integrated integrateTo nested terminal =
          12 * globalIntegratedCommutator terminal)
    (terminal : Time) :
    integrated integrateTo combined terminal =
      12 * globalIntegratedCommutator terminal := by
  calc
    integrated integrateTo combined terminal
        = integrated integrateTo nested terminal :=
      integrated_congr integrateTo integrationCongruent
        combined nested hPointwise terminal
    _ = 12 * globalIntegratedCommutator terminal := hNested terminal

theorem combined_payment_builds_commutator_payment
    (combinedIntegrated globalIntegratedCommutator bound : ℝ)
    (hIdentity :
      combinedIntegrated = 12 * globalIntegratedCommutator)
    (hPayment :
      combinedIntegrated ≤ 12 * bound) :
    globalIntegratedCommutator ≤ bound := by
  rw [hIdentity] at hPayment
  linarith

end

end CombinedSpacetimePayment
end NSBControl
