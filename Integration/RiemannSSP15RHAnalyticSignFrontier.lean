import Synthesis.RiemannQuarticProducerRoleCertificate

/-!
# Source-native quartic target: exact signed-estimate frontier

This file uses the actual RH producer terms, rather than an SSP15 role
encoding, to state the analytic bound that the signed identity can transfer.
No positivity or bound is asserted without an independent hypothesis.

The four-term identity is exact, but does not itself supply a one-sided
estimate. The equivalences below expose precisely the additional bound
required of the other three terms to constrain the source target.
-/

namespace Integration.RiemannSSP15RHAnalyticSignFrontier

namespace RH := Synthesis.RiemannQuarticProducerRoleCertificate

def otherThree (lam mu : ℝ) : ℝ :=
  RH.weightedCoordinate .pole lam mu +
  RH.weightedCoordinate .origin lam mu +
  RH.weightedCoordinate .j lam mu

theorem actual_source_balance (lam mu : ℝ) :
    otherThree lam mu + RH.weightedCoordinate .target lam mu = 0 := by
  exact RH.primitive_kernel_via_source_roles lam mu

theorem target_lower_bound_iff_other_upper_bound
    (lam mu lower : ℝ) :
    lower ≤ RH.weightedCoordinate .target lam mu ↔
    otherThree lam mu ≤ -lower := by
  have h := actual_source_balance lam mu
  constructor <;> intro hbound <;> linarith

theorem target_strict_lower_bound_iff_other_strict_upper_bound
    (lam mu lower : ℝ) :
    lower < RH.weightedCoordinate .target lam mu ↔
    otherThree lam mu < -lower := by
  have h := actual_source_balance lam mu
  constructor <;> intro hbound <;> linarith

theorem target_nonnegative_iff_other_nonpositive
    (lam mu : ℝ) :
    0 ≤ RH.weightedCoordinate .target lam mu ↔
    otherThree lam mu ≤ 0 := by
  simpa using target_lower_bound_iff_other_upper_bound lam mu 0

theorem no_target_bound_from_identity_alone
    (targetValue : ℝ) :
    ∃ otherValue : ℝ, otherValue + targetValue = 0 := by
  exact ⟨-targetValue, by ring⟩

end Integration.RiemannSSP15RHAnalyticSignFrontier
