/-!
# RH route supersession ledger

This file is deliberately archival rather than destructive.

The current four-window signed-pole route has a smaller Clay-facing min-cut,
but earlier pole-quotient, near/far, Gamma, Schur and zero-mode routes remain
valuable as proved machinery, diagnostics, donors and alternative proof-search
surfaces.  They are therefore marked `supersededDonor`, not deleted and not
declared false.

"Superseded" means only:

* not primitive on the current preferred Clay-facing dependency cut;
* retained for provenance and possible reuse;
* may still supply estimates or representation lemmas to the preferred route.
-/

namespace Synthesis

inductive RHQuarticRoute
  | currentSignedCompletedResidual
  | separateGammaEstimate
  | separatePolePayment
  | nearFarPoleQuotient
  | actualGridZeroModeTransport
  | independentSmoothMainLog
  | schurNuisanceSelection
  deriving DecidableEq, Repr

inductive RHRouteStatus
  | authoritativeMinCut
  | supersededDonor
  deriving DecidableEq, Repr

def rhQuarticRouteStatus : RHQuarticRoute -> RHRouteStatus
  | .currentSignedCompletedResidual => .authoritativeMinCut
  | .separateGammaEstimate => .supersededDonor
  | .separatePolePayment => .supersededDonor
  | .nearFarPoleQuotient => .supersededDonor
  | .actualGridZeroModeTransport => .supersededDonor
  | .independentSmoothMainLog => .supersededDonor
  | .schurNuisanceSelection => .supersededDonor

theorem currentSignedCompletedResidual_is_authoritative :
    rhQuarticRouteStatus .currentSignedCompletedResidual
      = .authoritativeMinCut := rfl

theorem separateGammaEstimate_is_retained_superseded :
    rhQuarticRouteStatus .separateGammaEstimate
      = .supersededDonor := rfl

theorem separatePolePayment_is_retained_superseded :
    rhQuarticRouteStatus .separatePolePayment
      = .supersededDonor := rfl

theorem nearFarPoleQuotient_is_retained_superseded :
    rhQuarticRouteStatus .nearFarPoleQuotient
      = .supersededDonor := rfl

theorem actualGridZeroModeTransport_is_retained_superseded :
    rhQuarticRouteStatus .actualGridZeroModeTransport
      = .supersededDonor := rfl

theorem independentSmoothMainLog_is_retained_superseded :
    rhQuarticRouteStatus .independentSmoothMainLog
      = .supersededDonor := rfl

theorem schurNuisanceSelection_is_retained_superseded :
    rhQuarticRouteStatus .schurNuisanceSelection
      = .supersededDonor := rfl

end Synthesis
