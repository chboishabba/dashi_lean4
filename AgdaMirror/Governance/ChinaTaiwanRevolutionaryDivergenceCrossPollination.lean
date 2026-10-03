import AgdaMirror.Governance.ComparativeMarxianRevolutionaryTranslationFamily
import AgdaMirror.Governance.ChinaTaiwanHistoricalSuccessionIdentity
import AgdaMirror.Governance.ChinaTaiwanUSPolicyPluralAuthority2026

namespace AgdaMirror.Governance.ChinaTaiwanRevolutionaryDivergenceCrossPollination

open AgdaMirror.Governance.ComparativeMarxianRevolutionaryTranslationFamily
open AgdaMirror.Governance.ChinaTaiwanHistoricalSuccessionIdentity
open AgdaMirror.Governance.ChinaTaiwanUSPolicyPluralAuthority2026

structure CrossStraitDivergence where
  chinaRevolutionaryProfile : RevolutionaryTranslationProfile
  rocRetreatTransition : HistoricalTransition
  taiwanDemocratisationTransition : HistoricalTransition
  currentUSExecutivePosition : PolicyPosition
  currentCongressionalPressure : PolicyPosition
  sharedCivilWarHistory : Bool := true
  samePresentPoliticalSystem : Bool := false
  sharedHistoryDeterminesPresentIdentity : Bool := false
  semiconductorPowerSettlesSovereignty : Bool := false
  usPolicySettlesHistoricalLegitimacy : Bool := false

def canonical : CrossStraitDivergence :=
  ⟨chinaProfile, rocCivilWarRetreat, rocAuthoritarianToDemocraticTaiwan,
   trumpAdministrationUnchangedPolicy, wickerSecurityPressure⟩

theorem canonical_divergence_is_noncollapsing :
    canonical.sharedCivilWarHistory = true ∧
    canonical.samePresentPoliticalSystem = false ∧
    canonical.sharedHistoryDeterminesPresentIdentity = false ∧
    canonical.semiconductorPowerSettlesSovereignty = false ∧
    canonical.usPolicySettlesHistoricalLegitimacy = false := by
  decide

end AgdaMirror.Governance.ChinaTaiwanRevolutionaryDivergenceCrossPollination
