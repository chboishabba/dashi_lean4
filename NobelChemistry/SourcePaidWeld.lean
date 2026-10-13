import Mathlib
import NobelChemistry.AsymmetricAutocatalysis
import NobelChemistry.Iteration

/-!
# Source-paid quantitative weld for Kagan–Soai chemistry

This file adds only numerical/mechanistic facts exposed by the cited source
surfaces. Sparse source points are not promoted to a unique continuous kinetic
law, and the 2003 amplification experiment is not identified with the distinct
2025 kinetic-profiling experiments.
-/

namespace NobelChemistry

/-- Sato et al. 2003: about 0.00005% ee, normalized to full-scale ee = 1. -/
def soai2003Initial : ℚ := 1 / 2000000

/-- Sato et al. 2003 terminal lower threshold: >99.5% ee. -/
def soai2003Threshold : ℚ := 199 / 200

def soai2003Cycles : Nat := 3

@[simp] theorem soai2003_initial_positive : 0 < soai2003Initial := by
  norm_num [soai2003Initial]

@[simp] theorem soai2003_extreme_amplification_order :
    soai2003Initial < soai2003Threshold := by
  norm_num [soai2003Initial, soai2003Threshold]

@[simp] theorem soai2003_threshold_below_full_scale :
    soai2003Threshold < 1 := by
  norm_num [soai2003Threshold]

@[simp] theorem soai2003_cycle_count : soai2003Cycles = 3 := rfl

/-- Source identifiers are metadata, not imported theorem authority. -/
def kagan1986DOI : String := "10.1021/ja00269a036"
def soai1995DOI : String := "10.1038/378767a0"
def soai2003DOI : String := "10.1002/anie.200390105"
def mohler2025DOI : String := "10.1038/s41467-025-62591-3"

/-- Four systems profiled by Möhler et al. 2025. -/
inductive SoaiSystem where
  | TMSPyr
  | AdPyr
  | TMSPym
  | AdPym
  deriving DecidableEq, Repr

open SoaiSystem

/-- Activation barriers in deci-kJ/mol, retaining the source's one decimal. -/
def activationBarrierDeciKJ : SoaiSystem → Nat
  | TMSPyr => 946
  | AdPyr => 955
  | TMSPym => 859
  | AdPym => 864

@[simp] theorem pyrimidine_tms_barrier_lower :
    activationBarrierDeciKJ TMSPym < activationBarrierDeciKJ TMSPyr := by decide

@[simp] theorem pyrimidine_ad_barrier_lower :
    activationBarrierDeciKJ AdPym < activationBarrierDeciKJ AdPyr := by decide

/-- Main-text reaction-network dimensions in Möhler et al. 2025. -/
def reactionODECount : Nat := 18
def sideReactionODECount : Nat := 1
def totalODECount : Nat := 19
def profilesPerIterationApprox : Nat := 24000000

@[simp] theorem ode_count_closes :
    reactionODECount + sideReactionODECount = totalODECount := by
  norm_num [reactionODECount, sideReactionODECount, totalODECount]

/-- Fast isopropylzinc-alkoxide formation, M^-1 s^-1. -/
def alkoxideFormationRate : Nat := 150

inductive RateCoordinate where
  | k2 | k3 | k4 | k5 | k6 | k7 | k8 | km2 | km3 | km4
  deriving DecidableEq, Repr

inductive RateUnit where
  | perMolarSecond
  | perSecond
  deriving DecidableEq, Repr

open RateCoordinate RateUnit

def rateUnit : RateCoordinate → RateUnit
  | k2 | k3 | k4 | k5 | k7 => perMolarSecond
  | k6 | k8 | km2 | km3 | km4 => perSecond

@[simp] theorem k4_rate_unit : rateUnit k4 = perMolarSecond := rfl
@[simp] theorem k6_rate_unit : rateUnit k6 = perSecond := rfl

/-- Source-exposed mechanistic flags, kept separate from equation bodies. -/
structure MechanisticReceipt where
  mirrorCyclesSameRates : Bool
  aldehydeSecondOrder : Bool
  k4RateDetermining : Bool
  dimersEnterAmplificationExplanation : Bool
  hemiacetalatePathwaySupported : Bool
  deriving DecidableEq, Repr

def mohler2025Receipt : MechanisticReceipt :=
  ⟨true, true, true, true, true⟩

@[simp] theorem mohler_mirror_rates : mohler2025Receipt.mirrorCyclesSameRates = true := rfl
@[simp] theorem mohler_k4_rate_determining : mohler2025Receipt.k4RateDetermining = true := rfl

/-- Exact representation-level C3 reflection law, reusing the chemistry carrier. -/
theorem mirror_phase_source_weld (x : ChiralBias) :
    phase (mirror x) = Complex.conj (phase x) :=
  phase_mirror_eq_conj x

/--
The implemented source weld deliberately preserves provenance separation:
2003 pays the extreme amplification endpoint; 2025 pays a later same-reaction-
family mechanistic/kinetic surface.  They are not represented as one experiment.
-/
structure SourceWeldBoundary where
  extremeAmplificationPaid : Bool
  kineticNetworkPaid : Bool
  activationBarrierTablePaid : Bool
  mirrorRateIdentityPaid : Bool
  rateDeterminingStepPaid : Bool
  sameHistoricalExperimentClaimed : Bool
  sparsePointsPromotedToUniqueContinuousLaw : Bool
  deriving DecidableEq, Repr

def sourceWeldBoundary : SourceWeldBoundary :=
  ⟨true, true, true, true, true, false, false⟩

end NobelChemistry
