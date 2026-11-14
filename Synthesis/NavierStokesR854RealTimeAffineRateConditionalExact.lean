import Mathlib

/-!
# R854 selected rational initial rate: real-time negativity from a TRUE
# same-object Galerkin Lipschitz estimate.

Source Agda owners:
  NSTriadKNR650Rational345SnapshotNormalizationRound829Exact,
  NSTriadKNR650CanonicalSelectedRateNormalFormRound853Exact,
  NSTriadKNR650Rational345LipschitzIntegralRound854Exact.
  PR chboishabba/dashi_agda #1501, head 98b6b63...

The R854 arithmetic is exact. This Lean proof gives a real-time pointwise
consumer for an ACTUAL rate envelope, without pretending to construct the
missing real Galerkin trajectory, its source rate, the real integral or a
Navier--Stokes Clay global-regularity theorem.

Attribution: Picard--Lindelof/mean-value bound is classical; finite selected
R829/R854 rational data are original DASHI source computations.
-/

noncomputable section
namespace Synthesis

def nsR854InitialRate : ℝ := -(28273644 : ℝ) / 125

def nsR854Lipschitz : ℝ := 391309593930357307785216

def nsR854Horizon : ℝ :=
  (226189 : ℝ) / 3938540454339300631433585885184

theorem nsR854Lipschitz_nonneg : 0 ≤ nsR854Lipschitz := by
  norm_num [nsR854Lipschitz]

theorem nsR854Horizon_pos : 0 < nsR854Horizon := by
  norm_num [nsR854Horizon]

theorem nsR854AffineFinalRate_neg :
    nsR854InitialRate + nsR854Lipschitz * nsR854Horizon < 0 := by
  norm_num [nsR854InitialRate, nsR854Lipschitz, nsR854Horizon]

/-- Applies to real time on the ORIGINAL selected R854 horizon. It is
a true theorem under a true rate upper bound, not a construction of that
upper bound for the original physical Galerkin flow. -/
theorem nsR854RateNegativeFromRealEnvelope
    (rate : ℝ → ℝ)
    (hSourceRate :
      ∀ t ∈ Set.Icc (0 : ℝ) nsR854Horizon,
        rate t ≤ nsR854InitialRate + nsR854Lipschitz * t) :
    ∀ t ∈ Set.Icc (0 : ℝ) nsR854Horizon, rate t < 0 := by
  intro t ht
  have htT : t ≤ nsR854Horizon := ht.2
  have hL := mul_le_mul_of_nonneg_left htT nsR854Lipschitz_nonneg
  have hr := hSourceRate t ht
  have hend := nsR854AffineFinalRate_neg
  linarith

/-- In particular the rate is strictly negative at the actual R854
terminal time. The essential R853 physical source envelope is explicit. -/
theorem nsR854TerminalRateNegative
    (rate : ℝ → ℝ)
    (hSourceRate :
      ∀ t ∈ Set.Icc (0 : ℝ) nsR854Horizon,
        rate t ≤ nsR854InitialRate + nsR854Lipschitz * t) :
    rate nsR854Horizon < 0 := by
  exact nsR854RateNegativeFromRealEnvelope rate hSourceRate
    nsR854Horizon
    ⟨le_of_lt nsR854Horizon_pos, le_refl _⟩

end Synthesis
