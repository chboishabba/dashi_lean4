import Integration.CertificateFormula
import Integration.GaugeSSP
import Integration.DescentLevel
import Integration.LeastSufficient

/-!
# The SSP lane's observational threshold

`Integration.DescentLevel` located the coarsest sufficient observation of the
finite axis lane exactly (level one).  The same question for the SSP nine-cell
lane is settled here, and the closed form of `Integration.CertificateFormula`
makes both answers computations rather than case analyses.

Two different transverse channels on the *same* nine cells give two different
answers, and that is the point:

* **Lane-polarity channel** (`Integration.GaugeSSP.sspBuild`, the channel used by
  the gauge weld): the three classes all have three cells, so by
  `nondegeneracy_eq_of_card_eq` the certificate is *constant*
  (`ssp_cert_constant`).  It therefore survives every coarsening
  (`ssp_factorsAt_all`) and **no threshold exists** (`ssp_no_threshold`).  The
  certificate of that channel measures nothing about resolution.
* **Zero-detecting channel** (`sspZeroBuild`, the lane-symmetry-invariant class
  "is this the zero trit?"): the classes have three and six cells, so the
  certificate takes the two distinct values `212/9` and `215/9`
  (`sspZero_cert_zero`, `sspZero_cert_nonzero`).  It is a function of the visible
  lane trit but not of the coarser two-state merge, so

  ```
      k_SSP = 1 ,
  ```

  proved as `sspZero_coarsest_sufficient` and `sspZero_threshold_is_one`.

So the answer to "does the SSP certificate need (polarity, phase), only
polarity, or an orbit statistic?" is: with the zero-detecting channel it needs
exactly the polarity layer — the wheel phase is never required — while the
polarity-indicator channel retains nothing at all.  Both statements are about
the finite nine-cell carrier; no physical claim is made.
-/

namespace Integration.SSPThreshold

open Spine
open Spine.MeanSplit
open Integration.SymmetryReduction
open Integration.StructuredObserver
open Integration.EquivariantChannel
open Integration.CertificateFormula
open Integration.DescentLevel
open Integration.DescentLevel.LayerTower
open Integration.PolarResidual
open Integration.GaugeSSP
open Integration.LeastSufficient

/-! ## The lane-polarity channel: all classes have three cells -/

/-- Every class of the lane-polarity channel has exactly three of the nine
cells. -/
theorem ssp_class_card (c : FullPhaseCell) :
    (classFinset sspBuild.cls cellEquiv c).card = 3 := by
  revert c; decide

/-- **Hence its certificate is constant**: the channel cannot distinguish any two
of the nine cells. -/
theorem ssp_cert_constant (c c' : FullPhaseCell) :
    sspGaugeObserver.nondegeneracy c = sspGaugeObserver.nondegeneracy c' :=
  nondegeneracy_eq_of_card_eq sspBuild cellEquiv (by rw [ssp_class_card, ssp_class_card])

/-- The SSP tower `9 cells → 3 lane trits → 2 merged classes`. -/
def tritMerge : KernelTrit → Bool
  | .positiveTrit => true
  | .zeroTrit => false
  | .negativeTrit => false

/-- The tower over the SSP projection. -/
def sspTower : LayerTower := twoStepTower (Prod.fst : FullPhaseCell → KernelTrit) tritMerge

/-- A constant certificate is visible at every level. -/
theorem ssp_factorsAt_all (k : ℕ) : sspTower.FactorsAt sspGaugeObserver.nondegeneracy k := by
  refine LayerTower.factorsAt_of_constant sspTower sspGaugeObserver.nondegeneracy
    (sspGaugeObserver.nondegeneracy (KernelTrit.zeroTrit, DepthWheelPhase.phase0)) ?_ k
  intro c
  exact ssp_cert_constant c (KernelTrit.zeroTrit, DepthWheelPhase.phase0)

/-- **So the gauge weld's own channel has no observational threshold on the SSP
lane.** -/
theorem ssp_no_threshold :
    ¬ ∃ k, sspTower.CoarsestSufficient sspGaugeObserver.nondegeneracy k := by
  rintro ⟨k, -, hk⟩
  exact hk (ssp_factorsAt_all (k + 1))

/-! ## The zero-detecting channel: a genuine threshold -/

/-- Observer data on the same nine cells with the lane-symmetry-**invariant**
class coordinate "is this the zero trit?".  The polarity flip fixes the zero trit
and exchanges the other two, and the wheel rotation does not touch the trit, so
this coordinate is invariant and the invariant-class constructor applies. -/
def sspZeroBuild : ObserverBuild LaneSym FullPhaseCell KernelTrit DepthWheelPhase Bool where
  reduction := sspGaugeReduction.toEquivariantQuotient
  actInv := fun g => actCell (invLane g)
  actInv_left := actCell_invLane_left
  actInv_right := actCell_invLane_right
  residual := Prod.snd
  reopen := fun t ph => (t, ph)
  reopen_project := fun _ => rfl
  cls := fun c => decide (c.1 = KernelTrit.zeroTrit)
  cls_invariant := by decide
  cls_separates := by decide

/-- The resulting symmetry-resolved observer. -/
noncomputable def sspZeroObserver :
    SymmetryResolvedObserver LaneSym FullPhaseCell KernelTrit DepthWheelPhase 9 :=
  sspZeroBuild.toObserver cellEquiv

/-- The zero class has three cells. -/
theorem sspZero_class_card_zero (ph : DepthWheelPhase) :
    (classFinset sspZeroBuild.cls cellEquiv (KernelTrit.zeroTrit, ph)).card = 3 := by
  revert ph; decide

/-- The nonzero class has six. -/
theorem sspZero_class_card_nonzero (c : FullPhaseCell) (h : c.1 ≠ KernelTrit.zeroTrit) :
    (classFinset sspZeroBuild.cls cellEquiv c).card = 6 := by
  revert c
  decide

/-- The certificate on a zero-trit cell. -/
theorem sspZero_cert_zero (ph : DepthWheelPhase) :
    sspZeroObserver.nondegeneracy (KernelTrit.zeroTrit, ph) = 212 / 9 := by
  rw [show sspZeroObserver.nondegeneracy (KernelTrit.zeroTrit, ph)
      = _ from nondegeneracy_eq' sspZeroBuild cellEquiv _, sspZero_class_card_zero ph]
  norm_num

/-- The certificate on a nonzero-trit cell: a different number, so this channel
is a genuinely nonconstant invariant. -/
theorem sspZero_cert_nonzero (c : FullPhaseCell) (h : c.1 ≠ KernelTrit.zeroTrit) :
    sspZeroObserver.nondegeneracy c = 215 / 9 := by
  rw [show sspZeroObserver.nondegeneracy c = _ from nondegeneracy_eq' sspZeroBuild cellEquiv c,
    sspZero_class_card_nonzero c h]
  norm_num

/-- The certificate is a function of the visible lane trit. -/
theorem sspZero_factorsAt_one : sspTower.FactorsAt sspZeroObserver.nondegeneracy 1 := by
  rw [LayerTower.factorsAt_iff_fibre]
  intro x y hxy
  have h1 : x.1 = y.1 := hxy
  refine nondegeneracy_eq_of_card_eq' sspZeroBuild cellEquiv ?_
  have : sspZeroBuild.cls x = sspZeroBuild.cls y := by
    show decide (x.1 = KernelTrit.zeroTrit) = decide (y.1 = KernelTrit.zeroTrit)
    rw [h1]
  simp only [classFinset, this]

/-- But not of the coarser merge, which puts the zero trit together with the
negative one. -/
theorem sspZero_not_factorsAt_two : ¬ sspTower.FactorsAt sspZeroObserver.nondegeneracy 2 := by
  rw [LayerTower.factorsAt_iff_fibre]
  intro h
  have hval := h (KernelTrit.zeroTrit, DepthWheelPhase.phase0)
    (KernelTrit.negativeTrit, DepthWheelPhase.phase0) rfl
  rw [sspZero_cert_zero, sspZero_cert_nonzero _ (by decide)] at hval
  norm_num at hval

/-- **The SSP observational threshold.**  With the zero-detecting channel the
coarsest observation of the nine-cell lane still determining the transverse
certificate is the three-state lane-polarity layer. -/
theorem sspZero_coarsest_sufficient :
    sspTower.CoarsestSufficient sspZeroObserver.nondegeneracy 1 :=
  ⟨sspZero_factorsAt_one, sspZero_not_factorsAt_two⟩

/-- And that level is unique: `k_SSP = 1`. -/
theorem sspZero_threshold_is_one {k : ℕ}
    (hk : sspTower.CoarsestSufficient sspZeroObserver.nondegeneracy k) : k = 1 :=
  LayerTower.coarsest_unique _ _ hk sspZero_coarsest_sufficient

/-- **The two channels contrasted.**  On the same nine cells and the same tower:
the polarity-indicator channel retains its certificate at every level and has no
threshold, while the zero-detecting channel has the threshold exactly at the
lane-polarity layer.  A resolution threshold is a property of the channel, not of
the carrier. -/
theorem ssp_threshold_dichotomy :
    (¬ ∃ k, sspTower.CoarsestSufficient sspGaugeObserver.nondegeneracy k) ∧
      sspTower.CoarsestSufficient sspZeroObserver.nondegeneracy 1 :=
  ⟨ssp_no_threshold, sspZero_coarsest_sufficient⟩

/-! ## The threshold layer is finer than the canonical observer -/

/-- The lane-polarity layer carries strictly more information than the
certificate: the certificate cannot tell the two nonzero polarities apart, so it
does not determine the layer. -/
theorem sspZero_not_refines_layer :
    ¬ Refines sspZeroObserver.nondegeneracy (sspTower.projTo 1) := by
  rintro ⟨f, hf⟩
  have hpos := hf (KernelTrit.positiveTrit, DepthWheelPhase.phase0)
  have hneg := hf (KernelTrit.negativeTrit, DepthWheelPhase.phase0)
  rw [sspZero_cert_nonzero _ (by decide)] at hpos
  rw [sspZero_cert_nonzero _ (by decide)] at hneg
  have : KernelTrit.positiveTrit = KernelTrit.negativeTrit := by
    rw [show KernelTrit.positiveTrit
      = sspTower.projTo 1 (KernelTrit.positiveTrit, DepthWheelPhase.phase0) from rfl,
      show KernelTrit.negativeTrit
      = sspTower.projTo 1 (KernelTrit.negativeTrit, DepthWheelPhase.phase0) from rfl,
      hpos, hneg]
  exact absurd this (by decide)

/-- **So the SSP threshold layer is the coarsest sufficient layer of this tower,
not the intrinsic least sufficient observer.**  It retains the certificate, and
is strictly more informative than it. -/
theorem sspZero_coarsest_strictly_finer :
    Refines (sspTower.projTo 1) sspZeroObserver.nondegeneracy ∧
      ¬ Equivalent (sspTower.projTo 1) sspZeroObserver.nondegeneracy :=
  coarsest_strictly_finer sspTower sspZeroObserver.nondegeneracy
    sspZero_coarsest_sufficient sspZero_not_refines_layer

end Integration.SSPThreshold
