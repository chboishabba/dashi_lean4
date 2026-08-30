import Integration.GaugeObserver
import Integration.GaugeSU2

/-!
# The SSP nine-cell lane as a gauge reduction

`Integration.StructuredObserver.wheelReduction` quotients the nine SSP phase
cells by the *whole* depth-wheel `C₃`, so its induced coarse action is trivial —
inevitably so
(`Integration.Gauge.GaugeReduction.coarse_action_trivial_of_orbit`).  This file
keeps the same projection `9 → 3` but enlarges the acting symmetry to

```
        G = C₃ × C₂          (depth-wheel rotation × lane-polarity flip)
        H = C₃               (the wheel phase: redundant for the visible lane)
        Q = G/H ≅ C₂         (the polarity flip: effective, survives)
   FullPhaseCell (9)  ──/H──▶  KernelTrit (3),   C₂ acting by negation
```

so that the reduction becomes a genuine gauge reduction: the wheel phase is the
redundancy, the polarity flip is the surviving symmetry, and the retained
residual is the phase itself, which reopens the cell exactly.

What is checked:

* `sspGaugeReduction`, `sspDatum_exact` — the gauge datum, with `C₂` literally
  `G/H`;
* `ssp_effective`, `ssp_not_orbit_quotient` — the surviving symmetry moves the
  visible lane, so this is not an orbit quotient;
* `ssp_redundant_iff_gauge` — the invisible symmetries are exactly the wheel
  rotations;
* `sspGaugeObserver`, `ssp_gauge_theorem`, `ssp_welded` — the lane as a
  symmetry-resolved observer with a strictly positive, symmetry-invariant
  transverse certificate;
* `wheel_vs_gauge` — the contrast made precise: same projection, same nine
  cells; under the wheel alone the induced action must be trivial, under the
  enlarged symmetry it is not.

As elsewhere, these are finite carriers of at most nine elements; no analytic or
physical claim is made.
-/

namespace Integration.GaugeSSP

open Spine
open Integration.SymmetryReduction
open Integration.StructuredObserver
open Integration.EquivariantChannel
open Integration.Gauge
open Integration.Gauge.GaugeReduction
open Integration.GaugeObserver
open Integration.GaugeSU2 (Sheet)
open Integration.PhaseQuotient (Phase3)
open Integration.PolarResidual

/-- The full symmetry of the lane: a wheel rotation together with a polarity
flip. -/
abbrev LaneSym := Phase3 × Sheet

/-- The polarity flip acting on a cell. -/
def sheetOnCell : Sheet → FullPhaseCell → FullPhaseCell
  | .keep, c => c
  | .flip, c => actFull .inverse c

/-- The polarity flip acting on the visible lane trit. -/
def sheetOnTrit : Sheet → KernelTrit → KernelTrit
  | .keep, t => t
  | .flip, t => actKernel .inverse t

/-- The action of `C₃ × C₂` on the nine cells. -/
def actCell : LaneSym → FullPhaseCell → FullPhaseCell :=
  fun g c => actWheel g.1 (sheetOnCell g.2 c)

/-- The pointwise inverse action. -/
def invLane : LaneSym → LaneSym := fun g => (invPhase g.1, g.2)

theorem actCell_one (c : FullPhaseCell) : actCell 1 c = c := by
  obtain ⟨t, ph⟩ := c; rfl

theorem actCell_mul (g h : LaneSym) (c : FullPhaseCell) :
    actCell (g * h) c = actCell g (actCell h c) := by
  revert g h c; decide

theorem actCell_invLane_left (g : LaneSym) (c : FullPhaseCell) :
    actCell (invLane g) (actCell g c) = c := by
  revert g c; decide

theorem actCell_invLane_right (g : LaneSym) (c : FullPhaseCell) :
    actCell g (actCell (invLane g) c) = c := by
  revert g c; decide

theorem sheetOnTrit_one (t : KernelTrit) : sheetOnTrit 1 t = t := rfl

theorem sheetOnTrit_mul (s s' : Sheet) (t : KernelTrit) :
    sheetOnTrit (s * s') t = sheetOnTrit s (sheetOnTrit s' t) := by
  revert s s' t; decide

/-! ## The gauge datum `C₃ → C₃ × C₂ ↠ C₂` -/

/-- The depth-wheel subgroup inside the lane symmetry, and the projection onto
the surviving polarity flip. -/
def sspDatum : GaugeQuotient LaneSym Phase3 Sheet where
  incl := fun p => (p, 1)
  incl_one := rfl
  incl_mul := fun _ _ => rfl
  quot := Prod.snd
  quot_one := rfl
  quot_mul := fun _ _ => rfl
  quot_surjective := fun s => ⟨(1, s), rfl⟩
  quot_incl := fun _ => rfl

/-- The datum is exact: the kernel of `C₃ × C₂ ↠ C₂` is exactly the wheel
subgroup. -/
theorem sspDatum_exact : sspDatum.Exact := by
  rintro ⟨p, s⟩ h
  exact ⟨p, by simpa [sspDatum] using congrArg (fun s => (p, s)) h⟩

/-! ## The reduction -/

/-- **The SSP lane as a gauge reduction.**  The nine cells are reduced to the
three lane polarities by quotienting the redundant depth-wheel phase; the
polarity flip survives and acts on the visible lane. -/
def sspGaugeReduction : GaugeReduction LaneSym Phase3 Sheet FullPhaseCell KernelTrit where
  gq := sspDatum
  actRich := actCell
  rich_one := actCell_one
  rich_mul := actCell_mul
  actCoarse := sheetOnTrit
  coarse_one := sheetOnTrit_one
  coarse_mul := sheetOnTrit_mul
  red := Prod.fst
  red_surjective := fun t => ⟨(t, .phase0), rfl⟩
  square := by decide

/-- The wheel phase is invisible to the lane. -/
theorem ssp_gauge_invariant (p : Phase3) (c : FullPhaseCell) :
    sspGaugeReduction.red (sspGaugeReduction.actRich (sspDatum.incl p) c)
      = sspGaugeReduction.red c :=
  sspGaugeReduction.gauge_invariant p c

/-- The surviving polarity flip is nontrivial on the visible lane. -/
theorem ssp_effective : sspGaugeReduction.Effective :=
  ⟨.flip, .negativeTrit, by decide⟩

/-- Hence the reduction is not an orbit quotient of the full lane symmetry. -/
theorem ssp_not_orbit_quotient :
    ∃ g c, sspGaugeReduction.red (sspGaugeReduction.actRich g c) ≠ sspGaugeReduction.red c :=
  sspGaugeReduction.effective_not_orbit_quotient ssp_effective

/-- The surviving action is faithful. -/
theorem ssp_coarse_faithful : sspGaugeReduction.CoarseFaithful := by
  intro q hq
  have h := hq .negativeTrit
  revert h
  cases q <;> decide

/-- **The redundancy is exactly the depth wheel.**  A lane symmetry is invisible
to the three-state visible layer if and only if it is a pure wheel rotation. -/
theorem ssp_redundant_iff_gauge (g : LaneSym) :
    (∀ c, sspGaugeReduction.red (sspGaugeReduction.actRich g c) = sspGaugeReduction.red c)
      ↔ ∃ p, g = sspDatum.incl p :=
  sspGaugeReduction.redundant_iff_gauge sspDatum_exact ssp_coarse_faithful g

/-- **The contrast, made precise.**  The same projection `9 → 3` carries a
trivial induced action when the acting group is the whole depth wheel — that is
forced, since the projection is then an orbit map — and a nontrivial one when the
wheel is only the gauge subgroup of the larger lane symmetry. -/
theorem wheel_vs_gauge :
    (∀ (g : Phase3) (t : KernelTrit), wheelReduction.actCoarse g t = t) ∧
      (∃ (g : Sheet) (t : KernelTrit), sspGaugeReduction.actCoarse g t ≠ t) ∧
      (∀ c, wheelReduction.proj c = sspGaugeReduction.red c) :=
  ⟨fun g t =>
      GaugeReduction.coarse_action_trivial_of_orbit wheelReduction
        (fun g c => wheelReduction.square g c) g t,
    ⟨.flip, .negativeTrit, by decide⟩, fun _ => rfl⟩

/-! ## The lane as a symmetry-resolved observer -/

/-- Observer data: the class coordinate is the visible lane trit, which the
surviving polarity flip *moves*, so the equivariant-channel constructor is
required. -/
def sspBuild : EqObserverBuild LaneSym FullPhaseCell KernelTrit DepthWheelPhase KernelTrit where
  reduction := sspGaugeReduction.toEquivariantQuotient
  actInv := fun g => actCell (invLane g)
  actInv_left := actCell_invLane_left
  actInv_right := actCell_invLane_right
  residual := Prod.snd
  reopen := fun t ph => (t, ph)
  reopen_project := fun _ => rfl
  cls := Prod.fst
  actK := fun g => sheetOnTrit g.2
  actKInv := fun g => sheetOnTrit g.2
  actKInv_left := by decide
  actKInv_right := by decide
  cls_equivariant := by decide
  cls_separates := by decide

/-- **The gauge-reduced SSP lane as a symmetry-resolved observer.** -/
noncomputable def sspGaugeObserver :
    SymmetryResolvedObserver LaneSym FullPhaseCell KernelTrit DepthWheelPhase 9 :=
  sspBuild.toObserver cellEquiv

/-- **The welded statement on the SSP lane.**  Gauge directions invisible,
surviving symmetry effective, exact reopening from (lane polarity, wheel phase),
and a strictly positive, symmetry-invariant transverse certificate. -/
theorem ssp_gauge_theorem :
    (∀ (p : Phase3) (c : FullPhaseCell),
        sspGaugeObserver.reduction.proj
            (sspGaugeObserver.reduction.actRich (sspDatum.incl p) c)
          = sspGaugeObserver.reduction.proj c) ∧
      (∃ g t, sspGaugeObserver.reduction.actCoarse g t ≠ t) ∧
      (∀ c, sspGaugeObserver.reopen (sspGaugeObserver.reduction.proj c)
        (sspGaugeObserver.residual c) = c) ∧
      Function.Injective
        (fun c => (sspGaugeObserver.reduction.proj c, sspGaugeObserver.residual c)) ∧
      (∀ c, 0 < sspGaugeObserver.nondegeneracy c) ∧
      (∀ g c, sspGaugeObserver.nondegeneracy (sspGaugeObserver.reduction.actRich g c)
        = sspGaugeObserver.nondegeneracy c) :=
  ⟨ssp_gauge_invariant, ⟨(1, .flip), .negativeTrit, by decide⟩,
    sspGaugeObserver.fine_recovery, sspGaugeObserver.coarse_residual_injective,
    sspGaugeObserver.nondegeneracy_pos, sspGaugeObserver.nondegeneracy_invariant⟩

/-- The generic gauge weld, instantiated on the SSP lane. -/
theorem ssp_welded :
    (sspGaugeObserver.reduction.proj = sspGaugeReduction.red) ∧
      (∀ (p : Phase3) (c : FullPhaseCell),
        sspGaugeReduction.red (sspGaugeReduction.actRich (sspDatum.incl p) c)
          = sspGaugeReduction.red c) ∧
      (∃ q t, sspGaugeReduction.actCoarse q t ≠ t) ∧
      (∀ c, sspGaugeObserver.reopen (sspGaugeObserver.reduction.proj c)
        (sspGaugeObserver.residual c) = c) ∧
      (∀ c, 0 < sspGaugeObserver.nondegeneracy c) ∧
      (∀ g c, sspGaugeObserver.nondegeneracy (sspBuild.reduction.actRich g c)
        = sspGaugeObserver.nondegeneracy c) :=
  gauge_welded_theorem sspGaugeReduction sspBuild cellEquiv rfl ssp_effective

/-- The residual is forced: three visible polarities cannot carry nine cells. -/
theorem ssp_residual_nontrivial : 2 ≤ Fintype.card DepthWheelPhase :=
  SymmetryResolvedObserver.residual_nontrivial sspGaugeObserver (by decide)

end Integration.GaugeSSP
