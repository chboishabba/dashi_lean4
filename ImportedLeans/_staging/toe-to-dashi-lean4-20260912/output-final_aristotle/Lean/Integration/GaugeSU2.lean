import Integration.GaugeReduction
import Integration.EquivariantChannel
import Integration.GaugeObserver
import Integration.PhysicsInstances

/-!
# The finite axis-lift lane as a gauge reduction with surviving symmetry

`Integration.PhysicsInstances.axisLiftObserver` presents the corpus's finite
`SU(2)`-flavoured chart — three axes × two lift polarities — as an **orbit**
quotient by the central flip: the induced action on the three axes is trivial,
which (`Integration.Gauge.GaugeReduction.coarse_action_trivial_of_orbit`) is
inevitable for a quotient by the whole acting group.

This file enlarges the acting symmetry so that the reduction becomes a genuine
gauge reduction in the sense of `Integration.Gauge`:

```
        G = C₂ × C₃            (sheet flip × axis rotation)
        H = C₂                 (the deck transformation: redundant)
        Q = G/H ≅ C₃           (axis rotation: effective, survives)
   AxisLift (6)  ──/H──▶  SU2Axis (3),      C₃ acting nontrivially downstairs
```

which is the finite shadow of the pattern `SU(2)/{±1} ≅ SO(3)`: a central
redundancy is quotiented away while a nontrivial symmetry remains.  No claim is
made that these finite carriers *are* `SU(2)` or `SO(3)`; what is proved is that
they instantiate the same quotient pattern, and only that.

What is checked here:

* `su2GaugeReduction` — the gauge reduction itself, with `gaugeDatum_exact`
  proving that the kernel of `G ↠ C₃` is exactly the sheet subgroup, so `C₃` is
  literally `G/H`.
* `su2_effective`, `su2_not_orbit_quotient` — the surviving symmetry moves the
  reduced carrier, hence this reduction is provably *not* an orbit quotient.
* `su2_redundant_iff_gauge` — the symmetries invisible to the reduced layer are
  exactly the gauge subgroup: nothing beyond the redundancy is thrown away.
* `sheet_is_deck_transformation` — the gauge generator acts as the central flip
  of the already-checked `axisLiftDoubleCover`.
* `su2GaugeObserver` — the same lane as a **symmetry-resolved observer**, built
  through `EquivariantChannel` because the surviving `C₃` moves every class, so
  no nonconstant invariant channel exists.
* `su2_gauge_theorem` — the four conclusions in one statement: gauge directions
  invisible, effective symmetry nontrivial downstairs, exact reopening from
  (axis, polarity), and a strictly positive, symmetry-invariant transverse
  certificate.
-/

namespace Integration.GaugeSU2

open Spine
open Integration.SymmetryReduction
open Integration.StructuredObserver
open Integration.EquivariantChannel
open Integration.Gauge
open Integration.Gauge.GaugeReduction
open Integration.GaugeObserver
open Integration.PhaseQuotient (Phase3)
open Integration.Physics369

/-! ## The symmetry group `C₂ × C₃` -/

/-- The deck group of the two-sheeted cover: the redundant `±1`. -/
inductive Sheet | keep | flip
  deriving DecidableEq, Repr, Fintype

/-- Composition of sheet elements. -/
def sheetMul : Sheet → Sheet → Sheet
  | .keep, s => s
  | .flip, .keep => .flip
  | .flip, .flip => .keep

instance : Monoid Sheet where
  mul := sheetMul
  one := .keep
  mul_assoc a b c := by revert a b c; decide
  one_mul _ := rfl
  mul_one a := by cases a <;> rfl

/-- The full symmetry: a sheet flip together with an axis rotation. -/
abbrev CoverSym := Sheet × Phase3

/-! ## The action on the six cover points -/

/-- The rotation of the axis triple by an element of `C₃`. -/
def rotAxis : Phase3 → SU2Axis → SU2Axis
  | .p0, a => a
  | .p1, .axisLow => .axisMid
  | .p1, .axisMid => .axisHigh
  | .p1, .axisHigh => .axisLow
  | .p2, .axisLow => .axisHigh
  | .p2, .axisMid => .axisLow
  | .p2, .axisHigh => .axisMid

/-- The inverse rotation. -/
def rotAxisInv : Phase3 → SU2Axis → SU2Axis
  | .p0, a => a
  | .p1, a => rotAxis .p2 a
  | .p2, a => rotAxis .p1 a

/-- The action of `C₂ × C₃` on the cover: rotate the axis, flip the sheet. -/
def actCover : CoverSym → AxisLift → AxisLift
  | (.keep, r), (a, p) => (rotAxis r a, p)
  | (.flip, r), (a, p) => (rotAxis r a, flipPolarity p)

/-- The pointwise inverse of the action. -/
def invCover : CoverSym → CoverSym
  | (s, .p0) => (s, .p0)
  | (s, .p1) => (s, .p2)
  | (s, .p2) => (s, .p1)

theorem actCover_one (x : AxisLift) : actCover 1 x = x := by
  obtain ⟨a, p⟩ := x; cases a <;> cases p <;> rfl

theorem actCover_mul (g h : CoverSym) (x : AxisLift) :
    actCover (g * h) x = actCover g (actCover h x) := by
  revert g h x; decide

theorem actCover_invCover_left (g : CoverSym) (x : AxisLift) :
    actCover (invCover g) (actCover g x) = x := by
  revert g x; decide

theorem actCover_invCover_right (g : CoverSym) (x : AxisLift) :
    actCover g (actCover (invCover g) x) = x := by
  revert g x; decide

theorem rotAxis_one (a : SU2Axis) : rotAxis 1 a = a := rfl

theorem rotAxis_mul (r s : Phase3) (a : SU2Axis) :
    rotAxis (r * s) a = rotAxis r (rotAxis s a) := by
  revert r s a; decide

/-! ## The gauge datum `C₂ → C₂ × C₃ ↠ C₃` -/

/-- The sheet subgroup inside the full symmetry, and the projection onto the
effective rotation symmetry. -/
def gaugeDatum : GaugeQuotient CoverSym Sheet Phase3 where
  incl := fun s => (s, 1)
  incl_one := rfl
  incl_mul := fun _ _ => rfl
  quot := Prod.snd
  quot_one := rfl
  quot_mul := fun _ _ => rfl
  quot_surjective := fun r => ⟨(.keep, r), rfl⟩
  quot_incl := fun _ => rfl

/-- **The datum is exact**: the kernel of `C₂ × C₃ ↠ C₃` is exactly the sheet
subgroup, so the effective symmetry is `G/H` and not a further quotient. -/
theorem gaugeDatum_exact : gaugeDatum.Exact := by
  rintro ⟨s, r⟩ h
  exact ⟨s, by simpa [gaugeDatum] using congrArg (fun r => (s, r)) h⟩

/-! ## The reduction -/

/-- **The finite `SU(2)/{±1}` pattern.**  The six cover points are reduced to the
three axes by quotienting the redundant sheet flip; the rotation symmetry
survives and acts on the axes. -/
def su2GaugeReduction : GaugeReduction CoverSym Sheet Phase3 AxisLift SU2Axis where
  gq := gaugeDatum
  actRich := actCover
  rich_one := actCover_one
  rich_mul := actCover_mul
  actCoarse := rotAxis
  coarse_one := rotAxis_one
  coarse_mul := rotAxis_mul
  red := Prod.fst
  red_surjective := fun a => ⟨(a, .pos), rfl⟩
  square := by decide

/-- **The gauge directions are invisible.** -/
theorem su2_gauge_invariant (s : Sheet) (x : AxisLift) :
    su2GaugeReduction.red (su2GaugeReduction.actRich (gaugeDatum.incl s) x)
      = su2GaugeReduction.red x :=
  su2GaugeReduction.gauge_invariant s x

/-- **The surviving symmetry is nontrivial downstairs.** -/
theorem su2_effective : su2GaugeReduction.Effective :=
  ⟨.p1, .axisLow, by decide⟩

/-- Hence the reduction is provably not an orbit quotient of the full symmetry:
some symmetry moves the reduced state. -/
theorem su2_not_orbit_quotient :
    ∃ g x, su2GaugeReduction.red (su2GaugeReduction.actRich g x) ≠ su2GaugeReduction.red x :=
  su2GaugeReduction.effective_not_orbit_quotient su2_effective

/-- The effective action is faithful: a rotation fixing every axis is trivial. -/
theorem su2_coarse_faithful : su2GaugeReduction.CoarseFaithful := by
  intro q hq
  have h := hq .axisLow
  revert h
  cases q <;> decide

/-- **The redundancy is exactly the gauge subgroup.**  A symmetry is invisible to
the three-axis layer if and only if it is a pure sheet flip; the reduction
removes the deck redundancy and nothing more. -/
theorem su2_redundant_iff_gauge (g : CoverSym) :
    (∀ x, su2GaugeReduction.red (su2GaugeReduction.actRich g x) = su2GaugeReduction.red x)
      ↔ ∃ s, g = gaugeDatum.incl s :=
  su2GaugeReduction.redundant_iff_gauge gaugeDatum_exact su2_coarse_faithful g

/-- The gauge generator acts as the central flip of the already-checked
two-sheeted cover, so the subgroup quotiented away here is the deck group. -/
theorem sheet_is_deck_transformation (x : AxisLift) :
    actCover (gaugeDatum.incl .flip) x = axisLiftDoubleCover.centralFlip x := by
  revert x; decide

/-! ## The lane as a symmetry-resolved observer -/

/-- Observer data.  The class coordinate is the axis, which the surviving `C₃`
*moves*; this is why the equivariant-channel constructor is needed. -/
def su2Build : EqObserverBuild CoverSym AxisLift SU2Axis LiftPolarity SU2Axis where
  reduction := su2GaugeReduction.toEquivariantQuotient
  actInv := fun g => actCover (invCover g)
  actInv_left := actCover_invCover_left
  actInv_right := actCover_invCover_right
  residual := Prod.snd
  reopen := fun a p => (a, p)
  reopen_project := fun _ => rfl
  cls := Prod.fst
  actK := fun g => rotAxis g.2
  actKInv := fun g => rotAxisInv g.2
  actKInv_left := by decide
  actKInv_right := by decide
  cls_equivariant := by decide
  cls_separates := by decide

/-- **The gauge-reduced axis-lift lane as a symmetry-resolved observer.** -/
noncomputable def su2GaugeObserver :
    SymmetryResolvedObserver CoverSym AxisLift SU2Axis LiftPolarity 6 :=
  su2Build.toObserver axisEnum

/-- **The welded statement on a physics-facing lane.**  Gauge directions are
invisible; the effective symmetry acts nontrivially on the reduced carrier; the
rich state is exactly recoverable from reduced state plus retained residual; and
the transverse certificate is strictly positive and constant along the whole
symmetry. -/
theorem su2_gauge_theorem :
    (∀ (s : Sheet) (x : AxisLift),
        su2GaugeObserver.reduction.proj (su2GaugeObserver.reduction.actRich (gaugeDatum.incl s) x)
          = su2GaugeObserver.reduction.proj x) ∧
      (∃ g y, su2GaugeObserver.reduction.actCoarse g y ≠ y) ∧
      (∀ x, su2GaugeObserver.reopen (su2GaugeObserver.reduction.proj x)
        (su2GaugeObserver.residual x) = x) ∧
      Function.Injective
        (fun x => (su2GaugeObserver.reduction.proj x, su2GaugeObserver.residual x)) ∧
      (∀ x, 0 < su2GaugeObserver.nondegeneracy x) ∧
      (∀ g x, su2GaugeObserver.nondegeneracy (su2GaugeObserver.reduction.actRich g x)
        = su2GaugeObserver.nondegeneracy x) := by
  refine ⟨su2_gauge_invariant, ⟨(.keep, .p1), .axisLow, by decide⟩,
    su2GaugeObserver.fine_recovery, su2GaugeObserver.coarse_residual_injective,
    su2GaugeObserver.nondegeneracy_pos, su2GaugeObserver.nondegeneracy_invariant⟩

/-- **The abstract gauge weld, instantiated here.**  The generic theorem of
`Integration.GaugeObserver` applied to this lane: the observer's visible layer is
the gauge-reduced axis carrier, the deck subgroup is invisible on it, the
surviving rotation symmetry is not, the cover point is recoverable from axis plus
polarity, and the transverse certificate is positive and symmetry-invariant. -/
theorem su2_welded :
    (su2GaugeObserver.reduction.proj = su2GaugeReduction.red) ∧
      (∀ (s : Sheet) (x : AxisLift),
        su2GaugeReduction.red (su2GaugeReduction.actRich (gaugeDatum.incl s) x)
          = su2GaugeReduction.red x) ∧
      (∃ q y, su2GaugeReduction.actCoarse q y ≠ y) ∧
      (∀ x, su2GaugeObserver.reopen (su2GaugeObserver.reduction.proj x)
        (su2GaugeObserver.residual x) = x) ∧
      (∀ x, 0 < su2GaugeObserver.nondegeneracy x) ∧
      (∀ g x, su2GaugeObserver.nondegeneracy (su2Build.reduction.actRich g x)
        = su2GaugeObserver.nondegeneracy x) :=
  gauge_welded_theorem su2GaugeReduction su2Build axisEnum rfl su2_effective

/-- The retained residual is forced: three axes cannot carry six cover points. -/
theorem su2_residual_nontrivial : 2 ≤ Fintype.card LiftPolarity :=
  SymmetryResolvedObserver.residual_nontrivial su2GaugeObserver (by decide)

/-- The arithmetic of the lane: `6 = 3 × 2`, rich, visible and residual. -/
theorem su2_cards :
    Fintype.card AxisLift = 6 ∧ Fintype.card SU2Axis = 3 ∧
      Fintype.card LiftPolarity = 2 ∧ Fintype.card CoverSym = 6 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

end Integration.GaugeSU2
