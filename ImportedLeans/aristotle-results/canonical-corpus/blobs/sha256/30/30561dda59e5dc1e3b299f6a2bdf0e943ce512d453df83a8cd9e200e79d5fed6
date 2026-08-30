import Integration.StructuredObserver
import Integration.Base369Group
import Spine.EqualCardinality

/-!
# Two finite physics lanes as instances of the welded schema

The earlier integration census deliberately excluded every path named for the
Yang–Mills or Navier–Stokes lanes.  That exclusion is lifted here for exactly
two modules, and only for their **finite chart layers**:

* `Agda/DASHI/Physics/Closure/SU2SO3369HypervoxelBridge.agda` — the axis triple,
  the lift polarity, the two-sheeted cover interface and the `3·2 = 6`,
  `3·3 = 9` adapters;
* `Agda/DASHI/Physics/Closure/NSTriadKNStage3Ternary369Ledger.agda` — the
  Stage-3 six- and nine-state receipt coordinates (signed analytic disposition ×
  proof maturity) and their `HexTruth` / `NonaryTruth` charts.

Nothing analytic is imported, mirrored or used: no gauge field, no connection,
no energy estimate, no Sobolev tail, no PDE.  Every carrier below is a finite
set of at most nine elements.  **No claim about Yang–Mills, Navier–Stokes, mass
gap, regularity or any physical system is made or supported anywhere in this
file**; the modules' own names are the only reason the word "physics" appears.

What is proved:

* `axisLiftDoubleCover` — the corpus's `TwoSheetedCoverInterface` mirrored and
  inhabited: projection, central flip, two distinct lifts, no fixed point, and
  fibre completeness.  `axisLift_card` gives `3 × 2 = 6`.
* `axisLiftObserver` — the cover as a **symmetry-resolved observer**: the SSP
  orientation monoid acts through the central flip, the base axis is the coarse
  layer (the induced action is trivial — this is the orbit reduction), the lift
  polarity is the retained residual, and the transverse certificate is positive
  and flip-invariant.  So `6 ≃ 3 + polarity` is an instance of the same theorem
  as the SSP `9 ≃ 3 + phase`.
* `matrixSlotNonary` — the `3 × 3 = 9` output-axis × input-axis slot carrier in
  its nonary chart, with `matrixSlot_no_canonical_phase_cell` as the honest
  control: nine slots and nine SSP phase cells admit more than one bijection, so
  the shared numeral is not a map.
* `stage3NonaryChart`, `stage3SixChart` — the NS Stage-3 receipt coordinates as
  exact charts onto `NonaryTruth` and `HexTruth`.
* `nsStage3Observer` — the Stage-3 nonary coordinate as a symmetry-resolved
  observer: the signed disposition is the coarse layer with the polarity
  involution as induced action, proof maturity is the retained residual.
* `physics_actions_factor_through_sign` — the genuine cross-lane fact: the SSP
  lane action, the SU(2) lift flip and the Stage-3 disposition flip are all
  actions of the *same* effective `ℤ/2`, namely the image of
  `Integration.SSPWeave.orientationSign`.  This is a proved equivariance, not a
  shared word.
-/

namespace Integration.Physics369

open Spine
open Spine.MeanSplit
open Integration.SymmetryReduction
open Integration.StructuredObserver
open Integration.SSPWeave
open Integration.PolarResidual
open AgdaMirror.Base369 (TriTruth NonaryTruth HexTruth)
open AgdaMirror.DASHIAlgebra (Trit)

/-! ## The SU(2)/SO(3) axis-lift double cover -/

/-- Mirror of `SU2SO3369HypervoxelBridge.SU2Axis` (`= Axis3`). -/
inductive SU2Axis | axisLow | axisMid | axisHigh
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `LiftPolarity` (`= OrientationPolarity`). -/
inductive LiftPolarity | pos | neg
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `flipOrientationPolarity`. -/
def flipPolarity : LiftPolarity → LiftPolarity
  | .pos => .neg
  | .neg => .pos

/-- Mirror of `AxisLift`: axis × lift polarity. -/
abbrev AxisLift := SU2Axis × LiftPolarity

/-- Mirror of `flipAxisLift`, the central flip. -/
def flipAxisLift : AxisLift → AxisLift
  | (a, p) => (a, flipPolarity p)

/-- Mirror of the corpus's `TwoSheetedCoverInterface`.  Every field is a proof
obligation; in particular the flip must be free, which rules out the identity
involution a weaker projection contract would admit. -/
structure TwoSheetedCover (Cover Base : Type) where
  /-- The projection to the base. -/
  project : Cover → Base
  /-- The deck transformation. -/
  centralFlip : Cover → Cover
  /-- The positive lift. -/
  liftPositive : Base → Cover
  /-- The negative lift. -/
  liftNegative : Base → Cover
  /-- The positive lift is a section. -/
  positiveProjects : ∀ b, project (liftPositive b) = b
  /-- The negative lift is a section. -/
  negativeProjects : ∀ b, project (liftNegative b) = b
  /-- The two lifts differ. -/
  liftsDistinct : ∀ b, liftPositive b ≠ liftNegative b
  /-- The flip exchanges the lifts. -/
  centralFlipPositive : ∀ b, centralFlip (liftPositive b) = liftNegative b
  /-- And back. -/
  centralFlipNegative : ∀ b, centralFlip (liftNegative b) = liftPositive b
  /-- The projection is flip-invariant. -/
  projectionInvariant : ∀ x, project (centralFlip x) = project x
  /-- The flip is an involution. -/
  centralFlipInvolutive : ∀ x, centralFlip (centralFlip x) = x
  /-- The flip is free. -/
  centralFlipHasNoFixedPoint : ∀ x, centralFlip x ≠ x
  /-- Every point of the cover is one of the two lifts of its image. -/
  fibreComplete : ∀ x, x = liftPositive (project x) ∨ x = liftNegative (project x)

/-- **The corpus's finite double cover, checked.** -/
def axisLiftDoubleCover : TwoSheetedCover AxisLift SU2Axis where
  project := Prod.fst
  centralFlip := flipAxisLift
  liftPositive := fun a => (a, .pos)
  liftNegative := fun a => (a, .neg)
  positiveProjects := fun _ => rfl
  negativeProjects := fun _ => rfl
  liftsDistinct := by decide
  centralFlipPositive := fun _ => rfl
  centralFlipNegative := fun _ => rfl
  projectionInvariant := by decide
  centralFlipInvolutive := by decide
  centralFlipHasNoFixedPoint := by decide
  fibreComplete := by decide

theorem axisLift_card : Fintype.card AxisLift = 6 := by decide

theorem axis_card : Fintype.card SU2Axis = 3 := by decide

/-! ### The cover as a symmetry-resolved observer -/

/-- The SSP orientation acting on the cover through its sign: the `inverse`
orientation is the central flip. -/
def liftAction : FibreOrientation → AxisLift → AxisLift
  | .inverse, x => flipAxisLift x
  | .mediated, x => x
  | .forward, x => x

theorem liftAction_one (x : AxisLift) : liftAction 1 x = x := by
  obtain ⟨a, p⟩ := x; rfl

theorem liftAction_mul (g h : FibreOrientation) (x : AxisLift) :
    liftAction (g * h) x = liftAction g (liftAction h x) := by
  revert g h x; decide

theorem liftAction_involutive (g : FibreOrientation) (x : AxisLift) :
    liftAction g (liftAction g x) = x := by
  revert g x; decide

/-- **The gauge reduction `6 → 3`.**  The base axis is an equivariant quotient
of the cover, and the induced action is trivial: the base is the orbit space of
the central flip. -/
def axisReduction : EquivariantQuotient FibreOrientation AxisLift SU2Axis where
  actRich := liftAction
  actCoarse := fun _ a => a
  proj := Prod.fst
  rich_one := liftAction_one
  rich_mul := liftAction_mul
  coarse_one := fun _ => rfl
  coarse_mul := fun _ _ _ => rfl
  proj_surjective := by decide
  square := by decide

/-- The observer data: the residual is the lift polarity, and the transverse
class coordinate is the (flip-invariant) base axis. -/
def axisLiftBuild : ObserverBuild FibreOrientation AxisLift SU2Axis LiftPolarity SU2Axis where
  reduction := axisReduction
  actInv := liftAction
  actInv_left := liftAction_involutive
  actInv_right := liftAction_involutive
  residual := Prod.snd
  reopen := fun a p => (a, p)
  reopen_project := fun _ => rfl
  cls := Prod.fst
  cls_invariant := by decide
  cls_separates := by decide

/-- The six cover points, enumerated. -/
def axisEnum : AxisLift ≃ Fin 6 where
  toFun
    | (.axisLow, .pos) => 0
    | (.axisLow, .neg) => 1
    | (.axisMid, .pos) => 2
    | (.axisMid, .neg) => 3
    | (.axisHigh, .pos) => 4
    | (.axisHigh, .neg) => 5
  invFun := ![(.axisLow, .pos), (.axisLow, .neg), (.axisMid, .pos), (.axisMid, .neg),
    (.axisHigh, .pos), (.axisHigh, .neg)]
  left_inv := by decide
  right_inv := by decide

/-- **The SU(2) axis-lift lane as a symmetry-resolved observer.** -/
noncomputable def axisLiftObserver :
    SymmetryResolvedObserver FibreOrientation AxisLift SU2Axis LiftPolarity 6 :=
  axisLiftBuild.toObserver axisEnum

/-- The three welded conclusions on the axis-lift lane. -/
theorem axisLift_theorem :
    (Function.Surjective axisLiftObserver.reduction.proj ∧
        ∀ g x, axisLiftObserver.reduction.proj (axisLiftObserver.reduction.actRich g x)
          = axisLiftObserver.reduction.actCoarse g (axisLiftObserver.reduction.proj x)) ∧
      (∀ x, axisLiftObserver.reopen (axisLiftObserver.reduction.proj x)
        (axisLiftObserver.residual x) = x) ∧
      Function.Injective
        (fun x => (axisLiftObserver.reduction.proj x, axisLiftObserver.residual x)) ∧
      (∀ x, 0 < axisLiftObserver.nondegeneracy x) ∧
      (∀ g x, axisLiftObserver.nondegeneracy (axisLiftObserver.reduction.actRich g x)
        = axisLiftObserver.nondegeneracy x) :=
  axisLiftObserver.symmetry_resolved_theorem

/-- The lift polarity is not removable: three base axes cannot carry six cover
points. -/
theorem axisLift_residual_nontrivial : 2 ≤ Fintype.card LiftPolarity :=
  SymmetryResolvedObserver.residual_nontrivial axisLiftObserver (by decide)

/-! ## The `3 × 3 = 9` operator-slot carrier -/

/-- Mirror of `MatrixSlot`: output axis × input axis. -/
abbrev MatrixSlot := SU2Axis × SU2Axis

/-- Mirror of `matrixSlotToNonary` / `nonaryToMatrixSlot`, as an equivalence. -/
def matrixSlotNonary : MatrixSlot ≃ NonaryTruth where
  toFun
    | (.axisLow, .axisLow) => .n0
    | (.axisLow, .axisMid) => .n1
    | (.axisLow, .axisHigh) => .n2
    | (.axisMid, .axisLow) => .n3
    | (.axisMid, .axisMid) => .n4
    | (.axisMid, .axisHigh) => .n5
    | (.axisHigh, .axisLow) => .n6
    | (.axisHigh, .axisMid) => .n7
    | (.axisHigh, .axisHigh) => .n8
  invFun
    | .n0 => (.axisLow, .axisLow)
    | .n1 => (.axisLow, .axisMid)
    | .n2 => (.axisLow, .axisHigh)
    | .n3 => (.axisMid, .axisLow)
    | .n4 => (.axisMid, .axisMid)
    | .n5 => (.axisMid, .axisHigh)
    | .n6 => (.axisHigh, .axisLow)
    | .n7 => (.axisHigh, .axisMid)
    | .n8 => (.axisHigh, .axisHigh)
  left_inv := by decide
  right_inv := by decide

theorem matrixSlot_card : Fintype.card MatrixSlot = 9 := by decide

/-- **The honest control.**  The nine operator slots and the nine SSP phase
cells have equal cardinality and therefore admit more than one bijection: the
shared numeral nine is not a canonical map between the two lanes. -/
theorem matrixSlot_no_canonical_phase_cell :
    ∃ e f : MatrixSlot ≃ FullPhaseCell, e ≠ f :=
  Spine.exists_two_distinct_equivs (by decide) (by decide)

/-! ## The NS Stage-3 receipt coordinates -/

/-- Mirror of `Stage3NonaryCoordinate`: a signed analytic disposition together
with a proof-maturity role. -/
abbrev Stage3Nonary := Trit × TriTruth

/-- Mirror of `Stage3SixCoordinate`: a signed analytic disposition together with
a theorem-closed flag. -/
abbrev Stage3Six := Trit × Bool

/-- Mirror of `encodeNonary` / `decodeNonary`, as an equivalence. -/
def stage3NonaryChart : Stage3Nonary ≃ NonaryTruth where
  toFun
    | (.neg, .low) => .n0
    | (.neg, .mid) => .n1
    | (.neg, .high) => .n2
    | (.zer, .low) => .n3
    | (.zer, .mid) => .n4
    | (.zer, .high) => .n5
    | (.pos, .low) => .n6
    | (.pos, .mid) => .n7
    | (.pos, .high) => .n8
  invFun
    | .n0 => (.neg, .low)
    | .n1 => (.neg, .mid)
    | .n2 => (.neg, .high)
    | .n3 => (.zer, .low)
    | .n4 => (.zer, .mid)
    | .n5 => (.zer, .high)
    | .n6 => (.pos, .low)
    | .n7 => (.pos, .mid)
    | .n8 => (.pos, .high)
  left_inv := by decide
  right_inv := by decide

/-- Mirror of `encodeSix` / `decodeSix`, as an equivalence. -/
def stage3SixChart : Stage3Six ≃ HexTruth where
  toFun
    | (.neg, false) => .h0
    | (.neg, true) => .h1
    | (.zer, false) => .h2
    | (.zer, true) => .h3
    | (.pos, false) => .h4
    | (.pos, true) => .h5
  invFun
    | .h0 => (.neg, false)
    | .h1 => (.neg, true)
    | .h2 => (.zer, false)
    | .h3 => (.zer, true)
    | .h4 => (.pos, false)
    | .h5 => (.pos, true)
  left_inv := by decide
  right_inv := by decide

theorem stage3_cards : Fintype.card Stage3Nonary = 9 ∧ Fintype.card Stage3Six = 6 := by
  refine ⟨by decide, by decide⟩

/-- The orientation acting on a Stage-3 nonary coordinate: `inverse` reverses the
signed analytic disposition and leaves the maturity role alone. -/
def dispositionAction : FibreOrientation → Stage3Nonary → Stage3Nonary
  | .inverse, (d, m) => (Trit.inv d, m)
  | .mediated, x => x
  | .forward, x => x

theorem dispositionAction_one (x : Stage3Nonary) : dispositionAction 1 x = x := by
  obtain ⟨d, m⟩ := x; rfl

theorem dispositionAction_mul (g h : FibreOrientation) (x : Stage3Nonary) :
    dispositionAction (g * h) x = dispositionAction g (dispositionAction h x) := by
  revert g h x; decide

theorem dispositionAction_involutive (g : FibreOrientation) (x : Stage3Nonary) :
    dispositionAction g (dispositionAction g x) = x := by
  revert g x; decide

/-- The disposition action on the trit alone. -/
def dispositionCoarse : FibreOrientation → Trit → Trit
  | .inverse, d => Trit.inv d
  | .mediated, d => d
  | .forward, d => d

/-- **The Stage-3 reduction `9 → 3`.**  The signed disposition is an equivariant
quotient of the nine-state receipt coordinate, with the polarity involution as
induced action. -/
def stage3Reduction : EquivariantQuotient FibreOrientation Stage3Nonary Trit where
  actRich := dispositionAction
  actCoarse := dispositionCoarse
  proj := Prod.fst
  rich_one := dispositionAction_one
  rich_mul := dispositionAction_mul
  coarse_one := fun t => by cases t <;> rfl
  coarse_mul := by decide
  proj_surjective := by decide
  square := by decide

theorem stage3Reduction_action_nontrivial : ∃ g t, stage3Reduction.actCoarse g t ≠ t :=
  ⟨.inverse, Trit.neg, by decide⟩

/-- The observer data: proof maturity is the retained residual, and it is
invariant under the disposition flip, so it is also the transverse class. -/
def stage3Build : ObserverBuild FibreOrientation Stage3Nonary Trit TriTruth TriTruth where
  reduction := stage3Reduction
  actInv := dispositionAction
  actInv_left := dispositionAction_involutive
  actInv_right := dispositionAction_involutive
  residual := Prod.snd
  reopen := fun d m => (d, m)
  reopen_project := fun _ => rfl
  cls := Prod.snd
  cls_invariant := by decide
  cls_separates := by decide

/-- The nine Stage-3 coordinates, enumerated through the nonary chart. -/
def stage3Enum : Stage3Nonary ≃ Fin 9 where
  toFun
    | (.neg, .low) => 0
    | (.neg, .mid) => 1
    | (.neg, .high) => 2
    | (.zer, .low) => 3
    | (.zer, .mid) => 4
    | (.zer, .high) => 5
    | (.pos, .low) => 6
    | (.pos, .mid) => 7
    | (.pos, .high) => 8
  invFun := ![(.neg, .low), (.neg, .mid), (.neg, .high), (.zer, .low), (.zer, .mid),
    (.zer, .high), (.pos, .low), (.pos, .mid), (.pos, .high)]
  left_inv := by decide
  right_inv := by decide

/-- **The NS Stage-3 receipt lane as a symmetry-resolved observer.** -/
noncomputable def nsStage3Observer :
    SymmetryResolvedObserver FibreOrientation Stage3Nonary Trit TriTruth 9 :=
  stage3Build.toObserver stage3Enum

/-- The three welded conclusions on the Stage-3 lane. -/
theorem nsStage3_theorem :
    (Function.Surjective nsStage3Observer.reduction.proj ∧
        ∀ g x, nsStage3Observer.reduction.proj (nsStage3Observer.reduction.actRich g x)
          = nsStage3Observer.reduction.actCoarse g (nsStage3Observer.reduction.proj x)) ∧
      (∀ x, nsStage3Observer.reopen (nsStage3Observer.reduction.proj x)
        (nsStage3Observer.residual x) = x) ∧
      Function.Injective
        (fun x => (nsStage3Observer.reduction.proj x, nsStage3Observer.residual x)) ∧
      (∀ x, 0 < nsStage3Observer.nondegeneracy x) ∧
      (∀ g x, nsStage3Observer.nondegeneracy (nsStage3Observer.reduction.actRich g x)
        = nsStage3Observer.nondegeneracy x) :=
  nsStage3Observer.symmetry_resolved_theorem

/-- Maturity is not removable: three dispositions cannot carry nine receipt
coordinates. -/
theorem nsStage3_residual_nontrivial : 2 ≤ Fintype.card TriTruth :=
  SymmetryResolvedObserver.residual_nontrivial nsStage3Observer (by decide)

/-! ## The cross-lane fact -/

/-- **One effective `ℤ/2` across three lanes.**  The SSP lane-state action, the
SU(2) central flip and the Stage-3 disposition flip all factor through the same
homomorphism `orientationSign : FibreOrientation → ℤ/2`.  This is a proved
equivariance between the lanes' actions, not a shared vocabulary. -/
theorem physics_actions_factor_through_sign :
    (∀ g h x, orientationSign g = orientationSign h → laneAction g x = laneAction h x) ∧
      (∀ g h x, orientationSign g = orientationSign h → liftAction g x = liftAction h x) ∧
      (∀ g h x, orientationSign g = orientationSign h →
        dispositionAction g x = dispositionAction h x) := by
  refine ⟨fun g h x => laneAction_factors_through_sign g h x, ?_, ?_⟩
  · decide
  · decide

/-- The physics tranche in one statement: a checked two-sheeted cover with
`3 × 2 = 6`, a `3 × 3 = 9` slot carrier that is *not* canonically the SSP
nine-cell carrier, the two welded observers, and the shared effective `ℤ/2`. -/
theorem physics_instances_summary :
    (∀ x : AxisLift, axisLiftDoubleCover.centralFlip x ≠ x) ∧
      Fintype.card AxisLift = 6 ∧
      Fintype.card MatrixSlot = 9 ∧
      (∃ e f : MatrixSlot ≃ FullPhaseCell, e ≠ f) ∧
      (∀ x, 0 < axisLiftObserver.nondegeneracy x) ∧
      (∀ x, 0 < nsStage3Observer.nondegeneracy x) ∧
      (∀ g x, axisLiftObserver.nondegeneracy (axisLiftObserver.reduction.actRich g x)
        = axisLiftObserver.nondegeneracy x) ∧
      (∀ g x, nsStage3Observer.nondegeneracy (nsStage3Observer.reduction.actRich g x)
        = nsStage3Observer.nondegeneracy x) :=
  ⟨axisLiftDoubleCover.centralFlipHasNoFixedPoint, axisLift_card, matrixSlot_card,
    matrixSlot_no_canonical_phase_cell, axisLiftObserver.nondegeneracy_pos,
    nsStage3Observer.nondegeneracy_pos, axisLiftObserver.nondegeneracy_invariant,
    nsStage3Observer.nondegeneracy_invariant⟩

end Integration.Physics369
