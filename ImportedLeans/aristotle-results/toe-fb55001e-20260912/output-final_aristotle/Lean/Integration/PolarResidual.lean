import Integration.TernaryHub

/-!
# The residual-bearing 9 → 6 projection is lossless

`DASHI/Physics/Closure/SSP369PolarResidualQuotient.agda` calls itself an "exact
reopening of the existing residual-bearing 9 → 6 projection" and proves
`reopen (polarProject x) ≡ x`.  It is careful to say that this is *not* a direct
`9 → 6` retraction: the zero branch is not discarded, its phase is retained as a
typed residual.  Mirrored and completed here:

* `polarEquiv : FullPhaseCell ≃ PolarProjectionResult` — the projection is a
  **bijection** onto `PolarPhaseCell ⊕ DepthWheelPhase`, so what looks like a
  `9 → 6` collapse is the exact decomposition `9 = 6 + 3`
  (`polar_cardinalities`);
* `no_retraction_to_polar` — and a genuine `9 → 6` retraction is impossible: no
  injection `FullPhaseCell → PolarPhaseCell` exists, so the residual is not
  removable bookkeeping;
* `project_preserves_phase` — the depth-wheel phase survives on both branches,
  which is exactly why the projection is reopenable;
* `polarTransport` — the polarity involution `negateTrit` is carried by the
  projection to the sign flip on the polar branch, fixing the residual branch: a
  level-iv preservation statement, not just a bijection of carriers;
* `kernelTritHub` — the carrier `KernelTrit` is the ternary hub, with
  `negateTrit` the hub polarity, so this quotient sits over the same ternary
  object as the rest of the spine.

Scope: all four carriers here are finite (9, 6, 3, 2 elements).  No physical
claim is made or implied; "phase" and "polar" are the source's names for the
constructors.
-/

namespace Integration.PolarResidual

open Integration.Levels
open Integration.TernaryHub
open AgdaMirror.DASHIAlgebra (Trit)

/-- Mirror of `DASHI.Biology.TriadicKernelLiftQuotientExact.KernelTrit`. -/
inductive KernelTrit | negativeTrit | zeroTrit | positiveTrit
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `negateTrit`. -/
def negateTrit : KernelTrit → KernelTrit
  | .negativeTrit => .positiveTrit
  | .zeroTrit => .zeroTrit
  | .positiveTrit => .negativeTrit

theorem negateTrit_involutive (t : KernelTrit) : negateTrit (negateTrit t) = t := by
  cases t <;> rfl

/-- Mirror of `DASHI.Biology.TernaryCantorWheelDiffusionExact.PolarTrit`. -/
inductive PolarTrit | polarNegative | polarPositive
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `polarToTrit`. -/
def polarToTrit : PolarTrit → KernelTrit
  | .polarNegative => .negativeTrit
  | .polarPositive => .positiveTrit

/-- Mirror of `SSPPrimeLane369DepthWheelCantorBridge.DepthWheelPhase`. -/
inductive DepthWheelPhase | phase0 | phase1 | phase2
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `nextDepthWheelPhase`. -/
def nextDepthWheelPhase : DepthWheelPhase → DepthWheelPhase
  | .phase0 => .phase1 | .phase1 => .phase2 | .phase2 => .phase0

theorem nextDepthWheelPhase_orderThree (p : DepthWheelPhase) :
    nextDepthWheelPhase (nextDepthWheelPhase (nextDepthWheelPhase p)) = p := by
  cases p <;> rfl

/-- Mirror of `FullPhaseCell`: the nine full phase cells. -/
abbrev FullPhaseCell := KernelTrit × DepthWheelPhase

/-- Mirror of `PolarPhaseCell`: the six polar phase cells. -/
abbrev PolarPhaseCell := PolarTrit × DepthWheelPhase

/-- Mirror of `embedPolarPhaseCell`. -/
def embedPolarPhaseCell : PolarPhaseCell → FullPhaseCell
  | (p, ph) => (polarToTrit p, ph)

/-- Mirror of `SSPPrimeLane369DepthAddressWheel.PolarProjectionResult`: the polar
branch together with the retained zero-branch residual. -/
inductive PolarProjectionResult
  /-- A cell with a definite polarity. -/
  | projectedPolar (cell : PolarPhaseCell)
  /-- The zero branch, whose phase is retained rather than discarded. -/
  | zeroBranchResidual (phase : DepthWheelPhase)
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `polarProject`. -/
def polarProject : FullPhaseCell → PolarProjectionResult
  | (.negativeTrit, ph) => .projectedPolar (.polarNegative, ph)
  | (.zeroTrit, ph) => .zeroBranchResidual ph
  | (.positiveTrit, ph) => .projectedPolar (.polarPositive, ph)

/-- Mirror of `reopenPolarResult`. -/
def reopenPolarResult : PolarProjectionResult → FullPhaseCell
  | .projectedPolar cell => embedPolarPhaseCell cell
  | .zeroBranchResidual ph => (.zeroTrit, ph)

/-- Mirror of `reopenPolarProjectExact`. -/
theorem reopen_project (c : FullPhaseCell) : reopenPolarResult (polarProject c) = c := by
  obtain ⟨t, ph⟩ := c; cases t <;> rfl

/-- The other round trip, which the source does not state. -/
theorem project_reopen (r : PolarProjectionResult) : polarProject (reopenPolarResult r) = r := by
  rcases r with ⟨p, ph⟩ | ph
  · cases p <;> rfl
  · rfl

/-- **The projection is an equivalence**: `9 = 6 + 3`, the three being the
retained zero-branch phases. -/
def polarEquiv : FullPhaseCell ≃ PolarProjectionResult where
  toFun := polarProject
  invFun := reopenPolarResult
  left_inv := reopen_project
  right_inv := project_reopen

theorem polar_cardinalities :
    Fintype.card FullPhaseCell = 9 ∧ Fintype.card PolarPhaseCell = 6 ∧
      Fintype.card DepthWheelPhase = 3 ∧ 6 + 3 = 9 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- **The residual is not removable**: there is no injection of the nine full
cells into the six polar cells, so no direct `9 → 6` retraction exists.  This is
the exact sense in which the source's warning is a theorem. -/
theorem no_retraction_to_polar : ¬ ∃ f : FullPhaseCell → PolarPhaseCell, Function.Injective f := by
  rintro ⟨f, hf⟩
  have h := Fintype.card_le_of_injective f hf
  rw [show Fintype.card FullPhaseCell = 9 from rfl,
    show Fintype.card PolarPhaseCell = 6 from rfl] at h
  omega

/-- Mirror of `polarProjectAfterEmbedding`. -/
theorem project_embed (cell : PolarPhaseCell) :
    polarProject (embedPolarPhaseCell cell) = .projectedPolar cell := by
  obtain ⟨p, ph⟩ := cell; cases p <;> rfl

/-- Mirror of `zeroProjectionRetainsPhase`. -/
theorem zero_retains_phase (ph : DepthWheelPhase) :
    polarProject (.zeroTrit, ph) = .zeroBranchResidual ph := rfl

/-- The phase coordinate of a projection result. -/
def phaseOf : PolarProjectionResult → DepthWheelPhase
  | .projectedPolar (_, ph) => ph
  | .zeroBranchResidual ph => ph

/-- **Both branches keep the phase**, which is why the projection is
reopenable. -/
theorem project_preserves_phase (c : FullPhaseCell) : phaseOf (polarProject c) = c.2 := by
  obtain ⟨t, ph⟩ := c; cases t <;> rfl

/-! ## The polarity involution is preserved -/

/-- Polarity reversal on full cells. -/
def negateCell : FullPhaseCell → FullPhaseCell
  | (t, ph) => (negateTrit t, ph)

/-- Polarity reversal on projection results: swap the polar sign, fix the
residual branch. -/
def negateResult : PolarProjectionResult → PolarProjectionResult
  | .projectedPolar (.polarNegative, ph) => .projectedPolar (.polarPositive, ph)
  | .projectedPolar (.polarPositive, ph) => .projectedPolar (.polarNegative, ph)
  | .zeroBranchResidual ph => .zeroBranchResidual ph

/-- **Level iv**: the residual-bearing projection is polarity-equivariant. -/
def polarTransport : Transport FullPhaseCell PolarProjectionResult negateCell negateResult where
  map := polarEquiv
  equivariant := by rintro ⟨t, ph⟩; cases t <;> rfl

/-- The kernel-trit carrier is the ternary hub, with `negateTrit` the hub
polarity. -/
def kernelTritHub : Transport KernelTrit Trit negateTrit Trit.inv where
  map :=
    { toFun := fun t => match t with
        | .negativeTrit => .neg | .zeroTrit => .zer | .positiveTrit => .pos
      invFun := fun t => match t with
        | .neg => .negativeTrit | .zer => .zeroTrit | .pos => .positiveTrit
      left_inv := by decide
      right_inv := by decide }
  equivariant := by decide

/-- Summary of the residual row: an exact `9 ≃ 6 + 3` decomposition, no direct
retraction, phase retained on both branches, and polarity preserved. -/
theorem polar_residual_summary :
    (∀ c : FullPhaseCell, reopenPolarResult (polarProject c) = c) ∧
      (∀ r, polarProject (reopenPolarResult r) = r) ∧
      (¬ ∃ f : FullPhaseCell → PolarPhaseCell, Function.Injective f) ∧
      (∀ c : FullPhaseCell, phaseOf (polarProject c) = c.2) ∧
      (∀ c, polarProject (negateCell c) = negateResult (polarProject c)) :=
  ⟨reopen_project, project_reopen, no_retraction_to_polar, project_preserves_phase,
    polarTransport.equivariant⟩

end Integration.PolarResidual
