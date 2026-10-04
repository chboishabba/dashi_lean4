import Mathlib
import YangMills.CMP119ResidualReflectionCut

/-!
# CMP119 source-polymer reflection audit

Complete-action reflection positivity is a source theorem, not a smallness
corollary.  This file gives the finite source audit a literal four-way support
classifier and an explicit falsification theorem for crossing kernels.

The classifier itself is deliberately carrier-agnostic: a concrete CMP119
source dictionary must supply the two booleans/predicates from the ACTUAL
periodic polymer support.  No theorem here claims that dictionary already
exists.
-/

namespace RequestProject.YangMills

inductive CMP119PolymerPlacement
  | positive
  | negative
  | crossing
  | empty
  deriving DecidableEq, Repr

/--
Classify a polymer by whether its actual support meets the positive and
negative open time halves.  Boundary-only/absent support is represented by the
`false,false` case; a concrete source dictionary may refine that distinction
before invoking this classifier.
-/
def cmp119ClassifyPolymerSupport
    (touchesPositive touchesNegative : Bool) : CMP119PolymerPlacement :=
  match touchesPositive, touchesNegative with
  | false, false => .empty
  | true, false => .positive
  | false, true => .negative
  | true, true => .crossing

/-- Source-facing dictionary from actual polymers to time-plane support data. -/
structure CMP119PolymerReflectionDictionary (Polymer : Type*) where
  touchesPositive : Polymer → Bool
  touchesNegative : Polymer → Bool

namespace CMP119PolymerReflectionDictionary

/-- The induced literal four-way placement of a source polymer. -/
def placement
    {Polymer : Type*}
    (dict : CMP119PolymerReflectionDictionary Polymer)
    (X : Polymer) : CMP119PolymerPlacement :=
  cmp119ClassifyPolymerSupport
    (dict.touchesPositive X) (dict.touchesNegative X)

/-- Crossing is exactly simultaneous support on both time halves. -/
theorem placement_eq_crossing_iff
    {Polymer : Type*}
    (dict : CMP119PolymerReflectionDictionary Polymer)
    (X : Polymer) :
    dict.placement X = CMP119PolymerPlacement.crossing ↔
      dict.touchesPositive X = true ∧ dict.touchesNegative X = true := by
  cases hpos : dict.touchesPositive X <;>
    cases hneg : dict.touchesNegative X <;>
    simp [placement, cmp119ClassifyPolymerSupport, hpos, hneg]

/-- Positive-only support is exactly the corresponding truth-table branch. -/
theorem placement_eq_positive_iff
    {Polymer : Type*}
    (dict : CMP119PolymerReflectionDictionary Polymer)
    (X : Polymer) :
    dict.placement X = CMP119PolymerPlacement.positive ↔
      dict.touchesPositive X = true ∧ dict.touchesNegative X = false := by
  cases hpos : dict.touchesPositive X <;>
    cases hneg : dict.touchesNegative X <;>
    simp [placement, cmp119ClassifyPolymerSupport, hpos, hneg]

/-- Negative-only support is exactly the corresponding truth-table branch. -/
theorem placement_eq_negative_iff
    {Polymer : Type*}
    (dict : CMP119PolymerReflectionDictionary Polymer)
    (X : Polymer) :
    dict.placement X = CMP119PolymerPlacement.negative ↔
      dict.touchesPositive X = false ∧ dict.touchesNegative X = true := by
  cases hpos : dict.touchesPositive X <;>
    cases hneg : dict.touchesNegative X <;>
    simp [placement, cmp119ClassifyPolymerSupport, hpos, hneg]

end CMP119PolymerReflectionDictionary

/--
A concrete negative quadratic-form witness falsifies reflection positivity of
that exact crossing kernel.  This is the finite-source failure mode required by
Block B: one counterexample is enough to rule out the current RP route for that
source kernel.
-/
theorem cmp119_crossing_kernel_falsified_by_negative_quadratic
    {ι : Type*} [Fintype ι]
    (kernel : ι → ι → ℝ)
    (test : ι → ℝ)
    (hneg : indexedReflectionQuadratic kernel test < 0) :
    ¬ (∀ f : ι → ℝ, 0 ≤ indexedReflectionQuadratic kernel f) := by
  intro hRP
  exact (not_lt_of_ge (hRP test)) hneg

/-- Build the exact residual cross-plane certificate once symmetry and PSD are proved. -/
def cmp119CrossingCertificate
    {ι : Type*} [Fintype ι]
    (kernel : ι → ι → ℝ)
    (hSymm : ∀ i j, kernel i j = kernel j i)
    (hRP : ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic kernel test) :
    CMP119SectorReflectionCertificate ι :=
  .crossKernel kernel hSymm hRP

/--
The three genuinely nontrivial source sectors after the constant-vacuum weld.
This is a finite audit set, not a claim that the certificates exist.
-/
def cmp119NontrivialReflectionSectors : Finset CMP119ResidualSector :=
  { CMP119ResidualSector.regularE
  , CMP119ResidualSector.rOperation
  , CMP119ResidualSector.boundaryB }

@[simp] theorem cmp119_regularE_in_nontrivial_reflection_sectors :
    CMP119ResidualSector.regularE ∈ cmp119NontrivialReflectionSectors := by
  simp [cmp119NontrivialReflectionSectors]

@[simp] theorem cmp119_rOperation_in_nontrivial_reflection_sectors :
    CMP119ResidualSector.rOperation ∈ cmp119NontrivialReflectionSectors := by
  simp [cmp119NontrivialReflectionSectors]

@[simp] theorem cmp119_boundaryB_in_nontrivial_reflection_sectors :
    CMP119ResidualSector.boundaryB ∈ cmp119NontrivialReflectionSectors := by
  simp [cmp119NontrivialReflectionSectors]

@[simp] theorem cmp119_vacuumV_not_in_nontrivial_reflection_sectors :
    CMP119ResidualSector.vacuumV ∉ cmp119NontrivialReflectionSectors := by
  simp [cmp119NontrivialReflectionSectors]

end RequestProject.YangMills
