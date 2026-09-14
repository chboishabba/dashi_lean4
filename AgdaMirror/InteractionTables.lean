import Mathlib

/-!
# Lean mirrors of the DASHI two-coordinate value tables

Three genuinely independent corpus surfaces carry a *total* function of two
coordinates into a numeric value.  They are transcribed here so that the
interaction owner `Integration.SeparabilityContrast` can be tested against real
source material rather than against synthetic tables.

* `Agda/DASHI/Visualisation/FiniteAnisotropicKernelExact.agda` —
  `positiveKernelValue : BoundarySharpness → RadiusClass → Nat`, an explicit
  three-by-three table, together with `sharpnessCode` and the corpus lemma
  `outsideContributesZero`.
* `Agda/DASHI/Visualisation/SelfConsistentEventRendererExact.agda` —
  `SharedDepth`, `sharedDepthWeight`, `legacyDecreasingWeight` and the
  *pair* `combinedAffinity` (a product) / `additiveAffinity` (a sum), with the
  corpus lemmas `closerBranchGetsLargerWeight`, `canonicalProductAffinity`,
  `legacyWeightHasWrongDirection` and `productAndAdditiveAreModellingChoices`.
* `Agda/DASHI/Visualisation/MeasureFieldAdapterExact.agda` —
  `Field2`, `swapField`, `SliceChoice` and
  `restrictField : SliceChoice → Field2 → Nat`.

The corpus's contextual and intersectional surfaces are *not* transcribed here:
they are already mirrored by `Integration.CounterfactualEffect` and
`AgdaMirror.NonFactorabilityKernels`, and `Integration.InteractionWelds` reuses
those rather than introducing a second reading of the same Agda text.

**Transcription boundary.**  `Nat` is Mathlib's `ℕ`, `≡` is `Eq`.
No Agda typechecker was run, so this file is Lean text about Lean definitions
transcribing Agda text; it is not evidence about the Agda files.  None of the
numeric values below is an empirical estimate; the corpus states them as
structural witnesses and they are mirrored with that status.
-/

namespace AgdaMirror.InteractionTables

/-! ## 1. The anisotropic kernel table -/

namespace AnisotropicKernel

/-- Mirror of `BoundarySharpness`. -/
inductive BoundarySharpness
  | softBoundary | mediumBoundary | hardBoundary
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Mirror of `RadiusClass`. -/
inductive RadiusClass
  | insideEllipsoid | boundaryEllipsoid | outsideEllipsoid
  deriving DecidableEq, Repr, Fintype, Inhabited

open BoundarySharpness RadiusClass

/-- Mirror of `sharpnessCode`. -/
def sharpnessCode : BoundarySharpness → ℕ
  | softBoundary => 1
  | mediumBoundary => 2
  | hardBoundary => 4

/-- Mirror of `positiveKernelValue`: the corpus's explicit three-by-three
table. -/
def positiveKernelValue : BoundarySharpness → RadiusClass → ℕ
  | softBoundary, insideEllipsoid => 2
  | softBoundary, boundaryEllipsoid => 1
  | softBoundary, outsideEllipsoid => 0
  | mediumBoundary, insideEllipsoid => 3
  | mediumBoundary, boundaryEllipsoid => 1
  | mediumBoundary, outsideEllipsoid => 0
  | hardBoundary, insideEllipsoid => 4
  | hardBoundary, boundaryEllipsoid => 1
  | hardBoundary, outsideEllipsoid => 0

/-- Mirror of the corpus lemma `outsideContributesZero`. -/
theorem outsideContributesZero (s : BoundarySharpness) :
    positiveKernelValue s outsideEllipsoid = 0 := by
  cases s <;> rfl

end AnisotropicKernel

/-! ## 2. The renderer affinity pair -/

namespace RendererAffinity

/-- Mirror of `SharedDepth`. -/
inductive SharedDepth
  | shared0 | shared1 | shared2 | shared3
  deriving DecidableEq, Repr, Fintype, Inhabited

open SharedDepth

/-- Mirror of `sharedDepthWeight`. -/
def sharedDepthWeight : SharedDepth → ℕ
  | shared0 => 1
  | shared1 => 2
  | shared2 => 3
  | shared3 => 4

/-- Mirror of the corpus lemma `closerBranchGetsLargerWeight`. -/
theorem closerBranchGetsLargerWeight :
    sharedDepthWeight shared0 = 1 ∧ sharedDepthWeight shared3 = 4 := ⟨rfl, rfl⟩

/-- Mirror of `legacyDecreasingWeight`. -/
def legacyDecreasingWeight : SharedDepth → ℕ
  | shared0 => 4
  | shared1 => 3
  | shared2 => 2
  | shared3 => 1

/-- Mirror of the corpus lemma `legacyWeightHasWrongDirection`. -/
theorem legacyWeightHasWrongDirection :
    legacyDecreasingWeight shared0 = 4 ∧ legacyDecreasingWeight shared3 = 1 :=
  ⟨rfl, rfl⟩

/-- Mirror of `combinedAffinity`: the *multiplicative* combination rule. -/
def combinedAffinity (euclideanKernel : ℕ) (depth : SharedDepth) : ℕ :=
  euclideanKernel * sharedDepthWeight depth

/-- Mirror of the corpus lemma `canonicalProductAffinity`. -/
theorem canonicalProductAffinity : combinedAffinity 3 shared2 = 9 := rfl

/-- Mirror of `additiveAffinity`: the *additive* combination rule. -/
def additiveAffinity (euclideanKernel : ℕ) (depth : SharedDepth) : ℕ :=
  euclideanKernel + sharedDepthWeight depth

/-- Mirror of the corpus lemma `productAndAdditiveAreModellingChoices`: the two
rules disagree at one point.  This is all the corpus claims about the pair. -/
theorem productAndAdditiveAreModellingChoices :
    combinedAffinity 3 shared2 ≠ additiveAffinity 3 shared2 := by decide

end RendererAffinity

/-! ## 3. The slice restriction table -/

namespace MeasureField

/-- Mirror of `Field2`. -/
structure Field2 where
  fieldLeft : ℕ
  fieldRight : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Mirror of `swapField`. -/
def swapField (f : Field2) : Field2 := ⟨f.fieldRight, f.fieldLeft⟩

/-- Mirror of `SliceChoice`. -/
inductive SliceChoice
  | leftCellSlice | rightCellSlice
  deriving DecidableEq, Repr, Fintype, Inhabited

open SliceChoice

/-- Mirror of `restrictField`. -/
def restrictField : SliceChoice → Field2 → ℕ
  | leftCellSlice, f => f.fieldLeft
  | rightCellSlice, f => f.fieldRight

/-- Mirror of `ImageTone`. -/
inductive ImageTone
  | darkTone | brightTone
  deriving DecidableEq, Repr, Inhabited

/-- Mirror of `coarseColour`. -/
def coarseColour : ℕ → ImageTone
  | 0 => ImageTone.darkTone
  | _ + 1 => ImageTone.brightTone

end MeasureField

end AgdaMirror.InteractionTables
