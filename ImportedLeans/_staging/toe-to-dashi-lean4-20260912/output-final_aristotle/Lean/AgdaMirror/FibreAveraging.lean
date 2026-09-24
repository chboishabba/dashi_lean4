import Mathlib

/-!
# Lean mirror of the DASHI finite fibre-averaging pair

Faithful transcription of the finite probability-fibre model of

* `Agda/DASHI/Analysis/NormalizedFibreAveragingExact.agda`, and
* `Agda/DASHI/Analysis/WeightedCoarseFineOrthogonalExact.agda`.

Both Agda modules parameterise a module over an arbitrary coarse carrier
`Base : Set`; the transcription keeps `Base` as an arbitrary `Type`.  A fine
point is a coarse point together with a two-element fibre coordinate, the two
fibre weights are `½`, and the derived operators are

```
  pullback : (Base → ℚ) → (Base × Fibre2 → ℚ)
  average  : (Base × Fibre2 → ℚ) → (Base → ℚ)
  P = pullback ∘ average          (the within-fibre mean, read back fibrewise)
  Q = id − P                      (the residual)
```

Everything proved in the Agda originals by `solve-∀` is proved here by `ring`
or by case analysis on the fibre coordinate.

**Transcription boundary.**  `ℚ` is Mathlib's `Rat`, not `Data.Rational.Base`;
`≡` is `Eq`.  No Agda typechecker was run in this environment, so this file is
Lean text about Lean definitions transcribing Agda text, and is not evidence
about the Agda files.  Nothing here is a claim about measure theory: the
disintegration theorem is not proved, only the finite algebra the Agda
originals construct.
-/

namespace AgdaMirror.FibreAveraging

/-- Mirror of `Fibre2`. -/
inductive Fibre2
  | leftFibre | rightFibre
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `weight`. -/
def weight : Fibre2 → ℚ
  | .leftFibre => 1 / 2
  | .rightFibre => 1 / 2

/-- Mirror of `fibreMass`. -/
def fibreMass : ℚ := weight .leftFibre + weight .rightFibre

/-- Mirror of `fibreMassIsOne`. -/
theorem fibreMassIsOne : fibreMass = 1 := by norm_num [fibreMass, weight]

variable (Base : Type)

/-- Mirror of `FinePoint`. -/
abbrev FinePoint : Type := Base × Fibre2

/-- Mirror of `CoarseObservable`. -/
abbrev CoarseObservable : Type := Base → ℚ

/-- Mirror of `FineObservable`. -/
abbrev FineObservable : Type := FinePoint Base → ℚ

variable {Base}

/-- Mirror of `π`. -/
def proj (x : FinePoint Base) : Base := x.1

/-- Mirror of `pullback`. -/
def pullback (f : CoarseObservable Base) : FineObservable Base := fun x => f x.1

/-- Mirror of `average`: the within-fibre weighted mean. -/
def average (g : FineObservable Base) : CoarseObservable Base := fun y =>
  weight .leftFibre * g (y, .leftFibre) + weight .rightFibre * g (y, .rightFibre)

/-- Mirror of `P` (`coarseProjection` in the first module). -/
def P (g : FineObservable Base) : FineObservable Base := pullback (average g)

/-- Mirror of `Q` (`fineResidual` in the first module). -/
def Q (g : FineObservable Base) : FineObservable Base := fun x => g x - P g x

/-- Mirror of `coarseInnerAt`. -/
def coarseInnerAt (y : Base) (f g : CoarseObservable Base) : ℚ := f y * g y

/-- Mirror of `fineInnerAt`. -/
def fineInnerAt (y : Base) (f g : FineObservable Base) : ℚ :=
  weight .leftFibre * (f (y, .leftFibre) * g (y, .leftFibre)) +
    weight .rightFibre * (f (y, .rightFibre) * g (y, .rightFibre))

/-- Mirror of `averagePullback`: fibre averaging is a left inverse of pullback,
because the fibre mass is one. -/
theorem averagePullback (f : CoarseObservable Base) (y : Base) :
    average (pullback f) y = f y := by
  simp only [average, pullback, weight]; ring

/-- Mirror of `pullbackAverageAdjoint`. -/
theorem pullbackAverageAdjoint (y : Base) (f : CoarseObservable Base)
    (g : FineObservable Base) :
    fineInnerAt y (pullback f) g = coarseInnerAt y f (average g) := by
  simp only [fineInnerAt, coarseInnerAt, pullback, average, weight]; ring

/-- Mirror of `projectionIdempotent`. -/
theorem projectionIdempotent (g : FineObservable Base) (x : FinePoint Base) :
    P (P g) x = P g x := by
  obtain ⟨y, s⟩ := x
  cases s <;> · simp only [P, pullback, average, weight]; ring

/-- Mirror of `projectionSelfAdjoint`. -/
theorem projectionSelfAdjoint (y : Base) (f g : FineObservable Base) :
    fineInnerAt y (P f) g = fineInnerAt y f (P g) := by
  simp only [fineInnerAt, P, pullback, average, weight]; ring

/-- Mirror of `coarsePlusResidual`. -/
theorem coarsePlusResidual (g : FineObservable Base) (x : FinePoint Base) :
    P g x + Q g x = g x := by simp [Q]

/-- Mirror of `averageResidualIsZero`. -/
theorem averageResidualIsZero (y : Base) (g : FineObservable Base) :
    average (Q g) y = 0 := by
  simp only [average, Q, P, pullback, weight]; ring

/-- Mirror of `projectionKillsResidual`. -/
theorem projectionKillsResidual (g : FineObservable Base) (x : FinePoint Base) :
    P (Q g) x = 0 := by
  obtain ⟨y, s⟩ := x
  cases s <;> · simp only [P, Q, pullback, average, weight]; ring

/-- Mirror of `residualKillsProjection`. -/
theorem residualKillsProjection (g : FineObservable Base) (x : FinePoint Base) :
    Q (P g) x = 0 := by
  obtain ⟨y, s⟩ := x
  cases s <;> · simp only [P, Q, pullback, average, weight]; ring

/-- Mirror of `projectionResidualOrthogonal`. -/
theorem projectionResidualOrthogonal (y : Base) (g : FineObservable Base) :
    fineInnerAt y (P g) (Q g) = 0 := by
  simp only [fineInnerAt, P, Q, pullback, average, weight]; ring

/-- Mirror of `residualProjectionOrthogonal`. -/
theorem residualProjectionOrthogonal (y : Base) (g : FineObservable Base) :
    fineInnerAt y (Q g) (P g) = 0 := by
  simp only [fineInnerAt, P, Q, pullback, average, weight]; ring

/-- Mirror of `Decomposition`. -/
abbrev Decomposition (Base : Type) : Type := FineObservable Base × FineObservable Base

/-- Mirror of `decompose`. -/
def decompose (g : FineObservable Base) : Decomposition Base := (P g, Q g)

/-- Mirror of `glassesSwap`. -/
def glassesSwap (d : Decomposition Base) : Decomposition Base := (d.2, d.1)

/-- Mirror of `glassesSwapInvolutive`. -/
theorem glassesSwapInvolutive (d : Decomposition Base) :
    glassesSwap (glassesSwap d) = d := rfl

/-- Mirror of `glassesSwapExchangesCoarseResidual`. -/
theorem glassesSwapExchangesCoarseResidual (g : FineObservable Base) :
    glassesSwap (decompose g) = (Q g, P g) := rfl

/-- Mirror of `NormalizedFibreClaimScope`, whose `Bool` fields are each pinned
by a companion equation. -/
structure NormalizedFibreClaimScope where
  /-- The finite probability mass is constructed. -/
  finiteProbabilityMassConstructed : Bool
  /-- …and the field is pinned to `true`. -/
  finiteProbabilityMassConstructedIsTrue : finiteProbabilityMassConstructed = true
  /-- An arbitrary Rokhlin disintegration is not constructed. -/
  arbitraryRokhlinDisintegrationConstructed : Bool
  /-- …and the field is pinned to `false`. -/
  arbitraryRokhlinDisintegrationConstructedIsFalse :
    arbitraryRokhlinDisintegrationConstructed = false

/-- Mirror of `canonicalNormalizedFibreClaimScope`. -/
def canonicalNormalizedFibreClaimScope : NormalizedFibreClaimScope :=
  ⟨true, rfl, false, rfl⟩

end AgdaMirror.FibreAveraging
