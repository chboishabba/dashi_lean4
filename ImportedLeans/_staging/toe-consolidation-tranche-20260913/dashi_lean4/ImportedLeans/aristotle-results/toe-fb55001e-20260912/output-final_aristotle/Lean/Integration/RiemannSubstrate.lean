import Integration.Levels
import Integration.RiemannStrip

/-!
# The analytic substrate as a socket, not a subject

`DASHI.Analysis.RiemannAnalyticSubstrate` declares a four-layer tower of
records — a complex analytic carrier, a Gamma/Mellin layer, a zeta half-plane
layer and a completed-zeta layer — and then defines

```agda
RiemannHypothesisFor : AnalyticSubstrate → Set
```

as a predicate on an inhabitant of the tower.  Every mathematical notion in the
tower (`Complex`, `Holomorphic`, `nontrivialZero`, `criticalLine`, …) is an
*abstract field*: a `Set` with no defining equation.  The Agda bundle contains
no inhabitant of `AnalyticSubstrate`, and neither does this Lean corpus.

This module mirrors the tower faithfully (fields as `Type`, exactly as the Agda
`Set`s) and proves the resulting classification:

* `analyticSubstrate` exists — the tower is not empty, so nothing is proved by
  exhibiting an inhabitant;
* `rh_true_substrate` and `rh_false_substrate` — there are inhabitants of the
  tower for which `RiemannHypothesisFor` holds and inhabitants for which it
  fails, so **the record tower places no constraint whatsoever on the
  predicate**;
* `substrate_does_not_constrain_rh` bundles the two.

Therefore the correct entry for this tower in the global map is a *socket*: a
typed interface awaiting an analytic implementation, not evidence about the
Riemann hypothesis.  Nothing here says anything about the actual Riemann zeta
function; the identifiers below are mirror names for abstract fields.
-/

namespace Integration.RiemannSubstrate

open Integration.Levels

/-! ## 1. The mirrored tower -/

/-- Mirror of `RiemannAnalyticSubstrate.ComplexAnalyticCarrier`. -/
structure ComplexAnalyticCarrier : Type 1 where
  Complex : Type
  Real : Type
  zeroC : Complex
  oneC : Complex
  addC : Complex → Complex → Complex
  mulC : Complex → Complex → Complex
  negC : Complex → Complex
  conjC : Complex → Complex
  realPart : Complex → Real
  imaginaryPart : Complex → Real
  Function : Type
  apply : Function → Complex → Complex
  Holomorphic : Function → Type
  Entire : Function → Type
  Meromorphic : Function → Type
  SimplePoleAt : Function → Complex → Type

/-- Mirror of `GammaMellinLayer`. -/
structure GammaMellinLayer (C : ComplexAnalyticCarrier) : Type 1 where
  Test : Type
  MellinDomain : Test → Type
  MellinInversionLaw : Test → Type
  gamma : C.Function
  mellin : Test → C.Function
  gammaMeromorphic : C.Meromorphic gamma
  mellinHolomorphicOnDomain : ∀ f, MellinDomain f → C.Holomorphic (mellin f)
  mellinInversion : ∀ f, MellinDomain f → MellinInversionLaw f

/-- Mirror of `ZetaHalfPlaneLayer`. -/
structure ZetaHalfPlaneLayer (C : ComplexAnalyticCarrier) : Type 1 where
  zetaHalfPlane : C.Function
  realPartGreaterThanOne : C.Complex → Type
  DirichletSeriesConverges : C.Complex → Type
  ZetaEqualsDirichletSeries : C.Complex → Type
  EulerProductConverges : C.Complex → Type
  ZetaEqualsEulerProduct : C.Complex → Type
  dirichletSeriesConverges : ∀ s, realPartGreaterThanOne s → DirichletSeriesConverges s
  zetaEqualsDirichletSeries : ∀ s, realPartGreaterThanOne s → ZetaEqualsDirichletSeries s
  eulerProductConverges : ∀ s, realPartGreaterThanOne s → EulerProductConverges s
  zetaEqualsEulerProduct : ∀ s, realPartGreaterThanOne s → ZetaEqualsEulerProduct s

/-- Mirror of `CompletedRiemannZeta`. -/
structure CompletedRiemannZeta (C : ComplexAnalyticCarrier)
    (_G : GammaMellinLayer C) (H : ZetaHalfPlaneLayer C) : Type 1 where
  zeta : C.Function
  xi : C.Function
  oneMinus : C.Complex → C.Complex
  isZero : C.Function → C.Complex → Type
  nontrivialZero : C.Complex → Type
  criticalLine : C.Complex → Type
  agreesWithHalfPlane : ∀ s, H.realPartGreaterThanOne s →
    C.apply zeta s = C.apply H.zetaHalfPlane s
  CompletedDefinition : C.Complex → Type
  zetaMeromorphic : C.Meromorphic zeta
  simplePoleAtOne : C.SimplePoleAt zeta C.oneC
  xiEntire : C.Entire xi
  completedDefinition : ∀ s, CompletedDefinition s
  functionalEquation : ∀ s, C.apply xi s = C.apply xi (oneMinus s)
  conjugationLaw : ∀ s, C.apply xi (C.conjC s) = C.conjC (C.apply xi s)
  nontrivialZeroIsZetaZero : ∀ s, nontrivialZero s → isZero zeta s
  nontrivialZeroIsXiZero : ∀ s, nontrivialZero s → isZero xi s
  xiZeroIsNontrivialZetaZero : ∀ s, isZero xi s → nontrivialZero s

/-- Mirror of `AnalyticSubstrate`. -/
structure AnalyticSubstrate : Type 1 where
  carrier : ComplexAnalyticCarrier
  gammaMellin : GammaMellinLayer carrier
  halfPlane : ZetaHalfPlaneLayer carrier
  completed : CompletedRiemannZeta carrier gammaMellin halfPlane

/-- Mirror of `RiemannHypothesisFor`. -/
def RiemannHypothesisFor (A : AnalyticSubstrate) : Type :=
  ∀ s : A.carrier.Complex, A.completed.nontrivialZero s → A.completed.criticalLine s

/-! ## 2. The tower constrains nothing

Both inhabitants below use the one-point carrier, for which every equational
field is `rfl`.  They differ only in the two *abstract predicate* fields
`nontrivialZero` and `criticalLine`, which the source leaves entirely free. -/

/-- The one-point analytic carrier: every field is forced, every equation is
`rfl`. -/
def trivialCarrier : ComplexAnalyticCarrier where
  Complex := Unit
  Real := Unit
  zeroC := ()
  oneC := ()
  addC _ _ := ()
  mulC _ _ := ()
  negC _ := ()
  conjC _ := ()
  realPart _ := ()
  imaginaryPart _ := ()
  Function := Unit
  apply _ _ := ()
  Holomorphic _ := PUnit
  Entire _ := PUnit
  Meromorphic _ := PUnit
  SimplePoleAt _ _ := PUnit

/-- The Gamma/Mellin layer over the one-point carrier. -/
def trivialGammaMellin : GammaMellinLayer trivialCarrier where
  Test := Unit
  MellinDomain _ := PUnit
  MellinInversionLaw _ := PUnit
  gamma := ()
  mellin _ := ()
  gammaMeromorphic := PUnit.unit
  mellinHolomorphicOnDomain _ _ := PUnit.unit
  mellinInversion _ _ := PUnit.unit

/-- The half-plane layer over the one-point carrier. -/
def trivialHalfPlane : ZetaHalfPlaneLayer trivialCarrier where
  zetaHalfPlane := ()
  realPartGreaterThanOne _ := PUnit
  DirichletSeriesConverges _ := PUnit
  ZetaEqualsDirichletSeries _ := PUnit
  EulerProductConverges _ := PUnit
  ZetaEqualsEulerProduct _ := PUnit
  dirichletSeriesConverges _ _ := PUnit.unit
  zetaEqualsDirichletSeries _ _ := PUnit.unit
  eulerProductConverges _ _ := PUnit.unit
  zetaEqualsEulerProduct _ _ := PUnit.unit

/-- The completed layer over the one-point carrier, parameterised by the one
field the source leaves entirely free: the critical-line predicate.  Every other
field is forced or `rfl`; in particular the three zero-linking fields hold
because `isZero` is inhabited. -/
def trivialCompleted (cl : Unit → Type) :
    CompletedRiemannZeta trivialCarrier trivialGammaMellin trivialHalfPlane where
  zeta := ()
  xi := ()
  oneMinus _ := ()
  isZero _ _ := PUnit
  nontrivialZero _ := PUnit
  criticalLine := cl
  agreesWithHalfPlane _ _ := rfl
  CompletedDefinition _ := PUnit
  zetaMeromorphic := PUnit.unit
  simplePoleAtOne := PUnit.unit
  xiEntire := PUnit.unit
  completedDefinition _ := PUnit.unit
  functionalEquation _ := rfl
  conjugationLaw _ := rfl
  nontrivialZeroIsZetaZero _ _ := PUnit.unit
  nontrivialZeroIsXiZero _ _ := PUnit.unit
  xiZeroIsNontrivialZetaZero _ _ := PUnit.unit

/-- The tower, over the one-point carrier, with a chosen critical-line
predicate. -/
def substrateWith (cl : Unit → Type) : AnalyticSubstrate where
  carrier := trivialCarrier
  gammaMellin := trivialGammaMellin
  halfPlane := trivialHalfPlane
  completed := trivialCompleted cl

/-- An inhabitant of the tower: the record is not empty, so exhibiting an
inhabitant proves nothing. -/
def analyticSubstrate : AnalyticSubstrate := substrateWith (fun _ => PUnit)

/-- **Socket, positive side.**  There is an inhabitant of the tower satisfying
`RiemannHypothesisFor`. -/
theorem rh_true_substrate : ∃ A : AnalyticSubstrate, Nonempty (RiemannHypothesisFor A) :=
  ⟨analyticSubstrate, ⟨fun _ _ => PUnit.unit⟩⟩

/-- **Socket, negative side.**  There is an inhabitant of the tower for which
`RiemannHypothesisFor` is *uninhabited*: every point is a nontrivial zero and
the critical line is empty.  Every field of every layer is still satisfied,
because no field of the tower relates `criticalLine` to anything else. -/
theorem rh_false_substrate : ∃ A : AnalyticSubstrate, ¬ Nonempty (RiemannHypothesisFor A) := by
  refine ⟨substrateWith (fun _ => Empty), ?_⟩
  rintro ⟨h⟩
  exact (h () PUnit.unit).elim

/-- **The classification.**  The substrate tower is a socket: it is inhabited,
and both truth values of `RiemannHypothesisFor` occur among its inhabitants, so
possessing an inhabitant is evidence for nothing about the predicate. -/
theorem substrate_does_not_constrain_rh :
    (∃ A : AnalyticSubstrate, Nonempty (RiemannHypothesisFor A)) ∧
    (∃ A : AnalyticSubstrate, ¬ Nonempty (RiemannHypothesisFor A)) :=
  ⟨rh_true_substrate, rh_false_substrate⟩

end Integration.RiemannSubstrate
