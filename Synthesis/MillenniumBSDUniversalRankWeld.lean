import Synthesis.MillenniumBSDMathlibLFunctionWeld
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Data.Set.Basic
import Mathlib.GroupTheory.Torsion

/-!
# Universal BSD rank-weld proof surface

This module records the Clay-facing scope of the Birch--Swinnerton-Dyer rank
statement on the literal mathlib rational elliptic-curve carrier.

The two ranks are no longer arbitrary supplied natural numbers.

* The analytic rank is derived from analyticOrderNatAt of an entire nonzero
  continuation of the literal W.LSeries, with right-half-plane agreement.
  Finite order at s = 1 is then derived from global nonvanishing plus
  analyticity rather than supplied independently.
* The algebraic rank is derived from AddCommGroup.freeRank of the literal
  rational point group W.toAffine.Point, once Mordell--Weil finite generation
  is supplied.

The remaining universal equality is therefore the actual BSD rank conjecture,
not an adapter between unrelated observer values.
-/

namespace Synthesis.Millennium.BSD

open Set Filter WeierstrassCurve
open scoped Topology

abbrev RationalEllipticCurve :=
  { W : WeierstrassCurve ℚ // W.IsElliptic }

noncomputable def rationalEllipticCurveLSeries
    (E : RationalEllipticCurve) (s : ℂ) : ℂ :=
  E.1.LSeries s

structure BSDRankObservers where
  analyticRank : RationalEllipticCurve → ℕ
  algebraicRank : RationalEllipticCurve → ℕ

def BSDRankWeldOn
    (obs : BSDRankObservers)
    (S : Set RationalEllipticCurve) : Prop :=
  ∀ E, E ∈ S → obs.analyticRank E = obs.algebraicRank E

def UniversalBSDRankWeld
    (obs : BSDRankObservers) : Prop :=
  BSDRankWeldOn obs Set.univ

def BSDRankWeldAt
    (obs : BSDRankObservers)
    (E : RationalEllipticCurve) : Prop :=
  obs.analyticRank E = obs.algebraicRank E

theorem bsdRankWeldOn_mono
    (obs : BSDRankObservers)
    {S T : Set RationalEllipticCurve}
    (hST : S ⊆ T)
    (hT : BSDRankWeldOn obs T) :
    BSDRankWeldOn obs S := by
  intro E hE
  exact hT E (hST hE)

theorem bsdRankWeldOn_of_universal
    (obs : BSDRankObservers)
    (h : UniversalBSDRankWeld obs)
    (S : Set RationalEllipticCurve) :
    BSDRankWeldOn obs S :=
  bsdRankWeldOn_mono obs (Set.subset_univ S) h

theorem bsdRankWeldAt_of_universal
    (obs : BSDRankObservers)
    (h : UniversalBSDRankWeld obs)
    (E : RationalEllipticCurve) :
    BSDRankWeldAt obs E :=
  h E (Set.mem_univ E)

def BSDCurveFamilyCoversAll
    (S : Set RationalEllipticCurve) : Prop :=
  ∀ E : RationalEllipticCurve, E ∈ S

theorem universalBSDRankWeld_of_family
    (obs : BSDRankObservers)
    (S : Set RationalEllipticCurve)
    (hCover : BSDCurveFamilyCoversAll S)
    (hS : BSDRankWeldOn obs S) :
    UniversalBSDRankWeld obs := by
  intro E _
  exact hS E (hCover E)

/-! ## Canonical analytic-rank binding -/

structure BSDEllipticLContinuation (E : RationalEllipticCurve) where
  toFun : ℂ → ℂ
  rightHalfPlane : ℝ
  agreesLSeries :
    ∀ s, rightHalfPlane < s.re →
      toFun s = rationalEllipticCurveLSeries E s
  entire : ∀ s, AnalyticAt ℂ toFun s
  nonzero : toFun ≠ 0

instance (E : RationalEllipticCurve) :
    CoeFun (BSDEllipticLContinuation E) (fun _ => ℂ → ℂ) :=
  ⟨BSDEllipticLContinuation.toFun⟩

noncomputable def BSDEllipticLContinuation.analyticRank
    {E : RationalEllipticCurve}
    (L : BSDEllipticLContinuation E) : ℕ :=
  analyticOrderNatAt L.toFun (1 : ℂ)


/-- Entire nonzero continuations have finite order at s = 1.  Thus local
finiteness of analytic order is derived rather than supplied independently. -/
theorem BSDEllipticLContinuation.finiteOrderAtOne
    {E : RationalEllipticCurve}
    (L : BSDEllipticLContinuation E) :
    analyticOrderAt L.toFun (1 : ℂ) ≠ ⊤ := by
  intro htop
  have hz : L.toFun = 0 := by
    exact (analyticOrderAt_eq_top_iff_eq_zero (1 : ℂ) L.entire).mp htop
  exact L.nonzero hz

theorem BSDEllipticLContinuation.rank_factorization
    {E : RationalEllipticCurve}
    (L : BSDEllipticLContinuation E) :
    ∃ G : ℂ → ℂ,
      AnalyticAt ℂ G 1 ∧
      G 1 ≠ 0 ∧
      ∀ᶠ s in 𝓝 (1 : ℂ),
        L s = (s - 1) ^ L.analyticRank * G s := by
  simpa [BSDEllipticLContinuation.analyticRank, smul_eq_mul] using
    (L.entire 1).analyticOrderNatAt_eq_iff L.finiteOrderAtOne

theorem BSDEllipticLContinuation.ext_fun
    {E : RationalEllipticCurve}
    (L₁ L₂ : BSDEllipticLContinuation E) :
    L₁.toFun = L₂.toFun := by
  let c : ℝ := max L₁.rightHalfPlane L₂.rightHalfPlane + 1
  let z₀ : ℂ := (c : ℂ)
  have hz₀ : max L₁.rightHalfPlane L₂.rightHalfPlane < z₀.re := by
    dsimp [z₀, c]
    simp
  have hV :
      {z : ℂ | max L₁.rightHalfPlane L₂.rightHalfPlane < z.re} ∈ 𝓝 z₀ :=
    (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hz₀
  have hEq : L₁.toFun =ᶠ[𝓝 z₀] L₂.toFun := by
    filter_upwards [hV] with z hz
    rw [L₁.agreesLSeries z (lt_of_le_of_lt (le_max_left _ _) hz)]
    rw [L₂.agreesLSeries z (lt_of_le_of_lt (le_max_right _ _) hz)]
  have hA₁ : AnalyticOnNhd ℂ L₁.toFun Set.univ :=
    fun z _ => L₁.entire z
  have hA₂ : AnalyticOnNhd ℂ L₂.toFun Set.univ :=
    fun z _ => L₂.entire z
  exact hA₁.eq_of_eventuallyEq hA₂ hEq

theorem BSDEllipticLContinuation.analyticRank_eq
    {E : RationalEllipticCurve}
    (L₁ L₂ : BSDEllipticLContinuation E) :
    L₁.analyticRank = L₂.analyticRank := by
  unfold BSDEllipticLContinuation.analyticRank
  rw [L₁.ext_fun L₂]

structure BSDAnalyticRankBinding where
  continuation : ∀ E : RationalEllipticCurve, BSDEllipticLContinuation E

noncomputable def BSDAnalyticRankBinding.rank
    (a : BSDAnalyticRankBinding)
    (E : RationalEllipticCurve) : ℕ :=
  (a.continuation E).analyticRank

theorem BSDAnalyticRankBinding.rank_eq
    (a₁ a₂ : BSDAnalyticRankBinding) :
    a₁.rank = a₂.rank := by
  funext E
  exact (a₁.continuation E).analyticRank_eq (a₂.continuation E)

/-! ## Canonical Mordell--Weil-rank binding -/

structure BSDMordellWeilFiniteGeneration where
  fg :
    ∀ E : RationalEllipticCurve,
      letI : E.1.IsElliptic := E.2
      AddGroup.FG E.1.toAffine.Point

noncomputable def BSDMordellWeilFiniteGeneration.rank
    (m : BSDMordellWeilFiniteGeneration)
    (E : RationalEllipticCurve) : ℕ := by
  letI : E.1.IsElliptic := E.2
  letI : AddGroup.FG E.1.toAffine.Point := m.fg E
  exact AddCommGroup.freeRank E.1.toAffine.Point

abbrev BSDMordellWeilRankBinding :=
  BSDMordellWeilFiniteGeneration

/-- The algebraic rank is independent of the finite-generation proof witness:
both bindings compute the free rank of the same actual point group. -/
theorem BSDMordellWeilFiniteGeneration.rank_eq
    (m₁ m₂ : BSDMordellWeilFiniteGeneration) :
    m₁.rank = m₂.rank := by
  funext E
  simp only [BSDMordellWeilFiniteGeneration.rank]
  congr

/-! ## Bound observers and the genuine universal weld -/

structure BSDBoundRankObservers where
  analytic : BSDAnalyticRankBinding
  algebraic : BSDMordellWeilRankBinding

noncomputable def BSDBoundRankObservers.toRankObservers
    (b : BSDBoundRankObservers) :
    BSDRankObservers where
  analyticRank := b.analytic.rank
  algebraicRank := b.algebraic.rank

def UniversalBSDBoundRankWeld
    (b : BSDBoundRankObservers) : Prop :=
  UniversalBSDRankWeld b.toRankObservers

def UniversalBSDRankEqualityProducer
    (a : BSDAnalyticRankBinding)
    (m : BSDMordellWeilRankBinding) : Prop :=
  UniversalBSDBoundRankWeld
    { analytic := a, algebraic := m }


/-- The truth of the universal rank equality does not depend on which valid
same-object binding witnesses are chosen. -/
theorem universalBSDRankEqualityProducer_congr
    (a₁ a₂ : BSDAnalyticRankBinding)
    (m₁ m₂ : BSDMordellWeilRankBinding)
    (h : UniversalBSDRankEqualityProducer a₁ m₁) :
    UniversalBSDRankEqualityProducer a₂ m₂ := by
  intro E _
  have ha := congrFun (BSDAnalyticRankBinding.rank_eq a₁ a₂) E
  have hm := congrFun (BSDMordellWeilFiniteGeneration.rank_eq m₁ m₂) E
  exact ha.symm.trans ((h E (Set.mem_univ E)).trans hm)

def UniversalBSDAnalyticBindingProducer : Prop :=
  Nonempty BSDAnalyticRankBinding

/-- Literal universal analytic-continuation statement needed by the BSD rank
surface: every rational elliptic curve's literal Mathlib L-series has one
entire nonzero continuation agreeing on a right half-plane. -/
def UniversalEllipticLContinuationStatement : Prop :=
  ∀ E : RationalEllipticCurve, BSDEllipticLContinuation E

def bsdAnalyticRankBinding_of_universalContinuation
    (h : UniversalEllipticLContinuationStatement) :
    BSDAnalyticRankBinding :=
  ⟨h⟩

/-- As on the algebraic side, the analytic binding wrapper contains no extra
mathematical claim beyond universal existence of the literal continuation. -/
theorem universalBSDAnalyticBindingProducer_iff :
    UniversalBSDAnalyticBindingProducer ↔
      UniversalEllipticLContinuationStatement := by
  constructor
  · rintro ⟨a⟩
    exact a.continuation
  · intro h
    exact ⟨bsdAnalyticRankBinding_of_universalContinuation h⟩

def UniversalBSDMordellWeilBindingProducer : Prop :=
  Nonempty BSDMordellWeilRankBinding

/-! ## Exact Mordell--Weil import seam

The external Mordell--Weil formalization by Michael Stoll states its theorem on
the same Mathlib carrier used here: `WeierstrassCurve.Affine.Point` with
conclusion `AddGroup.FG`.  We therefore expose the literal universal theorem
shape separately from its one-field packaging.  This keeps future vendoring or
version-porting entirely outside the Clay core.
-/

/-- Literal universal Mordell--Weil finite-generation statement needed by this
file, with no DASHI-specific observer or rank wrapper. -/
def UniversalMordellWeilFiniteGenerationStatement : Prop :=
  ∀ E : RationalEllipticCurve,
    letI : E.1.IsElliptic := E.2
    AddGroup.FG E.1.toAffine.Point

/-- Package a theorem on the literal Mathlib point group into the BSD algebraic
background binding. -/
def bsdMordellWeilRankBinding_of_universalFiniteGeneration
    (h : UniversalMordellWeilFiniteGenerationStatement) :
    BSDMordellWeilRankBinding :=
  ⟨h⟩

/-- No mathematical content is hidden in the Mordell--Weil binding wrapper:
producing the wrapper is equivalent to proving finite generation of the actual
rational point group for every rational elliptic curve. -/
theorem universalBSDMordellWeilBindingProducer_iff :
    UniversalBSDMordellWeilBindingProducer ↔
      UniversalMordellWeilFiniteGenerationStatement := by
  constructor
  · rintro ⟨m⟩
    exact m.fg
  · intro h
    exact ⟨bsdMordellWeilRankBinding_of_universalFiniteGeneration h⟩

/-! ## Clay-facing background / novel-obligation split

The official BSD rank statement uses analytic continuation/modularity and
Mordell--Weil finite generation as established background mathematics.  For a
publishable Clay-facing proof these may be cited as known theorems; they are
not themselves the novel BSD equality.  A fully self-contained Lean
certification may later formalize them end-to-end.

This package makes that boundary explicit without weakening same-object
binding: both inputs still refer to the literal elliptic curve, literal
mathlib L-series continuation, and literal rational point group above.
-/

structure BSDEstablishedBackground where
  analytic : BSDAnalyticRankBinding
  algebraic : BSDMordellWeilRankBinding

def UniversalBSDEstablishedBackgroundProducer : Prop :=
  Nonempty BSDEstablishedBackground

/-- The established-background package is exactly the conjunction of the two
known universal theorem shapes.  In particular it introduces no third
mathematical premise between known background and the BSD rank equality. -/
theorem universalBSDEstablishedBackgroundProducer_iff :
    UniversalBSDEstablishedBackgroundProducer ↔
      UniversalEllipticLContinuationStatement ∧
        UniversalMordellWeilFiniteGenerationStatement := by
  constructor
  · rintro ⟨bg⟩
    exact ⟨bg.analytic.continuation, bg.algebraic.fg⟩
  · rintro ⟨hA, hM⟩
    exact ⟨
      { analytic := bsdAnalyticRankBinding_of_universalContinuation hA
        algebraic :=
          bsdMordellWeilRankBinding_of_universalFiniteGeneration hM }⟩

def BSDEstablishedBackground.toBoundRankObservers
    (bg : BSDEstablishedBackground) : BSDBoundRankObservers where
  analytic := bg.analytic
  algebraic := bg.algebraic

/-- The sole novel Clay-facing BSD obligation once established background is
bound: equality of the canonical analytic and Mordell--Weil ranks for every
rational elliptic curve over Q. -/
def BSDClayCoreObligation
    (bg : BSDEstablishedBackground) : Prop :=
  UniversalBSDRankEqualityProducer bg.analytic bg.algebraic

/-- The core obligation is independent of the particular witnesses used to
package the established analytic-continuation and finite-generation facts. -/
theorem bsdClayCoreObligation_congr
    (bg₁ bg₂ : BSDEstablishedBackground)
    (h : BSDClayCoreObligation bg₁) :
    BSDClayCoreObligation bg₂ :=
  universalBSDRankEqualityProducer_congr
    bg₁.analytic bg₂.analytic bg₁.algebraic bg₂.algebraic h

structure UniversalBSDRankProof where
  bound : BSDBoundRankObservers
  rankWeld : UniversalBSDBoundRankWeld bound

def UniversalBSDRankTheorem : Prop :=
  Nonempty UniversalBSDRankProof

/-- Package one chosen pair of valid same-object bindings and the universal
rank equality on that pair. -/
theorem universalBSDRankTheorem_of_bound
    (a : BSDAnalyticRankBinding)
    (m : BSDMordellWeilRankBinding)
    (hRank : UniversalBSDRankEqualityProducer a m) :
    UniversalBSDRankTheorem :=
  ⟨
    { bound := { analytic := a, algebraic := m }
      rankWeld := hRank }⟩

/-- Compile the paper-facing split directly: established background plus the
single novel rank-equality obligation yields the packaged universal theorem. -/
theorem universalBSDRankTheorem_of_background
    (bg : BSDEstablishedBackground)
    (hRank : BSDClayCoreObligation bg) :
    UniversalBSDRankTheorem :=
  universalBSDRankTheorem_of_bound bg.analytic bg.algebraic hRank

/-- Existence-shaped max-cut: it is enough to construct one valid analytic
binding, one valid Mordell--Weil binding, and prove BSD rank equality on
those same objects. -/
theorem universalBSDRankTheorem_of_producers
    (h :
      ∃ (a : BSDAnalyticRankBinding)
        (m : BSDMordellWeilRankBinding),
        UniversalBSDRankEqualityProducer a m) :
    UniversalBSDRankTheorem := by
  rcases h with ⟨a, m, hRank⟩
  exact universalBSDRankTheorem_of_bound a m hRank

/-- The older split producer view compiles to the existence-shaped theorem
when the rank theorem is supplied uniformly; retained as a convenience. -/
theorem universalBSDRankTheorem_of_uniform_producers
    (hA : UniversalBSDAnalyticBindingProducer)
    (hM : UniversalBSDMordellWeilBindingProducer)
    (hRank :
      ∀ (a : BSDAnalyticRankBinding)
        (m : BSDMordellWeilRankBinding),
        UniversalBSDRankEqualityProducer a m) :
    UniversalBSDRankTheorem := by
  rcases hA with ⟨a⟩
  rcases hM with ⟨m⟩
  exact universalBSDRankTheorem_of_bound a m (hRank a m)

/-! ## Same-object CM specialization and scope guard -/

noncomputable def cmRationalEllipticCurve :
    RationalEllipticCurve :=
  ⟨cmWeierstrass, inferInstance⟩

theorem cmRationalEllipticCurve_LSeries_sameObject
    (s : ℂ) :
    rationalEllipticCurveLSeries cmRationalEllipticCurve s =
      cmLSeries s := by
  rfl

def CMBSDRankWeld (obs : BSDRankObservers) : Prop :=
  BSDRankWeldAt obs cmRationalEllipticCurve

theorem cmBSDRankWeld_of_universal
    (obs : BSDRankObservers)
    (h : UniversalBSDRankWeld obs) :
    CMBSDRankWeld obs :=
  bsdRankWeldAt_of_universal obs h cmRationalEllipticCurve

theorem cmBSDBoundRankWeld_of_universalProof
    (h : UniversalBSDRankTheorem) :
    ∃ b : BSDBoundRankObservers,
      CMBSDRankWeld b.toRankObservers := by
  rcases h with ⟨p⟩
  exact ⟨p.bound,
    cmBSDRankWeld_of_universal
      p.bound.toRankObservers p.rankWeld⟩

theorem universalBSDRankWeld_of_cm_and_coverage
    (obs : BSDRankObservers)
    (hCM : CMBSDRankWeld obs)
    (hCover : ∀ E : RationalEllipticCurve,
      E = cmRationalEllipticCurve) :
    UniversalBSDRankWeld obs := by
  intro E _
  rw [hCover E]
  exact hCM

/-! ## Refined BSD proof surface -/

structure BSDRefinedObservers where
  rank : BSDRankObservers
  shaFinite : RationalEllipticCurve → Prop
  leadingCoefficientIdentity : RationalEllipticCurve → Prop

def UniversalBSDRefinedWeld
    (obs : BSDRefinedObservers) : Prop :=
  UniversalBSDRankWeld obs.rank ∧
    (∀ E, obs.shaFinite E) ∧
    (∀ E, obs.leadingCoefficientIdentity E)

theorem universalBSDRankWeld_of_refined
    (obs : BSDRefinedObservers)
    (h : UniversalBSDRefinedWeld obs) :
    UniversalBSDRankWeld obs.rank :=
  h.1

structure BSDUniversalMaxCutStatus where
  rationalEllipticCurveCarrierPaid : Bool
  mathlibLSeriesCarrierPaid : Bool
  analyticOrderCarrierPaid : Bool
  finiteAnalyticOrderDerivedPaid : Bool
  continuationNonzeroFromLiteralLSeriesPaid : Bool
  analyticContinuationUniquenessPaid : Bool
  analyticRankWitnessIndependencePaid : Bool
  mordellWeilFreeRankCarrierPaid : Bool
  scopeRestrictionCompilerPaid : Bool
  familyCoverageCompilerPaid : Bool
  cmCurveSameObjectPaid : Bool
  universalAnalyticBindingPaid : Bool
  universalMordellWeilFiniteGenerationPaid : Bool
  universalRankWeldPaid : Bool
  universalShaFinitenessPaid : Bool
  universalLeadingCoefficientPaid : Bool
  deriving DecidableEq, Repr

def bsdUniversalMaxCutStatus : BSDUniversalMaxCutStatus :=
  ⟨true, true, true, true, false, true, true, true, true, true, true,
    false, false, false, false, false⟩

/-! ## Canonical Clay / certification / refined dashboards

`BSDUniversalMaxCutStatus` above is retained for compatibility with existing
receipts.  The three records below are the preferred reporting surface: they
prevent known-theorem certification work and refined BSD from being presented
as blockers for the official rank conjecture.
-/

structure BSDClayCoreStatus where
  literalRationalEllipticCurvePaid : Bool
  literalHasseWeilLSeriesPaid : Bool
  canonicalAnalyticOrderPaid : Bool
  canonicalMordellWeilFreeRankPaid : Bool
  establishedBackgroundBoundaryPaid : Bool
  universalRankEqualityPaid : Bool
  deriving DecidableEq, Repr

/-- Clay-facing max-cut: every representation/boundary item is paid; the
universal rank equality itself remains open. -/
def bsdClayCoreStatus : BSDClayCoreStatus :=
  ⟨true, true, true, true, true, false⟩

structure BSDLeanCertificationStatus where
  universalAnalyticContinuationFormalized : Bool
  universalMordellWeilFiniteGenerationFormalized : Bool
  exactHeadKernelReceipt : Bool
  deriving DecidableEq, Repr

/-- Optional end-to-end formal certification programme.  These are deliberately
not fields of `BSDClayCoreStatus`. -/
def bsdLeanCertificationStatus : BSDLeanCertificationStatus :=
  ⟨false, false, false⟩

/-! The current external Mordell--Weil implementation is a valuable
certification input, but it is not yet a dependency of this project.  At the
time this boundary was written, DASHI is pinned to Lean/mathlib 4.28 while the
checked external theorem repository is pinned to 4.34.  The theorem statement
itself is carrier-compatible; source/version compatibility and an exact-head
DASHI build remain to be established before the certification flag above can
be changed. -/
structure BSDMordellWeilExternalBridgeStatus where
  externalUniversalTheoremExists : Bool
  sameMathlibPointCarrier : Bool
  exactStatementImportSeamPaid : Bool
  leanMathlibVersionCompatible : Bool
  vendoredOrDependencyWired : Bool
  deriving DecidableEq, Repr

def bsdMordellWeilExternalBridgeStatus :
    BSDMordellWeilExternalBridgeStatus :=
  ⟨true, true, true, false, false⟩

structure BSDRefinedExtensionStatus where
  canonicalShaCarrierPaid : Bool
  shaFinitenessPaid : Bool
  periodRegulatorTamagawaPaid : Bool
  leadingCoefficientIdentityPaid : Bool
  deriving DecidableEq, Repr

/-- Refined BSD extension: useful mathematics, explicitly off the critical path
for the official Millennium rank statement. -/
def bsdRefinedExtensionStatus : BSDRefinedExtensionStatus :=
  ⟨true, false, false, false⟩

end Synthesis.Millennium.BSD
