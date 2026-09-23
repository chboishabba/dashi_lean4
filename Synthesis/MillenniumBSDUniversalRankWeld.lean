import Synthesis.MillenniumBSDMathlibLFunctionWeld
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Data.Set.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.GroupTheory.Torsion

/-!
# Universal BSD rank-weld proof surface

This module records the Clay-facing scope of the Birch--Swinnerton-Dyer rank
statement without pretending that a special CM calculation is universal.

The curve carrier is the literal mathlib Weierstrass-curve object over Q,
restricted by the actual IsElliptic typeclass. Mathlib already provides the
formal Euler-product L-series W.LSeries, but it does not currently expose
canonical definitions of either the analytic order of vanishing of the
continued elliptic L-function at s = 1 or the Mordell--Weil rank of W(Q).

Accordingly those two natural-number observers remain explicit parameters.
Binding them to canonical same-object definitions is a separate interface;
the Clay-facing theorem is the universal equality after that binding.

The scope API is intentional:
* a universal weld restricts to every family and every individual curve;
* a family weld becomes universal only from an explicit coverage theorem;
* the existing CM curve y^2 = x^3 - x is one literal member of the same
  universal carrier.

Thus special-curve progress cannot silently discharge the universal owner.
-/

namespace Synthesis.Millennium.BSD

open Set WeierstrassCurve

/-- Literal rational elliptic curves on the same mathlib carrier used by the
existing CM L-function development. -/
abbrev RationalEllipticCurve :=
  { W : WeierstrassCurve ℚ // W.IsElliptic }

/-- The actual mathlib L-series attached to a rational elliptic curve.
No analytic continuation or order-of-vanishing claim is made here. -/
noncomputable def rationalEllipticCurveLSeries
    (E : RationalEllipticCurve) (s : ℂ) : ℂ :=
  E.1.LSeries s

/-- Explicit rank-observer surface. These are deliberately parameters until
canonical analytic-rank and Mordell--Weil-rank objects are available and
same-object welded to this exact curve carrier. -/
structure BSDRankObservers where
  analyticRank : RationalEllipticCurve → ℕ
  algebraicRank : RationalEllipticCurve → ℕ


/-- A holomorphic function has a zero of exact order r at s = 1 when it
locally factors as (s - 1)^r times a holomorphic nonvanishing factor. -/
def HasZeroOfOrderAtOne
    (F : ℂ → ℂ) (r : ℕ) : Prop :=
  ∃ G : ℂ → ℂ,
    AnalyticAt ℂ G 1 ∧
    G 1 ≠ 0 ∧
    ∀ᶠ s in 𝓝 (1 : ℂ),
      F s = (s - 1) ^ r * G s

/-- Same-object analytic-rank binding. The continuation must agree with the
literal mathlib elliptic L-series on some right half-plane, be holomorphic
everywhere, and have the declared exact order at s = 1. -/
structure BSDAnalyticRankBinding where
  continuation : RationalEllipticCurve → ℂ → ℂ
  rightHalfPlane : RationalEllipticCurve → ℝ
  agreesLSeries :
    ∀ E s,
      rightHalfPlane E < s.re →
      continuation E s = rationalEllipticCurveLSeries E s
  entire :
    ∀ E s, AnalyticAt ℂ (continuation E) s
  rank : RationalEllipticCurve → ℕ
  rank_is_order :
    ∀ E, HasZeroOfOrderAtOne (continuation E) (rank E)

/-- Canonical algebraic-rank specification on the actual mathlib rational
point group: modulo torsion, E(Q) is free abelian on exactly r generators. -/
def IsMordellWeilRank
    (E : RationalEllipticCurve) (r : ℕ) : Prop :=
  letI : E.1.IsElliptic := E.2
  Nonempty
    ((E.1.toAffine.Point ⧸
        AddCommGroup.torsion E.1.toAffine.Point) ≃+
      (Fin r → ℤ))

/-- Same-object algebraic-rank binding for every rational elliptic curve. -/
structure BSDMordellWeilRankBinding where
  rank : RationalEllipticCurve → ℕ
  rank_spec : ∀ E, IsMordellWeilRank E (rank E)

/-- Both canonical rank observers, tied to the literal L-series and literal
rational point group. -/
structure BSDBoundRankObservers where
  analytic : BSDAnalyticRankBinding
  algebraic : BSDMordellWeilRankBinding

/-- Forget only the binding certificates, retaining the ranks themselves. -/
def BSDBoundRankObservers.toRankObservers
    (b : BSDBoundRankObservers) :
    BSDRankObservers where
  analyticRank := b.analytic.rank
  algebraicRank := b.algebraic.rank

/-- Clay-facing universal rank equality after both observers have been bound
to their actual same-curve objects. -/
def UniversalBSDBoundRankWeld
    (b : BSDBoundRankObservers) : Prop :=
  UniversalBSDRankWeld b.toRankObservers


/-- Prize-facing rank-theorem package: canonical same-object rank bindings
for every rational elliptic curve together with the universal equality. -/
structure UniversalBSDRankProof where
  bound : BSDBoundRankObservers
  rankWeld : UniversalBSDBoundRankWeld bound

/-- The actual universal rank theorem as a proposition. -/
def UniversalBSDRankTheorem : Prop :=
  Nonempty UniversalBSDRankProof

/-- A universal proof yields the rank equality for any literal selected curve,
including the repo's CM example. -/
theorem BSDRankWeldAt.of_universalProof
    (h : UniversalBSDRankTheorem)
    (E : RationalEllipticCurve) :
    ∃ b : BSDBoundRankObservers,
      BSDRankWeldAt b.toRankObservers E := by
  rcases h with ⟨p⟩
  exact ⟨p.bound,
    bsdRankWeldAt_of_universal
      p.bound.toRankObservers p.rankWeld E⟩

/-- BSD rank equality restricted to a specified family of rational elliptic
curves. -/
def BSDRankWeldOn
    (obs : BSDRankObservers)
    (S : Set RationalEllipticCurve) : Prop :=
  ∀ E, E ∈ S → obs.analyticRank E = obs.algebraicRank E

/-- The Clay-facing rank statement: the same rank equality for every rational
elliptic curve. -/
def UniversalBSDRankWeld
    (obs : BSDRankObservers) : Prop :=
  BSDRankWeldOn obs Set.univ

/-- Rank equality for one literal rational elliptic curve. -/
def BSDRankWeldAt
    (obs : BSDRankObservers)
    (E : RationalEllipticCurve) : Prop :=
  obs.analyticRank E = obs.algebraicRank E

/-- Scope restriction: a theorem on a larger family automatically applies to
every subfamily. -/
theorem bsdRankWeldOn_mono
    (obs : BSDRankObservers)
    {S T : Set RationalEllipticCurve}
    (hST : S ⊆ T)
    (hT : BSDRankWeldOn obs T) :
    BSDRankWeldOn obs S := by
  intro E hE
  exact hT E (hST hE)

/-- Universal BSD rank equality specializes to every chosen family. -/
theorem bsdRankWeldOn_of_universal
    (obs : BSDRankObservers)
    (h : UniversalBSDRankWeld obs)
    (S : Set RationalEllipticCurve) :
    BSDRankWeldOn obs S :=
  bsdRankWeldOn_mono obs (Set.subset_univ S) h

/-- Universal BSD rank equality specializes to every individual curve. -/
theorem bsdRankWeldAt_of_universal
    (obs : BSDRankObservers)
    (h : UniversalBSDRankWeld obs)
    (E : RationalEllipticCurve) :
    BSDRankWeldAt obs E :=
  h E (Set.mem_univ E)

/-- Exact condition required to promote a family theorem to the universal
Clay scope: the family must cover every rational elliptic curve. -/
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

/-- The literal CM curve already developed throughout the repo is one member
of the universal rational-elliptic-curve carrier. -/
noncomputable def cmRationalEllipticCurve :
    RationalEllipticCurve :=
  ⟨cmWeierstrass, inferInstance⟩

/-- Its universal-carrier L-series is definitionally the existing literal
mathlib CM L-series. -/
theorem cmRationalEllipticCurve_LSeries_sameObject
    (s : ℂ) :
    rationalEllipticCurveLSeries cmRationalEllipticCurve s =
      cmLSeries s := by
  rfl

/-- CM-curve rank equality, explicitly only a one-curve specialization. -/
def CMBSDRankWeld (obs : BSDRankObservers) : Prop :=
  BSDRankWeldAt obs cmRationalEllipticCurve

/-- The universal Clay statement implies the CM-curve statement. -/
theorem cmBSDRankWeld_of_universal
    (obs : BSDRankObservers)
    (h : UniversalBSDRankWeld obs) :
    CMBSDRankWeld obs :=
  bsdRankWeldAt_of_universal obs h cmRationalEllipticCurve


/-- Prize-facing universal package specializes to a canonically bound
CM-curve rank equality. -/
theorem cmBSDBoundRankWeld_of_universalProof
    (h : UniversalBSDRankTheorem) :
    ∃ b : BSDBoundRankObservers,
      CMBSDRankWeld b.toRankObservers := by
  rcases h with ⟨p⟩
  exact ⟨p.bound,
    cmBSDRankWeld_of_universal
      p.bound.toRankObservers p.rankWeld⟩

/-- Conversely, a CM-only theorem can produce the universal theorem only if
one separately proves that every rational elliptic curve is that CM curve.
This makes the missing coverage step explicit rather than silently
generalising a special case. -/
theorem universalBSDRankWeld_of_cm_and_coverage
    (obs : BSDRankObservers)
    (hCM : CMBSDRankWeld obs)
    (hCover : ∀ E : RationalEllipticCurve,
      E = cmRationalEllipticCurve) :
    UniversalBSDRankWeld obs := by
  intro E _
  rw [hCover E]
  exact hCM

/-- Refined BSD adds genuinely stronger universal obligations on top of the
rank weld. Their mathematical content is left explicit rather than hidden in
the CM descent machinery. -/
structure BSDRefinedObservers where
  rank : BSDRankObservers
  shaFinite : RationalEllipticCurve → Prop
  leadingCoefficientIdentity : RationalEllipticCurve → Prop

/-- Universal refined-BSD proof surface. -/
def UniversalBSDRefinedWeld
    (obs : BSDRefinedObservers) : Prop :=
  UniversalBSDRankWeld obs.rank ∧
    (∀ E, obs.shaFinite E) ∧
    (∀ E, obs.leadingCoefficientIdentity E)

/-- Refined BSD always contains the universal rank statement. -/
theorem universalBSDRankWeld_of_refined
    (obs : BSDRefinedObservers)
    (h : UniversalBSDRefinedWeld obs) :
    UniversalBSDRankWeld obs.rank :=
  h.1

/-- Machine-readable max-cut ledger. Concrete mathlib curve/L-series
carriers are paid; canonical rank bindings and the universal rank equality
remain open. The CM curve is explicitly not a universal coverage theorem. -/
structure BSDUniversalMaxCutStatus where
  rationalEllipticCurveCarrierPaid : Bool
  mathlibLSeriesCarrierPaid : Bool
  analyticRankSpecificationPaid : Bool
  mordellWeilRankSpecificationPaid : Bool
  boundObserverCompilerPaid : Bool
  cmCurveSameObjectPaid : Bool
  scopeRestrictionCompilerPaid : Bool
  familyCoverageCompilerPaid : Bool
  canonicalAnalyticRankBindingPaid : Bool
  canonicalMordellWeilRankBindingPaid : Bool
  universalRankWeldPaid : Bool
  universalShaFinitenessPaid : Bool
  universalLeadingCoefficientPaid : Bool
  deriving DecidableEq, Repr

def bsdUniversalMaxCutStatus : BSDUniversalMaxCutStatus :=
  ⟨true, true, true, true, true,
    true, true, true,
    false, false, false, false, false⟩

end Synthesis.Millennium.BSD
