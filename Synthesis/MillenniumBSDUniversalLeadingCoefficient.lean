import Synthesis.MillenniumBSDUniversalRankWeld
import Mathlib.NumberTheory.Height.EllipticCurve
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Universal refined BSD proof surface

This module separates the refined BSD formula into objects that are already
canonically attached to the literal curve and objects whose universal
same-object carrier is not yet available in mathlib/repo infrastructure.

Already canonical here:
* the normalized leading Taylor coefficient of the bound continuation;
* the order of the actual rational torsion subgroup.

Still explicit bindings:
* period;
* regulator;
* Tamagawa product.

Still missing at the object level:
* a universal classical Tate--Shafarevich group attached to an arbitrary
  rational elliptic curve.  We therefore do not invent an arbitrary Sha order.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve

/-- The normalized leading Taylor coefficient at s = 1 for the actual bound
continuation, using its canonically derived analytic rank. -/
noncomputable def BSDEllipticLContinuation.normalizedLeadingCoefficient
    {E : RationalEllipticCurve}
    (L : BSDEllipticLContinuation E) : ℂ :=
  iteratedDeriv L.analyticRank L.toFun (1 : ℂ) /
    (L.analyticRank.factorial : ℂ)

/-- The normalized leading coefficient is independent of the continuation
witness because the entire continuation itself is unique. -/
theorem BSDEllipticLContinuation.normalizedLeadingCoefficient_eq
    {E : RationalEllipticCurve}
    (L₁ L₂ : BSDEllipticLContinuation E) :
    L₁.normalizedLeadingCoefficient =
      L₂.normalizedLeadingCoefficient := by
  have hfun := L₁.ext_fun L₂
  have hrank := L₁.analyticRank_eq L₂
  simp [BSDEllipticLContinuation.normalizedLeadingCoefficient,
    hfun, hrank]

/-- The actual rational torsion subgroup is finite for every rational elliptic
curve by mathlib's height/Northcott theorem. -/
theorem rationalEllipticCurve_torsion_finite
    (E : RationalEllipticCurve) :
    letI : E.1.IsElliptic := E.2
    Finite (AddCommGroup.torsion E.1.toAffine.Point) := by
  letI : E.1.IsElliptic := E.2
  exact WeierstrassCurve.Affine.finite_torsion (W := E.1)

/-- Canonical torsion order of the actual rational point group. -/
noncomputable def rationalEllipticCurveTorsionOrder
    (E : RationalEllipticCurve) : ℕ := by
  letI : E.1.IsElliptic := E.2
  letI : Finite (AddCommGroup.torsion E.1.toAffine.Point) :=
    rationalEllipticCurve_torsion_finite E
  exact Nat.card (AddCommGroup.torsion E.1.toAffine.Point)

/-- Object slots for the three standard refined-BSD arithmetic factors not
yet canonically constructed for every arbitrary curve in this repo.  This
record says only which values are being bound to a curve; it does not confuse
their side-properties with their object identity. -/
structure BSDRefinedArithmeticCarrier where
  period : RationalEllipticCurve → ℝ
  regulator : RationalEllipticCurve → ℝ
  tamagawaProduct : RationalEllipticCurve → ℕ

/-- Standard elementary side-properties of a proposed refined arithmetic
carrier.  These are separate from the same-object binding problem. -/
structure BSDRefinedArithmeticCertification
    (a : BSDRefinedArithmeticCarrier) : Prop where
  period_pos : ∀ E, 0 < a.period E
  regulator_nonneg : ∀ E, 0 ≤ a.regulator E
  tamagawaProduct_pos : ∀ E, 0 < a.tamagawaProduct E

/-- Certified refined arithmetic data.  The genuinely open infrastructure is
still to bind these fields to the canonical period, Néron--Tate regulator,
and product of Tamagawa numbers for the same literal curve. -/
structure BSDRefinedArithmeticBinding where
  carrier : BSDRefinedArithmeticCarrier
  certified : BSDRefinedArithmeticCertification carrier

namespace BSDRefinedArithmeticBinding

abbrev period (a : BSDRefinedArithmeticBinding) :=
  a.carrier.period

abbrev regulator (a : BSDRefinedArithmeticBinding) :=
  a.carrier.regulator

abbrev tamagawaProduct (a : BSDRefinedArithmeticBinding) :=
  a.carrier.tamagawaProduct

end BSDRefinedArithmeticBinding

/-- Object-level interface required before refined BSD can be stated literally:
the classical Tate--Shafarevich carrier attached to each actual rational
elliptic curve.  No finiteness assumption is included here. -/
structure BSDUniversalShaCarrier where
  Sha : RationalEllipticCurve → Type

/-- Refined BSD finiteness conjecture, kept separate from construction of the
classical Sha carrier. -/
def UniversalBSDShaFiniteness
    (S : BSDUniversalShaCarrier) : Prop :=
  ∀ E : RationalEllipticCurve, Finite (S.Sha E)

/-- A finite Sha binding is only the combination needed at the point where
cardinality enters the refined formula. -/
structure BSDUniversalShaFiniteBinding where
  carrier : BSDUniversalShaCarrier
  finiteSha : UniversalBSDShaFiniteness carrier

/-- Once finiteness has been supplied as a separate conjectural theorem,
Sha cardinality is canonical. -/
noncomputable def BSDUniversalShaFiniteBinding.order
    (S : BSDUniversalShaFiniteBinding)
    (E : RationalEllipticCurve) : ℕ := by
  letI : Finite (S.carrier.Sha E) := S.finiteSha E
  exact Nat.card (S.carrier.Sha E)

/-- Full same-object data needed to state the refined formula after Sha
finiteness has been supplied separately. -/
structure BSDBoundRefinedData where
  rank : BSDBoundRankObservers
  arithmetic : BSDRefinedArithmeticBinding
  sha : BSDUniversalShaFiniteBinding

/-- Right-hand side of the refined BSD formula on the currently bound data.
The expression is cast to C to compare directly with the analytic leading
Taylor coefficient. -/
noncomputable def BSDRefinedArithmeticSide
    (b : BSDBoundRefinedData)
    (E : RationalEllipticCurve) : ℂ :=
  ((b.arithmetic.period E : ℂ) *
      (b.arithmetic.regulator E : ℂ) *
      (b.sha.order E : ℂ) *
      (b.arithmetic.tamagawaProduct E : ℂ)) /
    (rationalEllipticCurveTorsionOrder E : ℂ) ^ 2

/-- Literal leading-coefficient identity for one arbitrary rational elliptic
curve, using the same analytic continuation/rank binding as the rank theorem. -/
def BSDLeadingCoefficientIdentityAt
    (b : BSDBoundRefinedData)
    (E : RationalEllipticCurve) : Prop :=
  (b.rank.analytic.continuation E).normalizedLeadingCoefficient =
    BSDRefinedArithmeticSide b E

/-- Universal normalized leading-coefficient identity. -/
def UniversalBSDLeadingCoefficientIdentity
    (b : BSDBoundRefinedData) : Prop :=
  ∀ E : RationalEllipticCurve,
    BSDLeadingCoefficientIdentityAt b E

/-- Prize-facing refined BSD package.  Sha finiteness is now an explicit
separate theorem carried by bound.sha.finiteSha; it is not part of merely
constructing the Sha carrier. -/
structure UniversalBSDRefinedProof where
  bound : BSDBoundRefinedData
  rankWeld : UniversalBSDBoundRankWeld bound.rank
  leadingCoefficient : UniversalBSDLeadingCoefficientIdentity bound

def UniversalBSDRefinedTheorem : Prop :=
  Nonempty UniversalBSDRefinedProof

/-- Refined BSD implies the universal rank theorem on the same bound ranks. -/
theorem universalBSDRankTheorem_of_refined
    (h : UniversalBSDRefinedTheorem) :
    UniversalBSDRankTheorem := by
  rcases h with ⟨p⟩
  exact ⟨
    { bound := p.bound.rank
      rankWeld := p.rankWeld }⟩

/-- Machine-readable refined max-cut. -/
structure BSDUniversalRefinedMaxCutStatus where
  normalizedLeadingCoefficientPaid : Bool
  leadingCoefficientWitnessIndependencePaid : Bool
  actualRationalTorsionOrderPaid : Bool
  arithmeticCarrierSidePropertiesSeparatedPaid : Bool
  universalPeriodBindingPaid : Bool
  universalRegulatorBindingPaid : Bool
  universalTamagawaBindingPaid : Bool
  universalClassicalShaCarrierPaid : Bool
  shaCarrierFinitenessSeparatedPaid : Bool
  universalShaFinitenessPaid : Bool
  universalLeadingCoefficientIdentityPaid : Bool
  deriving DecidableEq, Repr

def bsdUniversalRefinedMaxCutStatus :
    BSDUniversalRefinedMaxCutStatus :=
  ⟨true, true, true, true,
    false, false, false, false, true, false, false⟩

end Synthesis.Millennium.BSD
