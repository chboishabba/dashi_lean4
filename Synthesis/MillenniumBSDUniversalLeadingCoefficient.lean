import Synthesis.MillenniumBSDUniversalRankWeld
import Synthesis.MillenniumBSDSelmerShaCohomologicalBoundary
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

/-- Universal same-object interface for the full elliptic-point
Galois module.  The remaining known-math object-binding task is to construct,
for every literal E/Q, the actual discrete TopRep carried by E(Qbar). -/
structure BSDUniversalEllipticPointRepresentationBinding where
  representation :
    RationalEllipticCurve → TopRep ℤ RationalAbsoluteGalois

/-- The classical degree-one Sha carrier is then not arbitrary: it is the
repo's literal global-to-local continuous-cohomology kernel for the supplied
elliptic-point representation. -/
noncomputable def BSDUniversalEllipticPointRepresentationBinding.Sha
    (P : BSDUniversalEllipticPointRepresentationBinding)
    (E : RationalEllipticCurve) : Type :=
  rationalTateShafarevichOne (P.representation E)

/-- Object-level classical Sha carrier, canonically derived from a bound
elliptic-point Galois representation.  No finiteness assumption occurs here. -/
structure BSDUniversalShaCarrier where
  ellipticPoints : BSDUniversalEllipticPointRepresentationBinding

namespace BSDUniversalShaCarrier

noncomputable abbrev Sha
    (S : BSDUniversalShaCarrier)
    (E : RationalEllipticCurve) : Type :=
  S.ellipticPoints.Sha E

end BSDUniversalShaCarrier

/-- Refined BSD finiteness conjecture, kept separate from construction of the
classical cohomological Sha carrier. -/
def UniversalBSDShaFiniteness
    (S : BSDUniversalShaCarrier) : Prop :=
  ∀ E : RationalEllipticCurve, Finite (S.Sha E)

/-- Once finiteness has been supplied as a separate conjectural theorem,
Sha cardinality is canonical. -/
noncomputable def BSDUniversalShaCarrier.order
    (S : BSDUniversalShaCarrier)
    (hFinite : UniversalBSDShaFiniteness S)
    (E : RationalEllipticCurve) : ℕ := by
  letI : Finite (S.Sha E) := hFinite E
  exact Nat.card (S.Sha E)

/-- Same-object refined carriers only.  Sha finiteness is deliberately not
stored here. -/
structure BSDBoundRefinedData where
  rank : BSDBoundRankObservers
  arithmetic : BSDRefinedArithmeticBinding
  sha : BSDUniversalShaCarrier

/-- Right-hand side of the refined BSD formula once Sha finiteness is supplied
as a separate theorem. -/
noncomputable def BSDRefinedArithmeticSide
    (b : BSDBoundRefinedData)
    (hShaFinite : UniversalBSDShaFiniteness b.sha)
    (E : RationalEllipticCurve) : ℂ :=
  ((b.arithmetic.period E : ℂ) *
      (b.arithmetic.regulator E : ℂ) *
      (b.sha.order hShaFinite E : ℂ) *
      (b.arithmetic.tamagawaProduct E : ℂ)) /
    (rationalEllipticCurveTorsionOrder E : ℂ) ^ 2

/-- Literal leading-coefficient identity for one arbitrary rational elliptic
curve, parameterized by the separate Sha-finiteness theorem. -/
def BSDLeadingCoefficientIdentityAt
    (b : BSDBoundRefinedData)
    (hShaFinite : UniversalBSDShaFiniteness b.sha)
    (E : RationalEllipticCurve) : Prop :=
  (b.rank.analytic.continuation E).normalizedLeadingCoefficient =
    BSDRefinedArithmeticSide b hShaFinite E

/-- Universal normalized leading-coefficient identity. -/
def UniversalBSDLeadingCoefficientIdentity
    (b : BSDBoundRefinedData)
    (hShaFinite : UniversalBSDShaFiniteness b.sha) : Prop :=
  ∀ E : RationalEllipticCurve,
    BSDLeadingCoefficientIdentityAt b hShaFinite E

/-- Refined BSD has two distinct universal conjectural layers after object
binding: Sha finiteness and the normalized leading-coefficient identity. -/
structure UniversalBSDRefinedProof where
  bound : BSDBoundRefinedData
  shaFinite : UniversalBSDShaFiniteness bound.sha
  rankWeld : UniversalBSDBoundRankWeld bound.rank
  leadingCoefficient :
    UniversalBSDLeadingCoefficientIdentity bound shaFinite

def UniversalBSDRefinedTheorem : Prop :=
  Nonempty UniversalBSDRefinedProof


/-- Known-math/object-binding surface for the refined arithmetic symbols.
This does not include Sha finiteness or the leading-coefficient conjecture. -/
def UniversalBSDRefinedCarrierProducer : Prop :=
  Nonempty BSDBoundRefinedData

/-- Explicit Sha-finiteness producer on a chosen classical Sha carrier. -/
def UniversalBSDShaFinitenessProducer
    (b : BSDBoundRefinedData) : Prop :=
  UniversalBSDShaFiniteness b.sha

/-- Explicit universal leading-coefficient producer after Sha finiteness is
available on the same carrier. -/
def UniversalBSDLeadingCoefficientProducer
    (b : BSDBoundRefinedData)
    (hSha : UniversalBSDShaFinitenessProducer b) : Prop :=
  UniversalBSDLeadingCoefficientIdentity b hSha

/-- Fully separated compiler for refined BSD: object bindings, Sha
finiteness, rank equality, and the leading coefficient remain distinct
inputs until the final package. -/
theorem universalBSDRefinedTheorem_of_producers
    (hCarrier : UniversalBSDRefinedCarrierProducer)
    (hSha :
      ∀ b : BSDBoundRefinedData,
        UniversalBSDShaFinitenessProducer b)
    (hRank :
      ∀ b : BSDBoundRefinedData,
        UniversalBSDBoundRankWeld b.rank)
    (hLeading :
      ∀ (b : BSDBoundRefinedData)
        (hs : UniversalBSDShaFinitenessProducer b),
        UniversalBSDLeadingCoefficientProducer b hs) :
    UniversalBSDRefinedTheorem := by
  rcases hCarrier with ⟨b⟩
  exact ⟨
    { bound := b
      shaFinite := hSha b
      rankWeld := hRank b
      leadingCoefficient := hLeading b (hSha b) }⟩

/-- Refined BSD implies the universal rank theorem on the same bound ranks. -/
theorem universalBSDRankTheorem_of_refined
    (h : UniversalBSDRefinedTheorem) :
    UniversalBSDRankTheorem := by
  rcases h with ⟨p⟩
  exact ⟨
    { bound := p.bound.rank
      rankWeld := p.rankWeld }⟩

/-- The two conjectural refined obligations are separately readable from a
refined proof package. -/
theorem universalBSDShaFiniteness_of_refined
    (h : UniversalBSDRefinedTheorem) :
    ∃ b : BSDBoundRefinedData,
      UniversalBSDShaFiniteness b.sha := by
  rcases h with ⟨p⟩
  exact ⟨p.bound, p.shaFinite⟩

theorem universalBSDLeadingCoefficient_of_refined
    (h : UniversalBSDRefinedTheorem) :
    ∃ (b : BSDBoundRefinedData)
      (hSha : UniversalBSDShaFiniteness b.sha),
      UniversalBSDLeadingCoefficientIdentity b hSha := by
  rcases h with ⟨p⟩
  exact ⟨p.bound, p.shaFinite, p.leadingCoefficient⟩

/-- Machine-readable refined max-cut. -/
structure BSDUniversalRefinedMaxCutStatus where
  normalizedLeadingCoefficientPaid : Bool
  leadingCoefficientWitnessIndependencePaid : Bool
  actualRationalTorsionOrderPaid : Bool
  arithmeticCarrierSidePropertiesSeparatedPaid : Bool
  universalPeriodBindingPaid : Bool
  universalRegulatorBindingPaid : Bool
  universalTamagawaBindingPaid : Bool
  universalEllipticPointRepresentationPaid : Bool
  universalClassicalShaCarrierCompilerPaid : Bool
  shaCarrierFinitenessSeparatedPaid : Bool
  universalShaFinitenessPaid : Bool
  universalLeadingCoefficientIdentityPaid : Bool
  deriving DecidableEq, Repr

def bsdUniversalRefinedMaxCutStatus :
    BSDUniversalRefinedMaxCutStatus :=
  ⟨true, true, true, true,
    false, false, false, false, true, true, false, false⟩

end Synthesis.Millennium.BSD
