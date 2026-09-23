import Synthesis.MillenniumBSDUniversalRankWeld
import Synthesis.MillenniumBSDUniversalEllipticPointTopRep
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

Now canonical at the object level:
* the full E(Qbar) Galois representation for arbitrary E/Q;
* the classical degree-one Sha carrier as the literal global-to-local
  continuous-cohomology kernel.

Still conjectural:
* universal finiteness of that fixed Sha carrier;
* the universal normalized leading-coefficient identity.
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

/-- The universal actual elliptic-point Galois representation is now a
canonical construction, not a supplied binding. -/
def UniversalBSDEllipticPointRepresentationPaid : Prop :=
  ∀ E : RationalEllipticCurve,
    Nonempty (TopRep ℤ RationalAbsoluteGalois)

theorem universalBSDEllipticPointRepresentation_paid :
    UniversalBSDEllipticPointRepresentationPaid := by
  intro E
  exact ⟨rationalEllipticCurvePointRepresentation E⟩

/-- Canonical classical Sha carrier on the actual universal E(Qbar)
representation. -/
noncomputable def rationalEllipticCurveSha
    (E : RationalEllipticCurve) : Type :=
  rationalTateShafarevichOne
    (rationalEllipticCurvePointRepresentation E)

theorem rationalEllipticCurveSha_sameObject
    (E : RationalEllipticCurve) :
    rationalEllipticCurveSha E =
      rationalTateShafarevichOne
        (rationalEllipticCurvePointRepresentation E) := by
  rfl

/-- Refined BSD finiteness conjecture for the canonical classical
cohomological Sha carrier constructed above. -/
def UniversalBSDCanonicalShaFiniteness : Prop :=
  ∀ E : RationalEllipticCurve, Finite (rationalEllipticCurveSha E)

/-- Once canonical Sha finiteness is supplied as a separate conjectural
theorem, its cardinality is canonical. -/
noncomputable def rationalEllipticCurveShaOrder
    (hFinite : UniversalBSDCanonicalShaFiniteness)
    (E : RationalEllipticCurve) : ℕ := by
  letI : Finite (rationalEllipticCurveSha E) := hFinite E
  exact Nat.card (rationalEllipticCurveSha E)

/-- Same-object refined carriers only.  The Sha carrier is no longer a field:
it is globally fixed to the canonical cohomological carrier above. -/
structure BSDBoundRefinedData where
  rank : BSDBoundRankObservers
  arithmetic : BSDRefinedArithmeticBinding

/-- Right-hand side of the refined BSD formula on the canonical Sha carrier,
once its finiteness conjecture is supplied separately. -/
noncomputable def BSDRefinedArithmeticSide
    (b : BSDBoundRefinedData)
    (hShaFinite : UniversalBSDCanonicalShaFiniteness)
    (E : RationalEllipticCurve) : ℂ :=
  ((b.arithmetic.period E : ℂ) *
      (b.arithmetic.regulator E : ℂ) *
      (rationalEllipticCurveShaOrder hShaFinite E : ℂ) *
      (b.arithmetic.tamagawaProduct E : ℂ)) /
    (rationalEllipticCurveTorsionOrder E : ℂ) ^ 2

/-- Literal leading-coefficient identity for one arbitrary rational elliptic
curve on the canonical Sha carrier. -/
def BSDLeadingCoefficientIdentityAt
    (b : BSDBoundRefinedData)
    (hShaFinite : UniversalBSDCanonicalShaFiniteness)
    (E : RationalEllipticCurve) : Prop :=
  (b.rank.analytic.continuation E).normalizedLeadingCoefficient =
    BSDRefinedArithmeticSide b hShaFinite E

/-- Universal normalized leading-coefficient identity. -/
def UniversalBSDLeadingCoefficientIdentity
    (b : BSDBoundRefinedData)
    (hShaFinite : UniversalBSDCanonicalShaFiniteness) : Prop :=
  ∀ E : RationalEllipticCurve,
    BSDLeadingCoefficientIdentityAt b hShaFinite E

/-- Refined BSD has three universal mathematical obligations on one fixed
same-object carrier: rank equality, canonical Sha finiteness, and the
normalized leading-coefficient identity. -/
structure UniversalBSDRefinedProof where
  bound : BSDBoundRefinedData
  shaFinite : UniversalBSDCanonicalShaFiniteness
  rankWeld : UniversalBSDBoundRankWeld bound.rank
  leadingCoefficient :
    UniversalBSDLeadingCoefficientIdentity bound shaFinite

def UniversalBSDRefinedTheorem : Prop :=
  Nonempty UniversalBSDRefinedProof

/-- Known-math/object-binding surface for the refined arithmetic symbols.
This does not include Sha finiteness or either BSD equality. -/
def UniversalBSDRefinedCarrierProducer : Prop :=
  Nonempty BSDBoundRefinedData

/-- Known-math same-object producer for the period/regulator/Tamagawa layer. -/
def UniversalBSDRefinedArithmeticBindingProducer : Prop :=
  Nonempty BSDRefinedArithmeticBinding

/-- The complete refined carrier is compiled from the rank bindings and the
period/regulator/Tamagawa same-object binding.  The elliptic-point/Sha carrier
is canonical globally and no longer supplied here. -/
theorem universalBSDRefinedCarrierProducer_of_components
    (hA : UniversalBSDAnalyticBindingProducer)
    (hMW : UniversalBSDMordellWeilBindingProducer)
    (hArithmetic : UniversalBSDRefinedArithmeticBindingProducer) :
    UniversalBSDRefinedCarrierProducer := by
  rcases hA with ⟨a⟩
  rcases hMW with ⟨m⟩
  rcases hArithmetic with ⟨arith⟩
  exact ⟨
    { rank := { analytic := a, algebraic := m }
      arithmetic := arith }⟩

/-- Explicit Sha-finiteness producer on the fixed canonical classical Sha
carrier. -/
def UniversalBSDShaFinitenessProducer : Prop :=
  UniversalBSDCanonicalShaFiniteness

/-- Explicit universal leading-coefficient producer after canonical Sha
finiteness is available. -/
def UniversalBSDLeadingCoefficientProducer
    (b : BSDBoundRefinedData)
    (hSha : UniversalBSDShaFinitenessProducer) : Prop :=
  UniversalBSDLeadingCoefficientIdentity b hSha

/-- Fully separated compiler for refined BSD on one chosen same-object
rank/arithmetic carrier and the fixed canonical Sha carrier. -/
theorem universalBSDRefinedTheorem_of_bound
    (b : BSDBoundRefinedData)
    (hSha : UniversalBSDShaFinitenessProducer)
    (hRank : UniversalBSDBoundRankWeld b.rank)
    (hLeading : UniversalBSDLeadingCoefficientProducer b hSha) :
    UniversalBSDRefinedTheorem :=
  ⟨
    { bound := b
      shaFinite := hSha
      rankWeld := hRank
      leadingCoefficient := hLeading }⟩

/-- Existence-shaped producer form. -/
theorem universalBSDRefinedTheorem_of_producers
    (h :
      ∃ (b : BSDBoundRefinedData),
        UniversalBSDBoundRankWeld b.rank ∧
          ∃ hSha : UniversalBSDShaFinitenessProducer,
            UniversalBSDLeadingCoefficientProducer b hSha) :
    UniversalBSDRefinedTheorem := by
  rcases h with ⟨b, hRank, hSha, hLeading⟩
  exact universalBSDRefinedTheorem_of_bound
    b hSha hRank hLeading

/-- Refined BSD implies the universal rank theorem on the same bound ranks. -/
theorem universalBSDRankTheorem_of_refined
    (h : UniversalBSDRefinedTheorem) :
    UniversalBSDRankTheorem := by
  rcases h with ⟨p⟩
  exact ⟨
    { bound := p.bound.rank
      rankWeld := p.rankWeld }⟩

/-- The two refined conjectural obligations are separately readable from a
refined proof package. -/
theorem universalBSDShaFiniteness_of_refined
    (h : UniversalBSDRefinedTheorem) :
    UniversalBSDCanonicalShaFiniteness := by
  rcases h with ⟨p⟩
  exact p.shaFinite

theorem universalBSDLeadingCoefficient_of_refined
    (h : UniversalBSDRefinedTheorem) :
    ∃ (b : BSDBoundRefinedData)
      (hSha : UniversalBSDCanonicalShaFiniteness),
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
  universalClassicalShaCarrierPaid : Bool
  refinedCarrierCompilerPaid : Bool
  shaCarrierFinitenessSeparatedPaid : Bool
  universalShaFinitenessPaid : Bool
  universalLeadingCoefficientIdentityPaid : Bool
  deriving DecidableEq, Repr

def bsdUniversalRefinedMaxCutStatus :
    BSDUniversalRefinedMaxCutStatus :=
  ⟨true, true, true, true,
    false, false, false, true, true, true, true, false, false⟩

end Synthesis.Millennium.BSD
