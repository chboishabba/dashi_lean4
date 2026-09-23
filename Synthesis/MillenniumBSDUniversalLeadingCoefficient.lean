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

/-- Universal binding surface for the arithmetic factors for which this repo
does not yet have canonical arbitrary-curve objects.  These fields are
deliberately labelled bindings rather than definitions. -/
structure BSDRefinedArithmeticBinding where
  period : RationalEllipticCurve → ℝ
  period_pos : ∀ E, 0 < period E
  regulator : RationalEllipticCurve → ℝ
  regulator_nonneg : ∀ E, 0 ≤ regulator E
  tamagawaProduct : RationalEllipticCurve → ℕ
  tamagawaProduct_pos : ∀ E, 0 < tamagawaProduct E

/-- Object-level interface required before refined BSD can be stated literally:
a classical Sha carrier for every arbitrary rational elliptic curve, together
with a proof that the carrier is the same Sha object used by the conjecture. -/
structure BSDUniversalShaBinding where
  Sha : RationalEllipticCurve → Type
  finiteSha : ∀ E, Finite (Sha E)

/-- Once a universal Sha carrier is bound, its cardinality is canonical. -/
noncomputable def BSDUniversalShaBinding.order
    (S : BSDUniversalShaBinding)
    (E : RationalEllipticCurve) : ℕ := by
  letI : Finite (S.Sha E) := S.finiteSha E
  exact Nat.card (S.Sha E)

/-- Full same-object data needed to state the refined formula. -/
structure BSDBoundRefinedData where
  rank : BSDBoundRankObservers
  arithmetic : BSDRefinedArithmeticBinding
  sha : BSDUniversalShaBinding

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

/-- Prize-facing refined BSD package.  Sha finiteness is present in the Sha
binding itself; the rank equality and leading coefficient are separate
universal mathematical obligations. -/
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
  universalPeriodBindingPaid : Bool
  universalRegulatorBindingPaid : Bool
  universalTamagawaBindingPaid : Bool
  universalClassicalShaCarrierPaid : Bool
  universalShaFinitenessPaid : Bool
  universalLeadingCoefficientIdentityPaid : Bool
  deriving DecidableEq, Repr

def bsdUniversalRefinedMaxCutStatus :
    BSDUniversalRefinedMaxCutStatus :=
  ⟨true, true, true,
    false, false, false, false, false, false⟩

end Synthesis.Millennium.BSD
