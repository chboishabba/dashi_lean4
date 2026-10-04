import Synthesis.MillenniumBSDUniversalRankWeld
import EllipticCurves.SelmerGroup
import Mathlib.Tactic

/-!
# Real all-place Selmer donor on the literal BSD curve carrier

Provenance: Michael Stoll, `EllipticCurves/SelmerGroup.lean`, commit
1e4709496a2c0cb3da66b400efbb15939358d444 (Apache-2.0).
Its mathematical content is the genuine 2-Selmer subgroup of square classes
of the étale algebra K[X]/(f), cut out by the norm condition and the genuine
local Kummer images at every finite AND infinite place of K.

The key point: NO freely chosen Selmer or residual type appears here. It
uses `WeierstrassCurve.Affine.selmerGroup₂`, with Stoll's proved
`range_μ_le_selmerGroup₂` and `pow_rank_le_card_of_range_μ_le`.

The exact DASHI curve is `RationalEllipticCurve` =
`{W : WeierstrassCurve ℚ // W.IsElliptic}`.
This experimental branch is deliberately pinned to Lean/mathlib v4.34;
it does not silently upgrade the active v4.28 BSD PR.

Scope: the Stoll source currently requires a Weierstrass model in the
characteristic-not-two normal form (a₁=a₃=0). Changing an arbitrary
elliptic curve to this model AND transporting its literal L-series/rank data
on the frozen Clay carrier is still a distinct theorem.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve

noncomputable section

/-- Actual same-curve rational 2-Selmer group of a normal-form rational
elliptic curve, defined by Stoll's independent local and norm conditions. -/
noncomputable def actualNormalFormTwoSelmer
    (E : RationalEllipticCurve)
    [E.1.toAffine.IsCharNeTwoNF] :
    Subgroup E.1.toAffine.M := by
  letI : E.1.IsElliptic := E.2
  exact
    E.1.toAffine.selmerGroup₂
      ℤ
      (fun v : InfinitePlace ℚ => v.Completion)

/-- Its membership has genuine independent arithmetic content: étale norm
triviality AND all finite and infinite Kummer-image conditions. -/
theorem actualNormalFormTwoSelmer_mem_iff
    (E : RationalEllipticCurve)
    [E.1.toAffine.IsCharNeTwoNF]
    (c : E.1.toAffine.M) :
    c ∈ actualNormalFormTwoSelmer E ↔
      E.1.toAffine.normM c = 1
      ∧ (∀ v : HeightOneSpectrum ℤ,
          c ∈ E.1.toAffine.localCondition (v.adicCompletion ℚ))
      ∧ (∀ v : InfinitePlace ℚ,
          c ∈ E.1.toAffine.localCondition v.Completion) := by
  letI : E.1.IsElliptic := E.2
  classical
  exact E.1.toAffine.mem_selmerGroup₂_iff ℤ
    (fun v : InfinitePlace ℚ => v.Completion)

/-- Actual pointwise global Kummer image is contained in the arithmetic
all-place Selmer subgroup of THAT SAME rational elliptic curve. -/
theorem actualNormalFormKummer_range_le_selmer
    (E : RationalEllipticCurve)
    [E.1.toAffine.IsCharNeTwoNF] :
    (E.1.toAffine.μ).range ≤ actualNormalFormTwoSelmer E := by
  letI : E.1.IsElliptic := E.2
  classical
  exact E.1.toAffine.range_μ_le_selmerGroup₂ ℤ
    (fun v : InfinitePlace ℚ => v.Completion)

/-- Correct torsion-aware rank bound: an actual finite Selmer subgroup
dominates 2^rank times the rational two-torsion cardinality. -/
theorem actualNormalFormRankTorsionSelmerBound
    (E : RationalEllipticCurve)
    [E.1.toAffine.IsCharNeTwoNF]
    [AddGroup.FG E.1.toAffine.Point]
    [Finite (actualNormalFormTwoSelmer E)] :
    2 ^ Module.finrank ℤ E.1.toAffine.Point
      * Nat.card (nsmulAddMonoidHom (α := E.1.toAffine.Point) 2).ker
      ≤ Nat.card (actualNormalFormTwoSelmer E) := by
  letI : E.1.IsElliptic := E.2
  classical
  exact E.1.toAffine.pow_rank_le_card_of_range_μ_le
    (actualNormalFormKummer_range_le_selmer E)

/-!
Do not claim the following from this module:

* that normal-form Selmer has already been transported through the
  all-Weierstrass-coordinate-change equivalence on every `E`;
* that the cokernel is identified as Sha(E)[2];
* that the 2-Selmer *cardinality* itself determines the analytic rank;
* that a family of finite local groupoids has a canonical global gluing
  unless the actual localization maps and obstruction kernels are proved.

The new result imports REAL arithmetic; it is not the old trivial exactness
record. No theorem about analytic orders of vanishing is asserted.
-/

end

end Synthesis.Millennium.BSD
