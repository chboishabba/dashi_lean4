import Synthesis.MillenniumBSDMathlibLFunctionWeld
import Synthesis.MillenniumBSDFrobeniusPointCount
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Tactic

/-!
# E32 actual Mathlib Euler polynomial <-> original finite-field count, BIDI

The original curve is cmWeierstrass : WeierstrassCurve ℚ, namely
y² = x³ - x. cmFormalLFunction already IS cmWeierstrass.LFunction.
Do not construct a new global L-function or arbitrary coefficient stream.

Mathlib's WeierstrassCurve.localPolynomial reduces the MINIMAL
p-adic integral Weierstrass model. The existing original frobeniusCoefficient
counts the literal y²=x³-x over ZMod p. These objects are not definitional
equals: prime place, residue field and reduction-point-group identification
are exact source witnesses below. The additive prime p=2 requires
its own genuine original minimal-model reduction proof.

Original owners: Mathlib WeierstrassCurve.localPolynomial / LFunction;
DASHI MillenniumBSDMathlibLFunctionWeld and MillenniumBSDFrobeniusPointCount.
Source-written, NOT Lean-kernel checked; not a BSD proof.
-/

namespace Synthesis.Millennium.BSD

open NumberField IsDedekindDomain Polynomial

/-- The actual Mathlib inverse local Euler polynomial at an original
    prime ideal; never a replacement elliptic L-function. -/
noncomputable def cmOriginalMathlibLocalPolynomial
    (place : HeightOneSpectrum (𝓞 ℚ)) : Polynomial ℤ :=
  (cmWeierstrass.baseChange (place.adicCompletion ℚ)).localPolynomial
    (place.adicCompletionIntegers ℚ)

/-- Independent GOOD local polynomial from the already-source-owned
    direct point-count coefficient. -/
noncomputable def cmOriginalCountedGoodPolynomial
    (p : ℕ) [Fact p.Prime] : Polynomial ℤ :=
  1 - C (frobeniusCoefficient p) * X + C (p : ℤ) * X ^ 2

/-- Exact original-field-to-original-Mathlib bridge. These hypotheses
    assert the three physical/arithmetic identifications, not the desired
    polynomial equality or a new L-function. In particular hReducedCount
    identifies the MINIMAL reduced model's actual point group with the
    original direct ZMod-p count. -/
theorem cmOriginalMathlibGoodPolynomial_eq_originalPointCount
    (place : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ) [Fact p.Prime]
    (hGood :
      ((cmWeierstrass.baseChange (place.adicCompletion ℚ)).minimal
        (place.adicCompletionIntegers ℚ)).HasGoodReduction
        (place.adicCompletionIntegers ℚ))
    (hResidue :
      Nat.card (IsLocalRing.ResidueField (place.adicCompletionIntegers ℚ)) = p)
    (hReducedCount :
      Nat.card
        (((cmWeierstrass.baseChange (place.adicCompletion ℚ)).minimal
          (place.adicCompletionIntegers ℚ)).reduction
          (place.adicCompletionIntegers ℚ)).toAffine.Point
        = projectivePointCount p) :
    cmOriginalMathlibLocalPolynomial place =
      cmOriginalCountedGoodPolynomial p := by
  simp [cmOriginalMathlibLocalPolynomial, cmOriginalCountedGoodPolynomial,
    WeierstrassCurve.localPolynomial, hGood, hResidue, hReducedCount,
    frobeniusCoefficient]

/-- Original Mathlib additive branch: still needs a source-certified
    prime over 2 and its genuine minimal additive reduction facts.
    Do NOT infer additive reduction merely from the discriminant. -/
theorem cmOriginalMathlibAdditivePolynomial_eq_one
    (place : HeightOneSpectrum (𝓞 ℚ))
    (hNotGood :
      ¬ ((cmWeierstrass.baseChange (place.adicCompletion ℚ)).minimal
        (place.adicCompletionIntegers ℚ)).HasGoodReduction
        (place.adicCompletionIntegers ℚ))
    (hNotSplit :
      ¬ ((cmWeierstrass.baseChange (place.adicCompletion ℚ)).minimal
        (place.adicCompletionIntegers ℚ)).HasSplitMultiplicativeReduction
        (place.adicCompletionIntegers ℚ))
    (hNotMult :
      ¬ ((cmWeierstrass.baseChange (place.adicCompletion ℚ)).minimal
        (place.adicCompletionIntegers ℚ)).HasMultiplicativeReduction
        (place.adicCompletionIntegers ℚ)) :
    cmOriginalMathlibLocalPolynomial place = 1 := by
  simp [cmOriginalMathlibLocalPolynomial,
    WeierstrassCurve.localPolynomial, hNotGood, hNotSplit, hNotMult]

/-- The original CM character-sum result yields the SAME counted good
    Euler polynomial as the source point-count coefficient. -/
theorem cmOriginalCountedGoodPolynomial_characterSum
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    cmOriginalCountedGoodPolynomial p =
      1 + C (cmCharacterSum p) * X + C (p : ℤ) * X ^ 2 := by
  simp [cmOriginalCountedGoodPolynomial,
    frobeniusCoefficient_eq_neg_characterSum hp2]

end Synthesis.Millennium.BSD
