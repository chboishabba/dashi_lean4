import Synthesis.MillenniumBSDMathlibLFunctionWeld
import Synthesis.MillenniumBSDFrobeniusPointCount
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# Original E32 literal reduction geometry, before the p-adic minimal-model weld

The existing source cmWeierstrass : WeierstrassCurve ℚ is y²=x³-x.
The following model is its LITERAL integral-coefficient reduction to ZMod p,
not a second chosen elliptic curve or L-function. Its discriminant is 64.
Every odd-prime literal reduction is smooth; the characteristic-two fibre
has a singular point (1,0), with exact local equation (v+u)^2+u^3.

This does NOT yet prove that Mathlib's noncomputable minimal reduction at
HeightOneSpectrum (𝓞 ℚ) is this literal model, nor the residue-field
isomorphism, nor Mathlib's additive localPolynomial case at p=2.
The good-prime local polynomial compiler is owned by the existing
MillenniumBSDCMActualLocalEulerPointCountBidiExact module in PR #115.

Source-written; pending pinned Mathlib/Lean kernel replay. No BSD claim.
-/

namespace Synthesis.Millennium.BSD

/-- Direct reduction of the FIVE actual original integral coefficients.
    The rational source curve has the same literal coefficient vector. -/
def cmOriginalLiteralModP (p : ℕ) : WeierstrassCurve (ZMod p) :=
  ⟨0, 0, 0, -1, 0⟩

/-- The discriminant computation is independent of the characteristic. -/
theorem cmOriginalLiteralModP_discriminant (p : ℕ) :
    (cmOriginalLiteralModP p).Δ = (64 : ZMod p) := by
  rw [cmOriginalLiteralModP, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- All primes except 2 fail to divide the ACTUAL discriminant 64.
    This is one universal arithmetic input, not 54 finite samples. -/
theorem cmOriginalOddPrime_not_dvd_64 (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 64 := by
  intro h64
  have hpPow : p ∣ (2 : ℕ) ^ 6 := by
    simpa [show (2 : ℕ) ^ 6 = 64 by norm_num] using h64
  have hpTwo : p ∣ 2 := hp.dvd_of_dvd_pow hpPow
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpTwo
  exact hp2 (Nat.le_antisymm hle hp.two_le)

/-- A genuine universal nonzero discriminant statement on the original
    ZMod-p reduction, conditional only on primality and p != 2. -/
theorem cmOriginalLiteralModP_discriminant_ne_zero
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (cmOriginalLiteralModP p).Δ ≠ 0 := by
  rw [cmOriginalLiteralModP_discriminant]
  intro h64
  exact cmOriginalOddPrime_not_dvd_64 p Fact.out hp2
    ((ZMod.natCast_eq_zero_iff 64 p).mp h64)

/-- The original literal finite-field equation is an elliptic curve
    at ALL odd primes (not a proof about the chosen minimal model). -/
theorem cmOriginalLiteralModP_isElliptic
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (cmOriginalLiteralModP p).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  exact cmOriginalLiteralModP_discriminant_ne_zero p hp2

/-- Affine equation y²-x³+x, evaluated only on the original p=2 fibre. -/
def cmOriginalEquationTwo (x y : ZMod 2) : ZMod 2 :=
  y ^ 2 - x ^ 3 + x

/-- The literal bad fibre has an actual singular point, as its
    equation and BOTH affine partial derivatives vanish at (1,0). -/
theorem cmOriginalTwo_singularPoint :
    cmOriginalEquationTwo 1 0 = 0 ∧
    (1 - 3 * (1 : ZMod 2) ^ 2) = 0 ∧
    (2 * (0 : ZMod 2)) = 0 := by
  decide

/-- After x=1+u and y=v, the original characteristic-two curve
    has a DOUBLE tangent line and cubic term: a cusp, not a node. -/
theorem cmOriginalTwo_cuspChart :
    ∀ u v : ZMod 2,
      cmOriginalEquationTwo (1 + u) v = (v + u) ^ 2 + u ^ 3 := by
  decide

/-- Characteristic two is exactly the zero-discriminant case. -/
theorem cmOriginalTwo_discriminant_zero :
    (cmOriginalLiteralModP 2).Δ = 0 := by
  rw [cmOriginalLiteralModP_discriminant]
  decide

-- The remaining SAME-OBJECT seam is from the original integral-coefficient
-- fibre into Mathlib's chosen (cmWeierstrass.baseChange K).minimal R,
-- including the actual prime ideal, residue field and affine point group.
-- Do not promote cusp/smoothness alone to the source's localPolynomial.

end Synthesis.Millennium.BSD
