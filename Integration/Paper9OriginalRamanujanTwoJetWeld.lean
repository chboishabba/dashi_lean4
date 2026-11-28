import Mathlib

/-!
Paper 9, original Ramanujan-to-j two-jet algebra, source-written and
NOT kernel checked. No new modular function, point, Euler series, or
analytic differentiation axiom is constructed here.

The upstream original Eisenstein/Delta analytic owners must provide the
product-derivative identities on their actual q-disk object. From those
identities the two native FirstQJet / SecondQJet equations follow with
no independent analytic derivative hypothesis and no division by X.
-/
namespace Integration.Paper9OriginalRamanujanTwoJetWeld

open Complex

-- Use the original j*Delta=X^3 relation, its differentiated version,
-- Ramanujan's E4 flow, and Delta's logarithmic derivative. The only
-- cancellation is by the original NONZERO discriminant.
theorem firstJet
    (X Y E K Delta DX DDelta Dj : ℂ)
    (hDelta : Delta ≠ 0)
    (hQuot : K * Delta = X ^ 3)
    (hProduct : Dj * Delta + K * DDelta = 3 * X ^ 2 * DX)
    (hDeltaFlow : DDelta = E * Delta)
    (hE4 : 3 * DX = E * X - Y) :
    X * Dj = -(K * Y) := by
  have h : Delta * (X * Dj + K * Y) = 0 := by
    linear_combination
      X * hProduct - X * K * hDeltaFlow +
      X ^ 3 * hE4 - (E * X - Y) * hQuot
  rcases mul_eq_zero.mp h with hzero | hzero
  · exact False.elim (hDelta hzero)
  · linear_combination hzero

-- Differentiate the ALREADY CLEARED first identity, then substitute
-- BOTH original Ramanujan differential rules and U=3 D(E4).
-- No inverse or additional nonzero premise is used here.
theorem secondJet
    (X Y E K DX DY Dj D2j U : ℂ)
    (hFirst : X * Dj = -(K * Y))
    (hFirstDerivative : DX * Dj + X * D2j + Dj * Y + K * DY = 0)
    (hE4 : 3 * DX = E * X - Y)
    (hE6 : 2 * DY = E * Y - X ^ 2)
    (hU : U = 3 * DX) :
    6 * X ^ 2 * D2j = K * (3 * X ^ 3 + 3 * Y ^ 2 - Y * U) := by
  linear_combination
    (6 * X) * hFirstDerivative -
    (6 * (DX + Y)) * hFirst -
    (3 * X * K) * hE6 +
    (3 * K * Y) * hE4 +
    (K * Y) * hU

-- Existing native source equations in one bundled consumer, not a
-- replacement for the analytic product and Euler differentiation owners.
theorem originalTwoJets
    (X Y E K Delta DX DY DDelta Dj D2j U : ℂ)
    (hDelta : Delta ≠ 0)
    (hQuot : K * Delta = X ^ 3)
    (hProduct : Dj * Delta + K * DDelta = 3 * X ^ 2 * DX)
    (hDeltaFlow : DDelta = E * Delta)
    (hE4 : 3 * DX = E * X - Y)
    (hE6 : 2 * DY = E * Y - X ^ 2)
    (hFirstDerivative : DX * Dj + X * D2j + Dj * Y + K * DY = 0)
    (hU : U = 3 * DX) :
    X * Dj = -(K * Y) ∧
      6 * X ^ 2 * D2j = K * (3 * X ^ 3 + 3 * Y ^ 2 - Y * U) := by
  have hf := firstJet X Y E K Delta DX DDelta Dj
    hDelta hQuot hProduct hDeltaFlow hE4
  exact ⟨hf, secondJet X Y E K DX DY Dj D2j U
    hf hFirstDerivative hE4 hE6 hU⟩

#print axioms originalTwoJets
end Integration.Paper9OriginalRamanujanTwoJetWeld
