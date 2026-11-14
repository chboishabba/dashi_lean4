import Mathlib.Tactic

/-!
# Selected BSD curve: integer valuation trichotomy for p=2

For a nonexceptional Q_2 point (x,y) on y^2=x(x-1)(x+1), let
vx=v_2(x), vy=v_2(y), vm=v_2(x-1), vp=v_2(x+1).
The curve equation gives 2*vy=vx+vm+vp.

The ultrametric case split at the unit:
  vx>0 => vm=vp=0
  vx<0 => vm=vp=vx
  vx=0 => parity immediate.
This file discharges the *integer arithmetic* independently, without
introducing an abstract fake elliptic group or asserting the p-adic
valuations themselves are already connected to this theorem.

Next genuine mathematical producer: instantiate the hypotheses from
Padic.addValuation / Padic.valuation on the original Q_2 curve,
and connect evenness of vx to the finite first-coordinate square-class
bit through a proved valuation-parity characterization.
-/

namespace Synthesis.Millennium.BSD

/-- All integer valuation data required from the actual 2-adic field. -/
theorem cmTwoAdicValuationParity_of_trichotomy
    (vx vy vm vp : ℤ)
    (hCurve : 2 * vy = vx + vm + vp)
    (hPos : 0 < vx → vm = 0 ∧ vp = 0)
    (hNeg : vx < 0 → vm = vx ∧ vp = vx) :
    ∃ k : ℤ, vx = 2 * k := by
  rcases lt_trichotomy vx 0 with hn | hz | hp
  · obtain ⟨hm, hplus⟩ := hNeg hn
    refine ⟨vy - vx, ?_⟩
    omega
  · refine ⟨0, ?_⟩
    omega
  · obtain ⟨hm, hplus⟩ := hPos hp
    refine ⟨vy, ?_⟩
    omega

/-- Positive-valuation branch: both shifted coordinates are units. -/
theorem cmTwoAdicValuationParity_positive
    (vx vy vm vp : ℤ)
    (hCurve : 2 * vy = vx + vm + vp)
    (hm : vm = 0)
    (hp : vp = 0) :
    vx = 2 * vy := by
  omega

/-- Negative-valuation branch: all three factors have valuation vx. -/
theorem cmTwoAdicValuationParity_negative
    (vx vy vm vp : ℤ)
    (hCurve : 2 * vy = vx + vm + vp)
    (hm : vm = vx)
    (hp : vp = vx) :
    vx = 2 * (vy - vx) := by
  omega

/-- Original x-T first-coordinate parity consumer: a 2-adic geometric
valuation theorem with the hypotheses above entails even valuation.
This is deliberately a relation on actual integer valuation *outputs*;
it does not assert their existence for local points. -/
theorem cmTwoAdicValuationParity_even
    (vx vy vm vp : ℤ)
    (hCurve : 2 * vy = vx + vm + vp)
    (hPos : 0 < vx → vm = 0 ∧ vp = 0)
    (hNeg : vx < 0 → vm = vx ∧ vp = vx) :
    Even vx := by
  obtain ⟨k, hk⟩ :=
    cmTwoAdicValuationParity_of_trichotomy vx vy vm vp hCurve hPos hNeg
  exact ⟨k, by omega⟩

end Synthesis.Millennium.BSD
