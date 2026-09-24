import Synthesis.RiemannProjectiveMonotoneWeightCovariance
import Zeta23Bridge.LiteralWeilTwoRadiusSeparationGate

/-!
# Generic curvature firewall for projective two-radius tapers

The canonical positive lobe is not an accident of the particular two-window
taper.

For any continuous compactly supported nonnegative taper `g`, if the doubled
sampling radius remains in the radial cosine window

  2 r |u| < pi/2

throughout the support and the support contains two positive points at distinct
moduli, the strict radial covariance theorem applied to `w(u)=u^2` gives

  integral g(u) u^2 B_r(u) du < 0.

This is exactly the signed second-moment direction that produces positive
curvature of the q-only projective kernel at q=0 after the usual positive
normalization/scaling.

Consequently a target-dependent family cannot reverse the local curvature while
retaining all of the present GateData geometry.  Any Route-B design that seeks
the opposite second-moment sign must genuinely leave at least one of:

* nonnegativity of the taper;
* doubled-radius radial admissibility;
* nondegenerate positive support at two distinct radii.

This is a mathematical design firewall, not an explicit-formula bookkeeping
identity.
-/

noncomputable section

open MeasureTheory Set
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector
open Zeta23Bridge.LiteralWeilTwoRadiusSeparationGate

/--
Generic strict second-moment sign for every nonnegative radially-admissible
projective two-radius taper.
-/
theorem projective_u_sq_covariance_neg_of_radial_gate
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (hnn : ∀ u, 0 ≤ g u)
    {r : ℝ}
    (hr : 0 < r)
    (hrad : ∀ u, g u ≠ 0 → 2 * r * |u| < Real.pi / 2)
    {u0 v0 : ℝ}
    (hu0 : 0 < g u0)
    (hv0 : 0 < g v0)
    (hne : |u0| ≠ |v0|) :
    (∫ u : ℝ,
      g u * u^2 * twoRadiusBracket g r u) < 0 := by
  apply integral_weight_mul_twoRadiusBracket_neg
    hg hgc hnn
    (by fun_prop : Continuous (fun u : ℝ => u^2))
    hr hrad
  · intro u v hu hv huv
    nlinarith [sq_abs u, sq_abs v, abs_nonneg u, abs_nonneg v]
  · exact hu0
  · exact hv0
  · exact hne
  · intro huv
    nlinarith [sq_abs u0, sq_abs v0, abs_nonneg u0, abs_nonneg v0]
  · intro hvu
    nlinarith [sq_abs u0, sq_abs v0, abs_nonneg u0, abs_nonneg v0]

/--
The opposite second-moment sign required by the naive curvature-reversal Route B
is impossible under the same radial gate hypotheses.
-/
theorem not_projective_u_sq_covariance_pos_of_radial_gate
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (hnn : ∀ u, 0 ≤ g u)
    {r : ℝ}
    (hr : 0 < r)
    (hrad : ∀ u, g u ≠ 0 → 2 * r * |u| < Real.pi / 2)
    {u0 v0 : ℝ}
    (hu0 : 0 < g u0)
    (hv0 : 0 < g v0)
    (hne : |u0| ≠ |v0|) :
    ¬ 0 <
      (∫ u : ℝ,
        g u * u^2 * twoRadiusBracket g r u) := by
  have hneg :=
    projective_u_sq_covariance_neg_of_radial_gate
      hg hgc hnn hr hrad hu0 hv0 hne
  linarith

/--
A nonnegative value is already incompatible with nondegenerate radial GateData;
the sign is forced strictly negative.
-/
theorem projective_u_sq_covariance_not_nonneg_of_radial_gate
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (hnn : ∀ u, 0 ≤ g u)
    {r : ℝ}
    (hr : 0 < r)
    (hrad : ∀ u, g u ≠ 0 → 2 * r * |u| < Real.pi / 2)
    {u0 v0 : ℝ}
    (hu0 : 0 < g u0)
    (hv0 : 0 < g v0)
    (hne : |u0| ≠ |v0|) :
    ¬ 0 ≤
      (∫ u : ℝ,
        g u * u^2 * twoRadiusBracket g r u) := by
  have hneg :=
    projective_u_sq_covariance_neg_of_radial_gate
      hg hgc hnn hr hrad hu0 hv0 hne
  linarith

/--
Direct GateData corollary.  In particular, making the taper depend on the target
horizontal displacement does not change this sign as long as each member of the
family remains inside the same GateData class.
-/
theorem GateData.projective_u_sq_covariance_neg
    {g : ℝ → ℝ} {t r Lambda : ℝ}
    (hd : GateData g t r Lambda) :
    (∫ u : ℝ,
      g u * u^2 * twoRadiusBracket g r u) < 0 := by
  obtain ⟨u0, v0, hu0, hv0, hne⟩ := hd.twoPoint
  exact projective_u_sq_covariance_neg_of_radial_gate
    hd.smooth.continuous hd.compactSupport hd.nonneg
    hd.radiusPos hd.radial hu0 hv0 hne

/--
There is no GateData inhabitant with the opposite projective second-moment sign.
This rules out the naive Route-B curvature reversal without changing the gate
geometry itself.
-/
theorem not_exists_gateData_with_projective_u_sq_covariance_pos
    {t r Lambda : ℝ} :
    ¬ ∃ g : ℝ → ℝ,
      GateData g t r Lambda ∧
      0 < (∫ u : ℝ,
        g u * u^2 * twoRadiusBracket g r u) := by
  rintro ⟨g, hd, hpos⟩
  have hneg := hd.projective_u_sq_covariance_neg
  linarith

/--
Family-level firewall.  No target-dependent family whose every member remains
GateData can realize the positive second moment proposed by curvature-reversal
Route B at any parameter value.
-/
theorem no_gateData_family_with_positive_projective_second_moment
    {I : Type*}
    {t r Lambda : I → ℝ}
    {g : I → ℝ → ℝ}
    (hd : ∀ i, GateData (g i) (t i) (r i) (Lambda i)) :
    ¬ ∃ i : I,
      0 < (∫ u : ℝ,
        g i u * u^2 * twoRadiusBracket (g i) (r i) u) := by
  rintro ⟨i, hpos⟩
  have hneg := (hd i).projective_u_sq_covariance_neg
  linarith

/--
Equivalent pointwise formulation useful for a target-height-indexed family:
every admissible member has strictly negative projective signed second moment.
-/
theorem gateData_family_projective_second_moment_neg
    {I : Type*}
    {t r Lambda : I → ℝ}
    {g : I → ℝ → ℝ}
    (hd : ∀ i, GateData (g i) (t i) (r i) (Lambda i))
    (i : I) :
    (∫ u : ℝ,
      g i u * u^2 * twoRadiusBracket (g i) (r i) u) < 0 :=
  (hd i).projective_u_sq_covariance_neg


end Synthesis
