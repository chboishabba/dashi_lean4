import Mathlib

/-!
# Actual finite SU(2) plaquette cost, with separate CMP119 effective sectors

A unit quaternion (a,b,c,d) represents the compact SU(2) fundamental
matrix [[a+ib,c+id],[-c+id,a-ib]].  Its **real normalized fundamental
trace** is a. The usual positive Wilson plaquette cost is therefore 1-a,
not the abstract coefficient of an unrelated action basis.

This file proves pointwise, finite-cutoff consequences which require NO
assumption of existence of a continuum Yang--Mills measure.  The physical
identification of actual CMP119 edge/plaquette variables with this
quaternion carrier, the published source action, the product Haar integral,
and the gauge-invariant/reflection-positive measure remain distinct
obligations.  It does not infer such an identification from CMP109's
inverse-coupling recursion or the T4 symbolic projector.

Wilson (1974): DOI 10.1103/PhysRevD.10.2445.
Balaban CMP 119 (1988): DOI 10.1007/BF01217741.
-/

namespace RequestProject.YangMills

/-- Fundamental SU(2) holonomy as a unit quaternion. -/
structure SU2PlaquetteHolonomy where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  unit_quaternion : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1

/-- Real part of the fundamental trace, before dividing by two. -/
def su2FundamentalRealTrace (U : SU2PlaquetteHolonomy) : ℝ :=
  2 * U.a

/-- The standard SU(2) Wilson cost 1 - (Re Tr U)/2. -/
def su2PositivePlaquetteCost (U : SU2PlaquetteHolonomy) : ℝ :=
  1 - su2FundamentalRealTrace U / 2

theorem su2_real_trace_normalization (U : SU2PlaquetteHolonomy) :
    su2PositivePlaquetteCost U = 1 - U.a := by
  simp [su2PositivePlaquetteCost, su2FundamentalRealTrace]

theorem su2_quaternion_real_part_abs_le_one
    (U : SU2PlaquetteHolonomy) :
    -1 ≤ U.a ∧ U.a ≤ 1 := by
  have hb := sq_nonneg U.b
  have hc := sq_nonneg U.c
  have hd := sq_nonneg U.d
  have ha := sq_nonneg U.a
  have hn := U.unit_quaternion
  constructor <;> nlinarith

/-- A genuine SU(2) plaquette costs between zero and two. -/
theorem su2_positive_plaquette_cost_bounds
    (U : SU2PlaquetteHolonomy) :
    0 ≤ su2PositivePlaquetteCost U ∧
      su2PositivePlaquetteCost U ≤ 2 := by
  rw [su2_real_trace_normalization]
  obtain ⟨hlo, hhi⟩ := su2_quaternion_real_part_abs_le_one U
  constructor <;> linarith

/--
The conventional bare SU(2) positive Wilson action uses
β = 4 / g₀² multiplying 1 - Re Tr(U)/2.
This number is different from the T4 symbolic coefficient of a
negative-exponent basis until an explicit source-basis map is proved.
-/
def su2WilsonBeta (bareCoupling : ℝ) : ℝ :=
  4 / bareCoupling ^ 2

theorem su2_wilson_beta_positive
    (bareCoupling : ℝ) (h : bareCoupling ≠ 0) :
    0 < su2WilsonBeta bareCoupling := by
  unfold su2WilsonBeta
  exact div_pos (by norm_num) (sq_pos_of_ne_zero h)

/--
The full finite Wilson action contains an ACTUAL finite plaquette sum;
`holonomy` is to be produced from physical link variables.
-/
def finiteSU2WilsonAction
    {P Ω : Type*}
    (plaquettes : Finset P)
    (holonomy : Ω → P → SU2PlaquetteHolonomy)
    (inverseCouplingCoefficient : ℝ)
    (configuration : Ω) : ℝ :=
  inverseCouplingCoefficient *
    ∑ p ∈ plaquettes,
      su2PositivePlaquetteCost (holonomy configuration p)

/--
Cutoff-explicit energy bounds for the genuine SU(2) Wilson cost.
They show exactly why a fixed-cutoff estimate is NOT automatically a
uniform ultraviolet/infinite-volume coercive estimate: the upper bound
contains the plaquette count and the inverse bare coupling.
-/
theorem finite_su2_wilson_action_bounds
    {P Ω : Type*}
    (plaquettes : Finset P)
    (holonomy : Ω → P → SU2PlaquetteHolonomy)
    (β : ℝ) (hβ : 0 ≤ β) (configuration : Ω) :
    0 ≤ finiteSU2WilsonAction plaquettes holonomy β configuration ∧
    finiteSU2WilsonAction plaquettes holonomy β configuration
      ≤ 2 * β * (plaquettes.card : ℝ) := by
  classical
  have hsumNonnegative :
      0 ≤ ∑ p ∈ plaquettes,
        su2PositivePlaquetteCost (holonomy configuration p) := by
    apply Finset.sum_nonneg
    intro p hp
    exact (su2_positive_plaquette_cost_bounds
      (holonomy configuration p)).1
  have hsumUpper :
      (∑ p ∈ plaquettes,
        su2PositivePlaquetteCost (holonomy configuration p))
        ≤ 2 * (plaquettes.card : ℝ) := by
    calc
      _ ≤ ∑ p ∈ plaquettes, (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact (su2_positive_plaquette_cost_bounds
          (holonomy configuration p)).2
      _ = 2 * (plaquettes.card : ℝ) := by simp
  constructor
  · exact mul_nonneg hβ hsumNonnegative
  · dsimp [finiteSU2WilsonAction]
    have h := mul_le_mul_of_nonneg_left hsumUpper hβ
    nlinarith

/--
Keep the four non-Wilson sectors distinct. Their sum is NOT automatically
gauge invariant, bounded, nonnegative, or a small remainder.
-/
def finiteCMP119SectorAction
    {P Ω : Type*}
    (plaquettes : Finset P)
    (holonomy : Ω → P → SU2PlaquetteHolonomy)
    (β : ℝ)
    (regular rOperation boundary vacuum : Ω → ℝ)
    (configuration : Ω) : ℝ :=
  finiteSU2WilsonAction plaquettes holonomy β configuration +
    regular configuration + rOperation configuration +
    boundary configuration + vacuum configuration

/--
A real source-specific finite lower bound: conditional only on four
separate numerical sector lower estimates, NOT on a guessed
Wilson-only complete action.
-/
theorem finite_cmp119_complete_action_lower_bound
    {P Ω : Type*}
    (plaquettes : Finset P)
    (holonomy : Ω → P → SU2PlaquetteHolonomy)
    (β : ℝ) (hβ : 0 ≤ β)
    (regular rOperation boundary vacuum : Ω → ℝ)
    (Kregular Kr Kboundary Kv : ℝ)
    (hregular : ∀ x, -Kregular ≤ regular x)
    (hr : ∀ x, -Kr ≤ rOperation x)
    (hboundary : ∀ x, -Kboundary ≤ boundary x)
    (hv : ∀ x, -Kv ≤ vacuum x)
    (x : Ω) :
    -(Kregular + Kr + Kboundary + Kv) ≤
      finiteCMP119SectorAction plaquettes holonomy β
        regular rOperation boundary vacuum x := by
  have hWilson := (finite_su2_wilson_action_bounds
    plaquettes holonomy β hβ x).1
  dsimp [finiteCMP119SectorAction]
  linarith [hregular x, hr x, hboundary x, hv x]

/--
The complementary upper estimate on the COMPLETE physical finite action.
One needs independent upper controls on all four selected effective sectors;
the Wilson estimate alone cannot pay these.
-/
theorem finite_cmp119_complete_action_upper_bound
    {P Ω : Type*}
    (plaquettes : Finset P)
    (holonomy : Ω → P → SU2PlaquetteHolonomy)
    (β : ℝ) (hβ : 0 ≤ β)
    (regular rOperation boundary vacuum : Ω → ℝ)
    (Kregular Kr Kboundary Kv : ℝ)
    (hregular : ∀ x, regular x ≤ Kregular)
    (hr : ∀ x, rOperation x ≤ Kr)
    (hboundary : ∀ x, boundary x ≤ Kboundary)
    (hv : ∀ x, vacuum x ≤ Kv)
    (x : Ω) :
    finiteCMP119SectorAction plaquettes holonomy β
      regular rOperation boundary vacuum x ≤
        2 * β * (plaquettes.card : ℝ) +
          Kregular + Kr + Kboundary + Kv := by
  have hWilson := (finite_su2_wilson_action_bounds
    plaquettes holonomy β hβ x).2
  dsimp [finiteCMP119SectorAction]
  linarith [hregular x, hr x, hboundary x, hv x]

/--
The finite Gibbs weight is strictly positive for every SU(2) configuration,
and an explicit bound on all remaining sectors gives a pointwise majorant.
Positivity alone does not establish positive Haar normalization unless the
chosen Haar measure and its support are physically identified.
-/
def finiteCMP119BoltzmannWeight
    {P Ω : Type*}
    (plaquettes : Finset P)
    (holonomy : Ω → P → SU2PlaquetteHolonomy)
    (β : ℝ)
    (regular rOperation boundary vacuum : Ω → ℝ)
    (configuration : Ω) : ℝ :=
  Real.exp (-(finiteCMP119SectorAction plaquettes holonomy β
    regular rOperation boundary vacuum configuration))

theorem finite_cmp119_boltzmann_weight_pos
    {P Ω : Type*}
    (plaquettes : Finset P)
    (holonomy : Ω → P → SU2PlaquetteHolonomy)
    (β : ℝ)
    (regular rOperation boundary vacuum : Ω → ℝ)
    (x : Ω) :
    0 < finiteCMP119BoltzmannWeight plaquettes holonomy β
      regular rOperation boundary vacuum x := by
  exact Real.exp_pos _

theorem finite_cmp119_boltzmann_weight_upper_bound
    {P Ω : Type*}
    (plaquettes : Finset P)
    (holonomy : Ω → P → SU2PlaquetteHolonomy)
    (β : ℝ) (hβ : 0 ≤ β)
    (regular rOperation boundary vacuum : Ω → ℝ)
    (Kregular Kr Kboundary Kv : ℝ)
    (hregular : ∀ x, -Kregular ≤ regular x)
    (hr : ∀ x, -Kr ≤ rOperation x)
    (hboundary : ∀ x, -Kboundary ≤ boundary x)
    (hv : ∀ x, -Kv ≤ vacuum x)
    (x : Ω) :
    finiteCMP119BoltzmannWeight plaquettes holonomy β
      regular rOperation boundary vacuum x
      ≤ Real.exp (Kregular + Kr + Kboundary + Kv) := by
  unfold finiteCMP119BoltzmannWeight
  apply Real.exp_le_exp.mpr
  have h := finite_cmp119_complete_action_lower_bound
    plaquettes holonomy β hβ regular rOperation boundary vacuum
    Kregular Kr Kboundary Kv hregular hr hboundary hv x
  linarith

/--
Finite physical partition function for an explicitly chosen probability
reference measure (intended to be the LINK product Haar measure).

This is a genuine finite-measure positivity result.  The estimate is
cutoff-dependent, and it does NOT assert that a symbolic CMP119 source
weight is equal to the Boltzmann weight used here.
-/
def finiteCMP119Partition
    {P Ω : Type*} [MeasurableSpace Ω]
    (haar : MeasureTheory.ProbabilityMeasure Ω)
    (plaquettes : Finset P)
    (holonomy : Ω → P → SU2PlaquetteHolonomy)
    (β : ℝ)
    (regular rOperation boundary vacuum : Ω → ℝ) : ℝ :=
  ∫ x : Ω,
    finiteCMP119BoltzmannWeight plaquettes holonomy β
      regular rOperation boundary vacuum x
    ∂((haar : MeasureTheory.ProbabilityMeasure Ω) :
        MeasureTheory.Measure Ω)

/--
A measurable, bounded-below complete selected finite action has
a positive, finite, explicitly bounded partition function with respect
to ANY normalized nonzero reference measure, including product Haar.

Four independent sector lower bounds are visible.  Their possible
volume/UV dependence is NOT eliminated by this theorem; bounding those
dependences is precisely the next physical RG estimate.
-/
theorem finite_cmp119_partition_positive_and_bounded
    {P Ω : Type*} [MeasurableSpace Ω]
    (haar : MeasureTheory.ProbabilityMeasure Ω)
    (plaquettes : Finset P)
    (holonomy : Ω → P → SU2PlaquetteHolonomy)
    (β : ℝ) (hβ : 0 ≤ β)
    (regular rOperation boundary vacuum : Ω → ℝ)
    (Kregular Kr Kboundary Kv : ℝ)
    (hregular : ∀ x, -Kregular ≤ regular x)
    (hr : ∀ x, -Kr ≤ rOperation x)
    (hboundary : ∀ x, -Kboundary ≤ boundary x)
    (hv : ∀ x, -Kv ≤ vacuum x)
    (hMeasurable :
      Measurable (finiteCMP119BoltzmannWeight plaquettes
        holonomy β regular rOperation boundary vacuum)) :
    0 < finiteCMP119Partition haar plaquettes holonomy β
      regular rOperation boundary vacuum ∧
    finiteCMP119Partition haar plaquettes holonomy β
      regular rOperation boundary vacuum
      ≤ Real.exp (Kregular + Kr + Kboundary + Kv) := by
  let μ : MeasureTheory.Measure Ω := haar
  let w : Ω → ℝ :=
    finiteCMP119BoltzmannWeight plaquettes holonomy β
      regular rOperation boundary vacuum
  let K : ℝ := Kregular + Kr + Kboundary + Kv
  have hwBound : ∀ x, w x ≤ Real.exp K := by
    intro x
    exact finite_cmp119_boltzmann_weight_upper_bound
      plaquettes holonomy β hβ regular rOperation boundary vacuum
      Kregular Kr Kboundary Kv hregular hr hboundary hv x
  have hwNonnegative : ∀ x, 0 ≤ w x := by
    intro x
    exact (finite_cmp119_boltzmann_weight_pos
      plaquettes holonomy β regular rOperation boundary vacuum x).le
  have hwAbs : ∀ x, ‖w x‖ ≤ Real.exp K := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hwNonnegative x)]
    exact hwBound x
  have hwIntegrable : MeasureTheory.Integrable w μ :=
    MeasureTheory.Integrable.of_bound
      hMeasurable.aestronglyMeasurable
      (Real.exp K)
      (Filter.Eventually.of_forall hwAbs)
  have hPositive : 0 < ∫ x, w x ∂μ := by
    have hSupport : Function.support w = Set.univ := by
      ext x
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact ne_of_gt (finite_cmp119_boltzmann_weight_pos
        plaquettes holonomy β regular rOperation boundary vacuum x)
    apply (MeasureTheory.integral_pos_iff_support_of_nonneg
      hwNonnegative hwIntegrable).2
    rw [hSupport]
    simp [μ]
  have hUpper : (∫ x, w x ∂μ) ≤ Real.exp K := by
    calc
      ∫ x, w x ∂μ ≤ ∫ _ : Ω, Real.exp K ∂μ :=
        MeasureTheory.integral_mono hwIntegrable
          (MeasureTheory.integrable_const _) hwBound
      _ = Real.exp K := by simp [μ]
  constructor
  · exact hPositive
  · exact hUpper


/-!
## Explicit nonzero plaquette probe and orientation calibration

The central quaternion -I has normalized Wilson cost exactly 2. This
provides a genuine SU(2) *holonomy* probe for uniqueness of a coefficient
in the literal Gibbs exponent. It is not yet a proof that the selected
CMP119 link/plaquette configuration and renormalized effective action use
this specific holonomy and exponent.
-/

/-- A genuine, nontrivial SU(2) element: central holonomy -I. -/
def su2NegativeIdentity : SU2PlaquetteHolonomy where
  a := -1
  b := 0
  c := 0
  d := 0
  unit_quaternion := by norm_num

theorem su2_negative_identity_plaquette_cost :
    su2PositivePlaquetteCost su2NegativeIdentity = 2 := by
  norm_num [su2PositivePlaquetteCost, su2FundamentalRealTrace,
    su2NegativeIdentity]

theorem su2_negative_identity_cost_strictly_positive :
    0 < su2PositivePlaquetteCost su2NegativeIdentity := by
  rw [su2_negative_identity_plaquette_cost]
  norm_num

/--
An actual nonzero SU(2) probe identifies the signed Wilson coefficient
from equality with the literal negative Gibbs action, without assuming the
conclusion c = -u or introducing an arbitrary normalized action basis.
-/
theorem su2_literal_exponent_probe_determines_coefficient
    (sourceCoefficient inverseSquare : ℝ)
    (hExponent :
      sourceCoefficient * su2PositivePlaquetteCost su2NegativeIdentity
        = -(inverseSquare * su2PositivePlaquetteCost su2NegativeIdentity)) :
    sourceCoefficient = -inverseSquare := by
  rw [su2_negative_identity_plaquette_cost] at hExponent
  linarith

/--
On precisely the same normalized positive Wilson cost, the standard
SU(2) bare coefficient 4/g₀² and T4's unit coefficient u agree only when
u = 4/g₀². This does not equate the bare and renormalized couplings.
-/
theorem su2_bare_vs_t4_coefficient_from_probe
    (t4Inverse bareInverse : ℝ)
    (hSameAction :
      t4Inverse * su2PositivePlaquetteCost su2NegativeIdentity
        = (4 * bareInverse) *
          su2PositivePlaquetteCost su2NegativeIdentity) :
    t4Inverse = 4 * bareInverse := by
  rw [su2_negative_identity_plaquette_cost] at hSameAction
  linarith

end RequestProject.YangMills
