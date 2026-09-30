import Mathlib
import YangMills.LiteralSU2FiniteWilson

/-!
# Actual four-dimensional periodic SU(2) lattice links and plaquettes

The finite configuration is a function from oriented 4D torus links
to unit quaternions, rather than an independently selected family of
plaquette holonomies.  The Wilson action from LiteralSU2FiniteWilson
is therefore evaluated on the canonical ordered plaquette holonomy
U(x,μ) U(x+μ,ν) U(x+ν,μ)⁻¹ U(x,ν)⁻¹.

Proved here: unit-quaternion group algebra, quaternion real-trace
cyclicity, commuting coordinate shifts, gauge-covariant plaquette
transport, and gauge invariance of every positive trace-normalized
plaquette cost.  No continuum, source RG, or reflection positivity is
claimed.  The source CMP119 action still requires an independently
proved identity to this exact finite-link presentation.
-/

namespace RequestProject.YangMills

private def su2Mul (x y : SU2PlaquetteHolonomy) :
    SU2PlaquetteHolonomy :=
  ⟨x.a*y.a - x.b*y.b - x.c*y.c - x.d*y.d,
   x.a*y.b + x.b*y.a + x.c*y.d - x.d*y.c,
   x.a*y.c - x.b*y.d + x.c*y.a + x.d*y.b,
   x.a*y.d + x.b*y.c - x.c*y.b + x.d*y.a,
   by
    have hNorm :
        (x.a*y.a - x.b*y.b - x.c*y.c - x.d*y.d)^2 +
        (x.a*y.b + x.b*y.a + x.c*y.d - x.d*y.c)^2 +
        (x.a*y.c - x.b*y.d + x.c*y.a + x.d*y.b)^2 +
        (x.a*y.d + x.b*y.c - x.c*y.b + x.d*y.a)^2 =
        (x.a^2 + x.b^2 + x.c^2 + x.d^2) *
          (y.a^2 + y.b^2 + y.c^2 + y.d^2) := by ring
    rw [x.unit_quaternion, y.unit_quaternion] at hNorm
    simpa using hNorm⟩

private def su2One : SU2PlaquetteHolonomy :=
  ⟨1,0,0,0,by norm_num⟩

private def su2Inv (x : SU2PlaquetteHolonomy) :
    SU2PlaquetteHolonomy :=
  ⟨x.a,-x.b,-x.c,-x.d, by
    have h : x.a^2 + (-x.b)^2 + (-x.c)^2 + (-x.d)^2 =
        x.a^2 + x.b^2 + x.c^2 + x.d^2 := by ring
    rw [h, x.unit_quaternion]⟩

instance : Mul SU2PlaquetteHolonomy := ⟨su2Mul⟩
instance : One SU2PlaquetteHolonomy := ⟨su2One⟩
instance : Inv SU2PlaquetteHolonomy := ⟨su2Inv⟩

@[ext] theorem su2_holonomy_ext (x y : SU2PlaquetteHolonomy)
    (ha : x.a = y.a)
    (hb : x.b = y.b)
    (hc : x.c = y.c)
    (hd : x.d = y.d) : x = y := by
  cases x with
  | mk a b c d normx =>
    cases y with
    | mk a' b' c' d' normy =>
      dsimp at ha hb hc hd
      subst a'
      subst b'
      subst c'
      subst d'
      rfl

private theorem su2_mul_assoc (x y z : SU2PlaquetteHolonomy) :
    (x * y) * z = x * (y * z) := by
  apply su2_holonomy_ext <;>
    dsimp [HMul.hMul, Mul.mul, su2Mul] <;> ring

private theorem su2_one_mul (x : SU2PlaquetteHolonomy) :
    1 * x = x := by
  apply su2_holonomy_ext <;>
    dsimp [HMul.hMul, Mul.mul, One.one, su2Mul, su2One] <;> ring

private theorem su2_inv_mul_cancel (x : SU2PlaquetteHolonomy) :
    x⁻¹ * x = 1 := by
  apply su2_holonomy_ext <;>
    dsimp [HMul.hMul, Mul.mul, Inv.inv, One.one,
      su2Mul, su2Inv, su2One] <;>
    nlinarith [x.unit_quaternion]

instance : Group SU2PlaquetteHolonomy :=
  Group.ofLeftAxioms su2_mul_assoc su2_one_mul su2_inv_mul_cancel

/-- Real fundamental trace is a cyclic invariant of unit-quaternion multiplication. -/
theorem su2_real_trace_cyclic (x y : SU2PlaquetteHolonomy) :
    (x * y).a = (y * x).a := by
  dsimp [HMul.hMul, Mul.mul, su2Mul]
  ring

/-- SU(2) plaquette cost is invariant under conjugation. -/
theorem su2_plaquette_cost_conjugation
    (g U : SU2PlaquetteHolonomy) :
    su2PositivePlaquetteCost (g * U * g⁻¹) =
      su2PositivePlaquetteCost U := by
  simp only [su2_real_trace_normalization]
  have htrace :
      (g * U * g⁻¹).a = U.a := by
    calc
      (g * U * g⁻¹).a = (g⁻¹ * (g * U)).a :=
        su2_real_trace_cyclic (g * U) (g⁻¹)
      _ = ((g⁻¹ * g) * U).a := by rw [mul_assoc]
      _ = U.a := by simp
  rw [htrace]

/-- Sites of the discrete four-dimensional periodic torus. -/
abbrev SU2TorusSite (L : ℕ) := Fin 4 → ZMod L

/-- One positive unit shift in the selected 4D coordinate. -/
def su2Shift {L : ℕ}
    (x : SU2TorusSite L) (direction : Fin 4) : SU2TorusSite L :=
  Function.update x direction (x direction + 1)

/-- A full four-dimensional lattice link configuration. -/
abbrev SU2TorusLinks (L : ℕ) :=
  SU2TorusSite L → Fin 4 → SU2PlaquetteHolonomy

/-- A gauge transformation assigns a unitary at each 4D lattice vertex. -/
abbrev SU2TorusGauge (L : ℕ) :=
  SU2TorusSite L → SU2PlaquetteHolonomy

/--
Coordinate shifts commute on the hypercubic periodic lattice.  This
elementary geometric fact is essential for the corner cancellation
in gauge covariance of a plaquette.
-/
theorem su2_shift_commute {L : ℕ}
    (x : SU2TorusSite L) (μ ν : Fin 4) :
    su2Shift (su2Shift x μ) ν =
      su2Shift (su2Shift x ν) μ := by
  classical
  by_cases h : μ = ν
  · subst ν
    rfl
  · funext i
    by_cases hiμ : i = μ
    · subst i
      have hνμ : ν ≠ μ := Ne.symm h
      simp [su2Shift, Function.update_same,
        Function.update_noteq hνμ, h]
    · by_cases hiν : i = ν
      · subst i
        simp [su2Shift, Function.update_same,
          Function.update_noteq hiμ, h]
      · simp [su2Shift, Function.update_noteq hiμ,
          Function.update_noteq hiν]

/-- Standard local SU(2) gauge action on an oriented lattice link. -/
def su2GaugeTransform {L : ℕ}
    (g : SU2TorusGauge L) (links : SU2TorusLinks L) :
    SU2TorusLinks L :=
  fun x μ => g x * links x μ * (g (su2Shift x μ))⁻¹

/-- The ordered, positively oriented 4D plaquette holonomy. -/
def su2Plaquette {L : ℕ}
    (links : SU2TorusLinks L)
    (x : SU2TorusSite L) (μ ν : Fin 4) :
    SU2PlaquetteHolonomy :=
  links x μ * links (su2Shift x μ) ν *
    (links (su2Shift x ν) μ)⁻¹ * (links x ν)⁻¹

/--
The plaquette of the transformed links is conjugated by the gauge
element at its initial vertex.  All intermediate gauge matrices
cancel using exact four-dimensional lattice shift geometry.
-/
theorem su2_plaquette_gauge_covariance {L : ℕ}
    (g : SU2TorusGauge L) (links : SU2TorusLinks L)
    (x : SU2TorusSite L) (μ ν : Fin 4) :
    su2Plaquette (su2GaugeTransform g links) x μ ν =
      g x * su2Plaquette links x μ ν * (g x)⁻¹ := by
  have hSquare := su2_shift_commute x μ ν
  dsimp [su2Plaquette, su2GaugeTransform]
  rw [hSquare]
  group

/-- Exact gauge invariance of the Wilson cost on each physical lattice plaquette. -/
theorem su2_plaquette_wilson_cost_gauge_invariant {L : ℕ}
    (g : SU2TorusGauge L) (links : SU2TorusLinks L)
    (x : SU2TorusSite L) (μ ν : Fin 4) :
    su2PositivePlaquetteCost
        (su2Plaquette (su2GaugeTransform g links) x μ ν) =
      su2PositivePlaquetteCost (su2Plaquette links x μ ν) := by
  rw [su2_plaquette_gauge_covariance]
  exact su2_plaquette_cost_conjugation _ _

/--
The full physical plaquette index is a four-dimensional site and an
ordered pair of directions.  Using μ<ν avoids double-counting opposite
orientations.
-/
def su2FourDimensionalPlaquettes (L : ℕ) [NeZero L] :
    Finset (SU2TorusSite L × Fin 4 × Fin 4) :=
  Finset.univ.filter (fun p => p.2.1 < p.2.2)

/-- Wilson action on the real lattice link field, not on arbitrary plaquette data. -/
def su2FourDimensionalWilsonAction (L : ℕ) [NeZero L]
    (links : SU2TorusLinks L) (β : ℝ) : ℝ :=
  finiteSU2WilsonAction
    (su2FourDimensionalPlaquettes L)
    (fun links p => su2Plaquette links p.1 p.2.1 p.2.2)
    β links

theorem su2_four_dimensional_wilson_action_gauge_invariant
    (L : ℕ) [NeZero L] (g : SU2TorusGauge L)
    (links : SU2TorusLinks L) (β : ℝ) :
    su2FourDimensionalWilsonAction L (su2GaugeTransform g links) β =
      su2FourDimensionalWilsonAction L links β := by
  classical
  dsimp [su2FourDimensionalWilsonAction, finiteSU2WilsonAction]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  exact su2_plaquette_wilson_cost_gauge_invariant
    g links p.1 p.2.1 p.2.2

/--
Actual 4D finite Wilson estimate, now using a link-derived plaquette
field.  It is finite-volume/cutoff explicit, NOT uniform along UV flow.
-/
theorem su2_four_dimensional_wilson_action_bounds
    (L : ℕ) [NeZero L] (links : SU2TorusLinks L) (β : ℝ) (hβ : 0 ≤ β) :
    0 ≤ su2FourDimensionalWilsonAction L links β ∧
      su2FourDimensionalWilsonAction L links β
        ≤ 2 * β * ((su2FourDimensionalPlaquettes L).card : ℝ) := by
  exact finite_su2_wilson_action_bounds
    (su2FourDimensionalPlaquettes L)
    (fun links p => su2Plaquette links p.1 p.2.1 p.2.2)
    β hβ links

/--
Two adjacent physical links blocked into a path of length two.
This is the natural group-valued RG blocking operation, not an
arithmetic average of plaquette coefficients.
-/
def su2TwoLinkBlock {L : ℕ}
    (links : SU2TorusLinks L)
    (x : SU2TorusSite L) (direction : Fin 4) :
    SU2PlaquetteHolonomy :=
  links x direction *
    links (su2Shift x direction) direction

/--
The blocked link has the proper endpoint gauge covariance under the
SAME fine-lattice gauge action.  Intermediate site gauge factors
cancel exactly.  This is the required local geometry for comparing
physical fine/coarse link fields in an RG trajectory.
-/
theorem su2_two_link_block_gauge_covariant {L : ℕ}
    (g : SU2TorusGauge L) (links : SU2TorusLinks L)
    (x : SU2TorusSite L) (direction : Fin 4) :
    su2TwoLinkBlock (su2GaugeTransform g links) x direction =
      g x * su2TwoLinkBlock links x direction *
        (g (su2Shift (su2Shift x direction) direction))⁻¹ := by
  dsimp [su2TwoLinkBlock, su2GaugeTransform]
  group

/-- Fundamental central negative unit of the genuine quaternion SU(2). -/
def su2CentralNegative : SU2PlaquetteHolonomy :=
  ⟨-1, 0, 0, 0, by norm_num⟩

theorem su2_negative_unit_cost :
    su2PositivePlaquetteCost su2CentralNegative = 2 := by
  norm_num [su2_real_trace_normalization, su2CentralNegative]

theorem su2_negative_units_multiply_to_identity :
    su2CentralNegative * su2CentralNegative =
      (1 : SU2PlaquetteHolonomy) := by
  apply su2_holonomy_ext <;>
    norm_num [su2CentralNegative, Mul.mul, su2Mul,
      One.one, su2One]

/--
Explicit finite nonlinear obstruction: Wilson cost is NOT additive
when two group-valued plaquette holonomies are multiplied.  A two-step
block containing -I and -I is the identity, with cost zero, while the
two original costs sum to four.  Thus a CMP119 RG action cannot be
obtained simply by summing Wilson terms across blocking scales.
-/
theorem su2_wilson_cost_not_additive_under_blocking :
    su2PositivePlaquetteCost
      (su2CentralNegative * su2CentralNegative) ≠
      su2PositivePlaquetteCost su2CentralNegative +
        su2PositivePlaquetteCost su2CentralNegative := by
  rw [su2_negative_units_multiply_to_identity,
    su2_negative_unit_cost]
  norm_num [su2PositivePlaquetteCost, su2FundamentalRealTrace,
    One.one, su2One]

/--
A physical one-plaquette source normalization probe, independent of the
T4 abstract plaquette projector: evaluate the actual normalized trace at
the central negative SU(2) element.
-/
theorem physical_su2_central_probe_extracts_two_beta (β : ℝ) :
    β * su2PositivePlaquetteCost su2CentralNegative = 2 * β := by
  rw [su2_negative_unit_cost]
  ring

/--
Two candidate Wilson normalizations which agree on the actual -I
plaquette must have the same coefficient, without any symbolic
projector assumption.
-/
theorem physical_su2_wilson_normalization_unique
    (β γ : ℝ)
    (hSamePhysicalProbe :
      β * su2PositivePlaquetteCost su2CentralNegative =
      γ * su2PositivePlaquetteCost su2CentralNegative) :
    β = γ := by
  rw [su2_negative_unit_cost] at hSamePhysicalProbe
  linarith

/--
The independent regular/R/boundary/vacuum sector changes must be
subtracted before claiming the Wilson coefficient has been measured.
This theorem returns a SOURCE-CHECKABLE equality for the physical
nonlinear plaquette rather than assuming total action = Wilson action.
-/
theorem physical_su2_complete_action_coefficient_probe
    (β : ℝ) (regular rOperation boundary vacuum :
      SU2PlaquetteHolonomy → ℝ) :
    β * su2PositivePlaquetteCost su2CentralNegative +
        regular su2CentralNegative +
        rOperation su2CentralNegative +
        boundary su2CentralNegative +
        vacuum su2CentralNegative -
        (regular su2CentralNegative +
        rOperation su2CentralNegative +
        boundary su2CentralNegative +
        vacuum su2CentralNegative) = 2 * β := by
  rw [su2_negative_unit_cost]
  ring

/--
The complete finite four-dimensional action includes E/R/boundary/vacuum
as separate source terms, evaluated on actual link configurations.
-/
def su2FourDimensionalCompleteAction (L : ℕ) [NeZero L]
    (links : SU2TorusLinks L) (β : ℝ)
    (regular rOperation boundary vacuum : SU2TorusLinks L → ℝ) : ℝ :=
  su2FourDimensionalWilsonAction L links β +
    regular links + rOperation links + boundary links + vacuum links

/--
A complete effective source is gauge invariant if its four NON-WILSON
terms are gauge invariant on the actual link carrier.  Gauge
invariance of the Wilson term alone cannot establish this conclusion.
-/
theorem su2_complete_action_gauge_invariant
    (L : ℕ) [NeZero L] (g : SU2TorusGauge L)
    (links : SU2TorusLinks L) (β : ℝ)
    (regular rOperation boundary vacuum : SU2TorusLinks L → ℝ)
    (hRegular : regular (su2GaugeTransform g links) = regular links)
    (hR : rOperation (su2GaugeTransform g links) = rOperation links)
    (hBoundary : boundary (su2GaugeTransform g links) = boundary links)
    (hVacuum : vacuum (su2GaugeTransform g links) = vacuum links) :
    su2FourDimensionalCompleteAction L
      (su2GaugeTransform g links) β regular rOperation boundary vacuum =
    su2FourDimensionalCompleteAction L
      links β regular rOperation boundary vacuum := by
  simp only [su2FourDimensionalCompleteAction,
    su2_four_dimensional_wilson_action_gauge_invariant,
    hRegular, hR, hBoundary, hVacuum]

/--
Gauge invariance passes to the real full Gibbs density, without dropping
any effective sector or assuming a particular CMP119 plaquette projector.
-/
theorem su2_complete_gibbs_density_gauge_invariant
    (L : ℕ) [NeZero L] (g : SU2TorusGauge L)
    (links : SU2TorusLinks L) (β : ℝ)
    (regular rOperation boundary vacuum : SU2TorusLinks L → ℝ)
    (hRegular : regular (su2GaugeTransform g links) = regular links)
    (hR : rOperation (su2GaugeTransform g links) = rOperation links)
    (hBoundary : boundary (su2GaugeTransform g links) = boundary links)
    (hVacuum : vacuum (su2GaugeTransform g links) = vacuum links) :
    Real.exp (-(su2FourDimensionalCompleteAction L
      (su2GaugeTransform g links) β regular rOperation boundary vacuum)) =
    Real.exp (-(su2FourDimensionalCompleteAction L
      links β regular rOperation boundary vacuum)) := by
  rw [su2_complete_action_gauge_invariant
    L g links β regular rOperation boundary vacuum
    hRegular hR hBoundary hVacuum]

end RequestProject.YangMills
