import Mathlib
import YangMills.LiteralSU2FourDimensionalLattice

/-!
# 4D finite Yang--Mills geometry for an arbitrary gauge group

This is the group-generic version of the *actual link and plaquette*
geometry previously implemented for unit-quaternion SU(2).

The lattice and orientation are fixed. The gauge group is a Mathlib
`Group`, so central quotients and different global forms are not
silently identified with their simply connected covers. Any class
function invariant under conjugation gives a gauge-invariant finite
plaquette observable. Quantitative class-function bounds then imply
cutoff-explicit bounds on its Wilson action.

The theorem is algebraic for *all groups*, hence also valid for every
compact simple group once instantiated.  It does NOT show that each
group admits the required gauge-invariant reference Haar integration,
uniform RG bounds, OS positivity, a continuum QFT or a mass gap.
These remain the H5 physical obligations.
-/

namespace RequestProject.YangMills

abbrev FourDimensionalTorusSite (L : ℕ) := Fin 4 → ZMod L

def fourDimensionalShift {L : ℕ}
    (x : FourDimensionalTorusSite L) (direction : Fin 4) :
    FourDimensionalTorusSite L :=
  Function.update x direction (x direction + 1)

abbrev FourDimensionalGroupLinks (G : Type*) [Group G] (L : ℕ) :=
  FourDimensionalTorusSite L → Fin 4 → G

abbrev FourDimensionalGroupGauge (G : Type*) [Group G] (L : ℕ) :=
  FourDimensionalTorusSite L → G

def fourDimensionalGaugeTransform
    {G : Type*} [Group G] {L : ℕ}
    (g : FourDimensionalGroupGauge G L)
    (links : FourDimensionalGroupLinks G L) :
    FourDimensionalGroupLinks G L :=
  fun x μ => g x * links x μ * (g (fourDimensionalShift x μ))⁻¹

theorem four_dimensional_shift_commute {L : ℕ}
    (x : FourDimensionalTorusSite L) (μ ν : Fin 4) :
    fourDimensionalShift (fourDimensionalShift x μ) ν =
    fourDimensionalShift (fourDimensionalShift x ν) μ := by
  exact su2_shift_commute x μ ν

def fourDimensionalPlaquette
    {G : Type*} [Group G] {L : ℕ}
    (links : FourDimensionalGroupLinks G L)
    (x : FourDimensionalTorusSite L) (μ ν : Fin 4) : G :=
  links x μ * links (fourDimensionalShift x μ) ν *
    (links (fourDimensionalShift x ν) μ)⁻¹ * (links x ν)⁻¹

theorem four_dimensional_plaquette_gauge_covariant
    {G : Type*} [Group G] {L : ℕ}
    (g : FourDimensionalGroupGauge G L)
    (links : FourDimensionalGroupLinks G L)
    (x : FourDimensionalTorusSite L) (μ ν : Fin 4) :
    fourDimensionalPlaquette (fourDimensionalGaugeTransform g links)
      x μ ν =
    g x * fourDimensionalPlaquette links x μ ν * (g x)⁻¹ := by
  have hSquare := four_dimensional_shift_commute x μ ν
  dsimp [fourDimensionalPlaquette, fourDimensionalGaugeTransform]
  rw [hSquare]
  group

def fourDimensionalPlaquetteSet (L : ℕ) [NeZero L] :
    Finset (FourDimensionalTorusSite L × Fin 4 × Fin 4) :=
  Finset.univ.filter (fun p => p.2.1 < p.2.2)

/--
A conjugacy-invariant real class cost.  For compact G, the standard
Wilson choice is built from the REAL normalized trace of an actual
unitary representation, not an arbitrary symbolic action projector.
-/
def fourDimensionalClassAction
    {G : Type*} [Group G] (L : ℕ) [NeZero L]
    (classCost : G → ℝ)
    (links : FourDimensionalGroupLinks G L)
    (β : ℝ) : ℝ :=
  β * ∑ p ∈ fourDimensionalPlaquetteSet L,
    classCost (fourDimensionalPlaquette links p.1 p.2.1 p.2.2)

/--
Source-independent gauge invariance of every actual 4D finite-link
class function, valid also for non-simply-connected compact simple G.
-/
theorem four_dimensional_class_action_gauge_invariant
    {G : Type*} [Group G]
    (L : ℕ) [NeZero L] (classCost : G → ℝ)
    (hClass : ∀ (g U : G),
      classCost (g * U * g⁻¹) = classCost U)
    (g : FourDimensionalGroupGauge G L)
    (links : FourDimensionalGroupLinks G L) (β : ℝ) :
    fourDimensionalClassAction L classCost
      (fourDimensionalGaugeTransform g links) β =
    fourDimensionalClassAction L classCost links β := by
  classical
  unfold fourDimensionalClassAction
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [four_dimensional_plaquette_gauge_covariant]
  exact hClass _ _

/--
Only class-function bounds and nonnegative beta are needed to
produce the full finite-volume Wilson-action bound. In particular,
the finite geometric estimate is not the all-G continuum/RG theorem.
-/
theorem four_dimensional_class_action_bounds
    {G : Type*} [Group G]
    (L : ℕ) [NeZero L] (classCost : G → ℝ)
    (hCost : ∀ U : G, 0 ≤ classCost U ∧ classCost U ≤ 2)
    (links : FourDimensionalGroupLinks G L)
    (β : ℝ) (hβ : 0 ≤ β) :
    0 ≤ fourDimensionalClassAction L classCost links β ∧
    fourDimensionalClassAction L classCost links β ≤
      2 * β * ((fourDimensionalPlaquetteSet L).card : ℝ) := by
  classical
  have hLower :
      0 ≤ ∑ p ∈ fourDimensionalPlaquetteSet L,
        classCost (fourDimensionalPlaquette links p.1 p.2.1 p.2.2) := by
    apply Finset.sum_nonneg
    intro p hp
    exact (hCost _).1
  have hUpper :
      (∑ p ∈ fourDimensionalPlaquetteSet L,
        classCost (fourDimensionalPlaquette links p.1 p.2.1 p.2.2)) ≤
        2 * ((fourDimensionalPlaquetteSet L).card : ℝ) := by
    calc
      _ ≤ ∑ p ∈ fourDimensionalPlaquetteSet L, (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact (hCost _).2
      _ = 2 * ((fourDimensionalPlaquetteSet L).card : ℝ) := by simp
  constructor
  · exact mul_nonneg hβ hLower
  · unfold fourDimensionalClassAction
    have hb := mul_le_mul_of_nonneg_left hUpper hβ
    nlinarith

end RequestProject.YangMills
