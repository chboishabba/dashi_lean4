import Mathlib.Tactic

/-!
# Whitney umbrella and Simons cone: exact algebraic realisations

Source roots: Whitney's pinch-point/umbrella model, and the classical
Simons cone (whose area-minimising property was proved by Bombieri,
De Giorgi and Giusti).

This file proves polynomial identities and a spherical-link equivalence
on actual real-coordinate carriers. It does NOT prove:
* a Whitney surface is an embedded 2-manifold;
* a general Whitney stratification theorem;
* the Simons cone is area-minimising (geometric measure theory);
* identity with the separately constructed Agda coordinate fixtures.

No surrogate CW library is introduced.
-/

namespace Synthesis.ExoticTopology

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ
deriving DecidableEq

def whitneyParam (u v : ℝ) : Point3 :=
  ⟨u * v, u, v ^ 2⟩

def whitneyPolynomial (p : Point3) : ℝ :=
  p.x ^ 2 - p.y ^ 2 * p.z

theorem whitneyPolynomial_param (u v : ℝ) :
    whitneyPolynomial (whitneyParam u v) = 0 := by
  dsimp [whitneyPolynomial, whitneyParam]
  ring

theorem whitneyParam_z_nonneg (u v : ℝ) :
    0 ≤ (whitneyParam u v).z := by
  dsimp [whitneyParam]
  positivity

/-- The parametrised REAL image is contained in the correct semialgebraic
    half of the implicit algebraic variety. In particular a negative-z
    point of the algebraic zero locus cannot be represented by this map. -/
theorem whitneyImage_necessary (u v : ℝ) :
    whitneyPolynomial (whitneyParam u v) = 0 ∧
      0 ≤ (whitneyParam u v).z :=
  ⟨whitneyPolynomial_param u v, whitneyParam_z_nonneg u v⟩

/-- A nonzero negative-z point on the formal axis satisfies the implicit
    equation but cannot occur as a real parametric image. -/
theorem whitney_negative_axis_is_spurious (z : ℝ) (hz : z < 0) :
    whitneyPolynomial ⟨0, 0, z⟩ = 0 ∧
      ¬ ∃ u v : ℝ, whitneyParam u v = ⟨0, 0, z⟩ := by
  constructor
  · simp [whitneyPolynomial]
  · rintro ⟨u, v, heq⟩
    have hzEq : (whitneyParam u v).z = z := congrArg Point3.z heq
    have hnonneg := whitneyParam_z_nonneg u v
    linarith

/-- Simons cone: R⁴ × R⁴ with equal squared Euclidean radii. -/
def normSq4 (x : Fin 4 → ℝ) : ℝ :=
  ∑ i, (x i) ^ 2

def simonsCone (x y : Fin 4 → ℝ) : Prop :=
  normSq4 x = normSq4 y

/-- The spherical link is precisely the product of two radius-1/√2
    3-spheres: each of the two squared radii is exactly 1/2.
    This theorem is algebraic and does not establish area minimality. -/
theorem simonsCone_unitLink
    (x y : Fin 4 → ℝ)
    (hunit : normSq4 x + normSq4 y = 1) :
    simonsCone x y ↔
      normSq4 x = (1 / 2 : ℝ) ∧ normSq4 y = (1 / 2 : ℝ) := by
  constructor
  · intro heq
    dsimp [simonsCone] at heq
    constructor <;> linarith
  · rintro ⟨hx, hy⟩
    dsimp [simonsCone]
    linarith

theorem simonsCone_vertex :
    simonsCone (fun _ : Fin 4 => (0 : ℝ))
      (fun _ : Fin 4 => (0 : ℝ)) := by
  simp [simonsCone, normSq4]

end Synthesis.ExoticTopology
