import Mathlib

/-!
# Miller's projected-vorticity geometry: exact finite three-vector carrier

Classical algebra: the Lagrange cross-product identity in R³. It is not a
novel result of Evan Miller or of DASHI. Reconstructed as a finite
lemma usable when checking the geometric meaning of the projection
appearing in Evan Miller, "A Locally Anisotropic Regularity Criterion for
the Navier–Stokes Equation in Terms of Vorticity", Proc. AMS Series B 8
(2021), 60–74, DOI 10.1090/bproc/74, Theorem 1.6.

The source's projected vorticity is v × omega (the component in the
plane perpendicular to the unit vector v). This file proves its square
is |omega|²-(v·omega)², and that it has no more squared magnitude than
the full vorticity. A true L^4_t L²_x estimate on a SAME continuous NS
solution, a spacetime gradient bound on v, the continuum norm identity,
and the continuation theorem remain unproved here. These are algebraic
scalar coordinates, not physical analytic norm constructions.
-/

namespace RequestProject.NavierStokes.MillerProjectionGeometry

def cross1 (v₁ v₂ v₃ w₁ w₂ w₃ : ℝ) : ℝ := v₂ * w₃ - v₃ * w₂
def cross2 (v₁ v₂ v₃ w₁ w₂ w₃ : ℝ) : ℝ := v₃ * w₁ - v₁ * w₃
def cross3 (v₁ v₂ v₃ w₁ w₂ w₃ : ℝ) : ℝ := v₁ * w₂ - v₂ * w₁

def dot (v₁ v₂ v₃ w₁ w₂ w₃ : ℝ) : ℝ :=
  v₁ * w₁ + v₂ * w₂ + v₃ * w₃

def normSq (a b c : ℝ) : ℝ := a ^ 2 + b ^ 2 + c ^ 2

def crossNormSq (v₁ v₂ v₃ w₁ w₂ w₃ : ℝ) : ℝ :=
  normSq
    (cross1 v₁ v₂ v₃ w₁ w₂ w₃)
    (cross2 v₁ v₂ v₃ w₁ w₂ w₃)
    (cross3 v₁ v₂ v₃ w₁ w₂ w₃)

/-- The classical Lagrange identity in explicit 3-coordinate arithmetic. -/
theorem cross_normSq_lagrange
    (v₁ v₂ v₃ w₁ w₂ w₃ : ℝ) :
    crossNormSq v₁ v₂ v₃ w₁ w₂ w₃ =
      normSq v₁ v₂ v₃ * normSq w₁ w₂ w₃ -
        dot v₁ v₂ v₃ w₁ w₂ w₃ ^ 2 := by
  unfold crossNormSq cross1 cross2 cross3 normSq dot
  ring

/-- For a *pointwise* unit direction, the projected square is the
total vorticity square less its component along the direction. -/
theorem unit_direction_projected_square
    (v₁ v₂ v₃ w₁ w₂ w₃ : ℝ)
    (hUnit : normSq v₁ v₂ v₃ = 1) :
    crossNormSq v₁ v₂ v₃ w₁ w₂ w₃ =
      normSq w₁ w₂ w₃ -
        dot v₁ v₂ v₃ w₁ w₂ w₃ ^ 2 := by
  rw [cross_normSq_lagrange, hUnit]
  ring

/-- Pointwise domination is free; the required scale-critical spacetime
estimate DOES NOT follow unless the whole-vorticity spacetime norm is
already controlled. This fact must not be used in a circular BKM proof. -/
theorem unit_direction_projected_le_total
    (v₁ v₂ v₃ w₁ w₂ w₃ : ℝ)
    (hUnit : normSq v₁ v₂ v₃ = 1) :
    crossNormSq v₁ v₂ v₃ w₁ w₂ w₃ ≤
      normSq w₁ w₂ w₃ := by
  rw [unit_direction_projected_square _ _ _ _ _ _ hUnit]
  have hNonnegative :
      0 ≤ dot v₁ v₂ v₃ w₁ w₂ w₃ ^ 2 := sq_nonneg _
  linarith

/-- A unit z-normal projects onto the fixed xy-plane. This is the
finite geometric case of Chae–Choe's fixed-plane predecessor and of
Miller's locally varying plane; neither source theorem is re-proved. -/
theorem constant_z_plane_formula (w₁ w₂ w₃ : ℝ) :
    crossNormSq 0 0 1 w₁ w₂ w₃ = w₁ ^ 2 + w₂ ^ 2 := by
  unfold crossNormSq normSq cross1 cross2 cross3
  ring

/-- A direction parallel to the local vorticity has zero projected
component. This *cannot* be chosen as Miller's admissible direction
unless the same field has the required bounded spatial gradient,
including a justified treatment of vorticity zeros. -/
theorem parallel_direction_has_zero_cross
    (v₁ v₂ v₃ k : ℝ) :
    crossNormSq v₁ v₂ v₃ (k * v₁) (k * v₂) (k * v₃) = 0 := by
  unfold crossNormSq normSq cross1 cross2 cross3
  ring

/-!
## Finite sample majorant / R735 transfer boundary

A same-source *continuum* enstrophy ceiling D would imply finite
projected fourth-power expenditure over a bounded time interval.
The following theorem only proves that finite nonnegative real
sample analogue. It is a safe consumer of supplied numerical bounds,
not a proof that the periodic #1271 source provides Miller's R³
spacetime estimates (nor a replacement for integration, compactness
or continuation).
-/

/-- If the projected square P at each time is no larger than the full
enstrophy E and each E is no larger than D, the finite-sample
fourth-power budget is at most (#samples) * D². -/
theorem finite_sample_fourth_power_budget
    {Time : Type*} (samples : Finset Time)
    (P E : Time → ℝ) (D : ℝ)
    (hPNonnegative : ∀ t ∈ samples, 0 ≤ P t)
    (hProjection : ∀ t ∈ samples, P t ≤ E t)
    (hEnstrophyCeiling : ∀ t ∈ samples, E t ≤ D) :
    (∑ t ∈ samples, (P t) ^ 2) ≤
      (samples.card : ℝ) * D ^ 2 := by
  calc
    ∑ t ∈ samples, (P t) ^ 2 ≤
        ∑ t ∈ samples, D ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      have hp0 : 0 ≤ P t := hPNonnegative t ht
      have hpD : P t ≤ D :=
        (hProjection t ht).trans (hEnstrophyCeiling t ht)
      have hD0 : 0 ≤ D := hp0.trans hpD
      nlinarith [mul_nonneg (sub_nonneg.mpr hpD) (add_nonneg hD0 hp0)]
    _ = (samples.card : ℝ) * D ^ 2 := by simp

end RequestProject.NavierStokes.MillerProjectionGeometry
