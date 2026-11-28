import Mathlib

/-!
# Original whole-space R3 input-pair midpoint and Leray geometry

This is an *explicit complex phase-preserving Cartesian 3-vector* shadow
of the already-existing Agda R290/R541 and
NSTriadKNEuclideanCanonicalProjectedInteractionExact constructors.
Do NOT mistake it for a newly discovered PDE bound, a second A
physical-kernel constructor, or a Fourier-transform/measure theorem.

For xi != 0, the physical Euclidean resolvent uses a=ν|xi|².
For a same-output interaction eta+zeta=xi, the ACTUAL physical viscous
input rate satisfies
  ν(|eta|²+|zeta|²)=ν|xi|²/2+2ν|eta-xi/2|².
The centered rate is nonnegative, with no arbitrary positive rate
or shell approximation.

For an incompressible complex Fourier velocity u_eta with eta·u_eta=0,
  xi·u_eta=-2(eta-xi/2)·u_eta.
Thus the physical divergence-form/Leray cell loses one factor of the
midpoint displacement, with BOTH real and imaginary phases retained.
This identity is the original A2-midpoint INNER sector donor; it alone
does NOT control the outer signed double interaction/continuum or
prove regularity. Zero output remains separate.
-/

namespace DASHI.NavierStokes.EuclideanMidpoint

/-- Same literal three physical Cartesian coordinates, no shell aliases. -/
def massSq (v : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, v i ^ 2

/-- Euclidean nonnegative physical mass; only the exact finite square
summation is used here, not a Fourier measure on R3. -/
theorem massSq_nonnegative (v : Fin 3 → ℝ) :
    0 ≤ massSq v := by
  unfold massSq
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- Literal same-output midpoint/pair rate equality for the original
physical input eta,xi-eta and the real center eta-xi/2. -/
theorem physical_midpoint_mass_identity (η ξ : Fin 3 → ℝ) :
    massSq η + massSq (fun i => ξ i - η i) =
      massSq ξ / 2 + 2 * massSq (fun i => η i - ξ i/2) := by
  unfold massSq
  have hi (i : Fin 3) :
      η i ^ 2 + (ξ i - η i) ^ 2 =
        ξ i ^ 2 / 2 + 2 * (η i - ξ i/2) ^ 2 := by
    ring
  calc
    (∑ i : Fin 3, η i ^ 2) +
        (∑ i : Fin 3, (ξ i - η i) ^ 2)
      = ∑ i : Fin 3, (η i ^ 2 + (ξ i - η i) ^ 2) := by
        rw [Finset.sum_add_distrib]
    _ = ∑ i : Fin 3, (ξ i ^ 2 / 2 + 2*(η i-ξ i/2)^2) := by
      exact Finset.sum_congr rfl (fun i _ => hi i)
    _ = (∑ i : Fin 3, ξ i ^ 2)/2 +
        2*(∑ i : Fin 3, (η i-ξ i/2)^2) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

/-- Viscosity is the SAME actual positive physical ν on both inputs. -/
theorem physical_midpoint_viscous_rate
    (ν : ℝ) (η ξ : Fin 3 → ℝ) :
    ν*(massSq η + massSq (fun i => ξ i-η i)) =
      ν*(massSq ξ/2 + 2*massSq (fun i => η i-ξ i/2)) := by
  rw [physical_midpoint_mass_identity]

/-- The centered rate remainder is genuinely nonnegative for ν>0. -/
theorem physical_centered_rate_nonnegative
    (ν : ℝ) (hν : 0 ≤ ν) (η ξ : Fin 3 → ℝ) :
    0 ≤ 2*ν*massSq (fun i => η i-ξ i/2) := by
  exact mul_nonneg (mul_nonneg (by norm_num) hν)
    (massSq_nonnegative _)

/-- Preserve the COMPLEX relative phase: use the exact original
Fourier transversality constraint eta·u_eta=0 rather than assuming
the output interaction is a nonnegative scalar Gram. -/
theorem physical_output_dot_from_input_transverse
    (η ξ : Fin 3 → ℝ) (u : Fin 3 → ℂ)
    (hη : (∑ i : Fin 3, (η i : ℂ)*u i) = 0) :
    (∑ i : Fin 3, (ξ i : ℂ)*u i) =
      -2*(∑ i : Fin 3, ((η i-ξ i/2 : ℝ) : ℂ)*u i) := by
  have hi (i : Fin 3) :
      (ξ i : ℂ)*u i =
        2*((η i : ℂ)*u i) -
          2*((((η i-ξ i/2 : ℝ) : ℂ)*u i)) := by
    push_cast
    ring
  calc
    (∑ i : Fin 3, (ξ i : ℂ)*u i) =
      ∑ i : Fin 3, (2*((η i : ℂ)*u i) -
        2*((((η i-ξ i/2 : ℝ) : ℂ)*u i))) := by
          exact Finset.sum_congr rfl (fun i _ => hi i)
    _ = 2*(∑ i : Fin 3, (η i : ℂ)*u i) -
      2*(∑ i : Fin 3, ((η i-ξ i/2 : ℝ) : ℂ)*u i) := by
        simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
        ring
    _ = -2*(∑ i : Fin 3, ((η i-ξ i/2 : ℝ) : ℂ)*u i) := by
      rw [hη]
      ring

/-- The midpoint input eta=xi/2 has ZERO divergence-form projected
cell for an actual incompressible velocity, without absolute values. -/
theorem exact_midpoint_transverse_output_vanishes
    (η ξ : Fin 3 → ℝ) (u : Fin 3 → ℂ)
    (hmid : ∀ i, η i = ξ i / 2)
    (hη : (∑ i : Fin 3, (η i : ℂ)*u i) = 0) :
    (∑ i : Fin 3, (ξ i : ℂ)*u i) = 0 := by
  rw [physical_output_dot_from_input_transverse η ξ u hη]
  have hz (i : Fin 3) : η i - ξ i / 2 = 0 := by
    rw [hmid i]
    ring
  simp [hz]

end DASHI.NavierStokes.EuclideanMidpoint
