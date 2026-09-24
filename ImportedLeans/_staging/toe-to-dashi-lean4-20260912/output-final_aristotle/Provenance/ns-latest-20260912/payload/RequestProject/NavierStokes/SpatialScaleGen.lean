/-
# The scaling generator on a time-independent profile

`GaussianScaleGram.lean` defines the parabolic scaling generator on space-time,

  `Λu = u + (x − x₀)·∇u + 2(t − t₀)∂_tu`,

as `ClayNS.scaleGen`, on fields `U : STime → E3` with `STime = ℝ × E3`.  The
probe construction of `ScaleProbeExistence.lean` and its three-dimensional lift
in `RadialProbeLift.lean` live instead on the *spatial* field `W : E3 → E3` and
the pure dilation generator `W(x) + (DW)(x)x`.

This file is the plumbing between the two.  For a *time-independent* profile —
i.e. the lift `stLift W (t,x) = W x` of a spatial field — the time derivative
term of `Λ` drops out and the spatial term assembles into a single directional
derivative:

* `ClayNS.stLift_fderiv` — the chain rule through `Prod.snd`;
* `ClayNS.dvec_space_stLift`, `ClayNS.dvec_time_stLift` — the two directional
  derivatives appearing in `scaleGen`;
* `ClayNS.scaleGen_stLift` — **the identification**
  `scaleGen (t₀, x₀) (stLift W) (t,x) = W x + (DW)(x)(x − x₀)`;
* `ClayNS.scaleGen_stLift_origin` — at a base point on the time axis,
  `scaleGen (t₀, 0) (stLift W) (t,x) = W x + (DW)(x)x`, which is exactly the
  dilation generator of `RadialProbeLift.lean`;
* `ClayNS.scaleGen_stLift_radialField` — combined with
  `ClayNS.radialField_dilation`: for a radial profile the space-time scaling
  generator of the lift *is* the radial field of `ΛV = V + rV'`.

Nothing here is an approximation: every statement is an identity.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.RadialProbeLift
import RequestProject.NavierStokes.GaussianScaleGram

open scoped BigOperators

noncomputable section

namespace ClayNS

/-- The time-independent lift of a spatial field to space-time. -/
def stLift (W : E3 → E3) : STime → E3 := fun z => W z.2

@[simp] lemma stLift_apply (W : E3 → E3) (z : STime) : stLift W z = W z.2 := rfl

/-- The Fréchet derivative of a time-independent lift: the chain rule through
the (linear) projection `Prod.snd`. -/
theorem stLift_hasFDerivAt {W : E3 → E3} {z : STime} (hW : DifferentiableAt ℝ W z.2) :
    HasFDerivAt (stLift W)
      ((fderiv ℝ W z.2).comp (ContinuousLinearMap.snd ℝ ℝ E3)) z :=
  hW.hasFDerivAt.comp z (ContinuousLinearMap.snd ℝ ℝ E3).hasFDerivAt

theorem stLift_fderiv {W : E3 → E3} {z : STime} (hW : DifferentiableAt ℝ W z.2) :
    fderiv ℝ (stLift W) z = (fderiv ℝ W z.2).comp (ContinuousLinearMap.snd ℝ ℝ E3) :=
  (stLift_hasFDerivAt hW).fderiv

/-- A purely spatial directional derivative of the lift is the spatial
derivative. -/
lemma dvec_space_stLift {W : E3 → E3} {z : STime} (hW : DifferentiableAt ℝ W z.2) (v : E3) :
    dvec (0, v) (stLift W) z = fderiv ℝ W z.2 v := by
  rw [dvec, stLift_fderiv hW]
  simp

/-- The time directional derivative of a time-independent lift vanishes. -/
lemma dvec_time_stLift {W : E3 → E3} {z : STime} (hW : DifferentiableAt ℝ W z.2) :
    dvec (1, 0) (stLift W) z = 0 := by
  rw [dvec, stLift_fderiv hW]
  simp

/-- The standard basis of `E3` reassembles a vector. -/
lemma sum_smul_ee (v : E3) : ∑ j, (v j) • ee j = v := by
  ext i
  rw [show (∑ j, (v j) • ee j) i = ∑ j, ((v j) • ee j) i from rfl]
  simp [ee, EuclideanSpace.single_apply]

/-- **The scaling generator of a time-independent profile.**  For the lift of a
spatial field `W`, the parabolic scaling generator based at `z₀ = (t₀, x₀)`
reduces to the spatial dilation generator centred at `x₀`:

  `Λ(stLift W)(t,x) = W(x) + (DW)(x)(x − x₀)`.

The `2(t − t₀)∂_t` term vanishes identically, and the sum over coordinates
collapses into one directional derivative. -/
theorem scaleGen_stLift {W : E3 → E3} {z0 z : STime} (hW : DifferentiableAt ℝ W z.2) :
    scaleGen z0 (stLift W) z = W z.2 + fderiv ℝ W z.2 (z.2 - z0.2) := by
  have hspace : ∀ j : Fin 3,
      ((z.2 - z0.2) j) • dvec (0, ee j) (stLift W) z
        = fderiv ℝ W z.2 (((z.2 - z0.2) j) • ee j) := by
    intro j
    rw [dvec_space_stLift hW, map_smul]
  rw [scaleGen, dvec_time_stLift hW, smul_zero, add_zero,
    Finset.sum_congr rfl (fun j _ => hspace j), ← map_sum, sum_smul_ee]
  rfl

/-- **The scaling generator at a base point on the time axis.**  With `x₀ = 0`
the identification is with the pure dilation generator `W + (DW)·x`, which is
the object the radial probe of `RadialProbeLift.lean` is blind to. -/
theorem scaleGen_stLift_origin {W : E3 → E3} {t0 : ℝ} {z : STime}
    (hW : DifferentiableAt ℝ W z.2) :
    scaleGen (t0, (0 : E3)) (stLift W) z = W z.2 + fderiv ℝ W z.2 z.2 := by
  rw [scaleGen_stLift hW]
  simp

/-- **The radial profile instance.**  For `W = radialField V` with `V`
differentiable, the space-time scaling generator of the time-independent lift is
the radial field of the one-dimensional generator `ΛV = V + rV'`. -/
theorem scaleGen_stLift_radialField {V V' : ℝ → ℝ} {t0 : ℝ} {z : STime} (hz : z.2 ≠ 0)
    (hV : HasDerivAt V (V' ‖z.2‖) ‖z.2‖) :
    scaleGen (t0, (0 : E3)) (stLift (radialField V)) z = radialField (radGen V V') z.2 := by
  rw [scaleGen_stLift_origin (radialField_differentiableAt hz hV)]
  exact radialField_dilation hz hV

end ClayNS
