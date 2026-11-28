import Synthesis.NavierStokesOriginalRawConvectionSummabilityExact
import Synthesis.NavierStokesPressureCellSeriesExact

/-!
Original pressure summability from the *difference* of the already
summable raw and projected nonlinear Fourier cells.

At nonzero output k a selected nonzero coordinate k_i provides a
legitimate division. At zero output, pressureCell_zero discharges the
series directly. No independent pressure summability assumption is
introduced. This is not yet physical-space pressure reconstruction.
-/
namespace DASHI.NavierStokes.EuclideanMidpoint
open scoped BigOperators
noncomputable section

/-- A single nonzero physical output component makes the original
pressure cell a scalar multiple of the raw/projected difference.
A nonzero-output witness is necessary; zero output is separate. -/
theorem pressure_summable_from_raw_projected {J : Type*}
    (k : Vec3) (i : Fin 3) (hk : (k i : ℂ) ≠ 0)
    (u v : J → CVec3)
    (hr : Summable (fun p => -rawConvection k (u p) (v p) i))
    (hp : Summable (fun p => -projectedConvection k (u p) (v p) i)) :
    Summable (fun p => pressureCell k (u p) (v p)) := by
  let c : ℂ := Complex.I * (k i : ℂ)
  have hc : c ≠ 0 := mul_ne_zero Complex.I_ne_zero hk
  have hdiff : Summable (fun p =>
      (-rawConvection k (u p) (v p) i) -
      (-projectedConvection k (u p) (v p) i)) :=
    hr.sub hp
  have heq (p : J) :
      pressureCell k (u p) (v p) =
      c⁻¹ * ((-rawConvection k (u p) (v p) i) -
        (-projectedConvection k (u p) (v p) i)) := by
    have hs := projected_pressure_split k (u p) (v p) i
    change (-projectedConvection k (u p) (v p) i) =
      (-rawConvection k (u p) (v p) i) -
        c * pressureCell k (u p) (v p) at hs
    have hterm :
        ((-rawConvection k (u p) (v p) i) -
         (-projectedConvection k (u p) (v p) i)) =
          c * pressureCell k (u p) (v p) := by
      calc
        _ = c * pressureCell k (u p) (v p) := by
          rw [hs]
          ring
    rw [hterm, inv_mul_cancel_left₀ hc]
  exact (hdiff.mul_left c⁻¹).congr (fun p => (heq p).symm)

end
end DASHI.NavierStokes.EuclideanMidpoint
