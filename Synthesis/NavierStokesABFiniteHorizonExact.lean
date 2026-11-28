import Synthesis.MillenniumNSSignedSpectralResidualExact
import Synthesis.NavierStokesFractionalR568EndpointWeldExact
import Synthesis.NavierStokesR726SignedDefectViscosityNoGoExact
import Synthesis.NavierStokesR726PhysicalRadicalSignCertificatesExact
import Synthesis.NavierStokesOriginalC1C2R652TraceWeldExact
import Synthesis.NavierStokesEuclideanOriginalMidpointLerayWeldExact
import Synthesis.NavierStokesRealCauchyTraceFTCExact
import Synthesis.NavierStokesEuclideanDoubleInteractionKernelExact
import Synthesis.NavierStokesEuclideanSignedProductMajorantExact
import Synthesis.NavierStokesEuclideanWeightedConvolutionExact
import Mathlib

/-!
Finite-horizon regularity cut for both original unforced NS lanes.
The energy identity and critical Fourier interpolation are physical
inputs. The theorem pays the common time-selection step with the
actual interval integral, not an assumption of an already global flow.
See the companion Agda roadmap for the original Fourier constants
and the conditional continuation proof. No universal NS theorem.
-/
namespace DASHI.NavierStokes.AB
open MeasureTheory


theorem critical_time_exists
    (E D X : ℝ → ℝ) (ν T K E₀ L : ℝ)
    (hν : 0 < ν) (hT : 0 < T) (hK : 0 ≤ K) (hE₀ : 0 ≤ E₀)
    (hL : 0 < L)
    (hD : IntervalIntegrable D volume 0 T)
    (henergy : 2*ν*(∫ t in 0..T, D t) ≤ E₀)
    (hnD : ∀ t ∈ Set.Icc 0 T, 0 ≤ D t)
    (hE : ∀ t ∈ Set.Icc 0 T, E t ≤ E₀)
    (hinterp : ∀ t ∈ Set.Icc 0 T, X t ^ 4 ≤ K*E t*D t)
    (horizon : K*E₀^2 < 2*ν*T*L^4) :
    ∃ t ∈ Set.Icc 0 T, X t < L := by
  by_contra! h
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
      L^4 ≤ (K*E₀)*D t := by
    calc
      L^4 ≤ X t^4 := pow_le_pow_left₀ hL.le (h t ht) 4
      _ ≤ K*E t*D t := hinterp t ht
      _ ≤ (K*E₀)*D t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hE t ht) hK) (hnD t ht)
  have hconst : IntervalIntegrable (fun _ : ℝ => L^4) volume 0 T :=
    continuous_const.intervalIntegrable _ _
  have hi := intervalIntegral.integral_mono_on hT.le
    hconst (hD.const_mul (K*E₀)) hpoint
  rw [intervalIntegral.integral_const_mul] at hi
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hi
  have h₁ := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2*ν by positivity)
  have h₂ := mul_le_mul_of_nonneg_left henergy (mul_nonneg hK hE₀)
  apply (not_le_of_gt horizon)
  calc
    2*ν*T*L^4 ≤ (2*ν)*((K*E₀)*(∫ t in 0..T, D t)) := by
      convert h₁ using 1 <;> ring
    _ ≤ K*E₀^2 := by
      convert h₂ using 1 <;> ring

/-- A common sufficient real threshold with the normalized Fourier
Lebesgue constant rounded outwards to 8^4. -/
theorem euclidean_time_exists
    (E D X : ℝ → ℝ) (ν T E₀ : ℝ)
    (hν : 0 < ν) (hT : 0 < T) (hE₀ : 0 ≤ E₀)
    (hD : IntervalIntegrable D volume 0 T)
    (henergy : 2*ν*(∫ t in 0..T, D t) ≤ E₀)
    (hnD : ∀ t ∈ Set.Icc 0 T, 0 ≤ D t)
    (hE : ∀ t ∈ Set.Icc 0 T, E t ≤ E₀)
    (hinterp : ∀ t ∈ Set.Icc 0 T, X t^4 ≤ 4096*E t*D t)
    (horizon : 128*E₀^2 < ν^5*T) :
    ∃ t ∈ Set.Icc 0 T, X t < 2*ν := by
  apply critical_time_exists E D X ν T 4096 E₀ (2*ν)
    hν hT (by norm_num) hE₀ (by positivity) hD henergy hnD hE hinterp
  nlinarith only [horizon, show (2*ν*T*(2*ν)^4) = 32*(ν^5*T) by ring]

/-- Mean-zero 2pi-periodic Fourier lattice, rounded constant 11^4. -/
theorem periodic_time_exists
    (E D X : ℝ → ℝ) (ν T E₀ : ℝ)
    (hν : 0 < ν) (hT : 0 < T) (hE₀ : 0 ≤ E₀)
    (hD : IntervalIntegrable D volume 0 T)
    (henergy : 2*ν*(∫ t in 0..T, D t) ≤ E₀)
    (hnD : ∀ t ∈ Set.Icc 0 T, 0 ≤ D t)
    (hE : ∀ t ∈ Set.Icc 0 T, E t ≤ E₀)
    (hinterp : ∀ t ∈ Set.Icc 0 T, X t^4 ≤ 14641*E t*D t)
    (horizon : 14641*E₀^2 < 32*ν^5*T) :
    ∃ t ∈ Set.Icc 0 T, X t < 2*ν := by
  apply critical_time_exists E D X ν T 14641 E₀ (2*ν)
    hν hT (by norm_num) hE₀ (by positivity) hD henergy hnD hE hinterp
  convert horizon using 1 <;> ring

/-- Keep the sign of helicity and both nonnegative dissipations.
This is the pointwise exact total/variation/minority decomposition. -/
theorem signed_dissipation_split (p m : ℝ) :
    p+m=|p-m|+2*min p m := by
  rcases le_total p m with h|h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- From the actual unforced signed helicity balance, the time-integrated
dissipation of either chirality controls both. No sign preservation
assumption and no absolute-value substitution in the balance. -/
theorem signed_helicity_budget (ν hp hm hp₀ hm₀ dp dm : ℝ)
    (hν : 0 < ν) (hminor : 0 ≤ hm)
    (hbal : hp-hm+2*ν*(dp-dm)=hp₀-hm₀) :
    hp+hm+2*ν*(dp+dm)=hp₀-hm₀+2*hm+4*ν*dm := by
  linarith


/-- A proof-producing scalar bound for the same reference error on
either Euclidean or periodic Fourier carriers. No minimum nonzero
wave number is required. E=X^{-1}, G=X^0, H=X^1 are nonnegative
norms of the actual error; Cauchy gives G^2 ≤ E H.
The paired Leray estimate supplies the displayed physical input. -/
theorem reference_rate_no_spectral_gap
    (E G H V ν q β δ rate residual : ℝ)
    (hE : 0 ≤ E) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hV : 0 ≤ V) (hβ : 0 < β)
    (hCauchy : G^2 ≤ E*H) (hEcap : E ≤ q)
    (hreserve : β+δ ≤ ν-q/2)
    (hRate : rate+(ν-E/2)*H ≤ V*G+residual) :
    rate+δ*H ≤ (V^2/(4*β))*E+residual := by
  have hYoung : V*G ≤ β*H+V^2/(4*β)*E := by
    by_cases hz : E=0
    · have hg : G=0 := by rw [hz,zero_mul] at hCauchy; nlinarith [sq_nonneg G]
      rw [hz,hg,mul_zero,mul_zero,add_zero]
      exact mul_nonneg hβ.le hH
    · have hEp : 0 < E := lt_of_le_of_ne hE (Ne.symm hz)
      have hsq := sq_nonneg (2*β*G-V*E)
      have hmul := mul_le_mul_of_nonneg_left hCauchy (show 0 ≤ 4*β^2 by positivity)
      have haux : 0 ≤ 4*β^2*E*H-4*β*V*E*G+V^2*E^2 := by
        nlinarith only [hsq,hmul]
      have hp : 0 < 4*β*E := by positivity
      apply (le_of_mul_le_mul_left ?_ hp)
      calc
        (4*β*E)*(V*G) ≤ 4*β^2*E*H+V^2*E^2 := by linarith only [haux]
        _ = (4*β*E)*(β*H+V^2/(4*β)*E) := by
          field_simp [ne_of_gt hβ] <;> ring
  have hr := mul_le_mul_of_nonneg_right
    (show β+δ ≤ ν-E/2 by linarith) hH
  linarith only [hRate,hYoung,hr]

end DASHI.NavierStokes.AB
