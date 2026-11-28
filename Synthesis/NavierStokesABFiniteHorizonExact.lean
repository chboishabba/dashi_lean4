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
open scoped Interval

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
  have hi := intervalIntegral.integral_mono_on hT.le
    (intervalIntegrable_const (c := L^4))
    (hD.const_mul (K*E₀)) hpoint
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

end DASHI.NavierStokes.AB
