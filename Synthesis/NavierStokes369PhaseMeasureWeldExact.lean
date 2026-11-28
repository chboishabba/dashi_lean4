import Synthesis.NavierStokesEuclideanOriginalMidpointLerayWeldExact

/-!
Actual Cartesian midpoint bound, retaining the two real components of the
original complex Fourier coefficient. Classical Lagrange identity; DASHI
same-output midpoint attachment (R290/R541). No positive-data continuation
or cutoff-uniform signed exterior is inferred.
-/
namespace DASHI.NavierStokes.EuclideanMidpoint

def realDot (a b : Fin 3 → ℝ) : ℝ := ∑ i, a i * b i

theorem realDot_sq_le_mass (a b : Fin 3 → ℝ) :
    realDot a b ^ 2 ≤ massSq a * massSq b := by
  have h01 := sq_nonneg (a 0*b 1-a 1*b 0)
  have h02 := sq_nonneg (a 0*b 2-a 2*b 0)
  have h12 := sq_nonneg (a 1*b 2-a 2*b 1)
  simp only [realDot, massSq, Fin.sum_univ_three]
  nlinarith only [h01,h02,h12]

/-- The signed real/imaginary split is exact, not a norm-only reconstruction. -/
def phaseDotSq (a : Fin 3 → ℝ) (u : Fin 3 → ℂ) : ℝ :=
  realDot a (fun i => (u i).re)^2 + realDot a (fun i => (u i).im)^2

def phaseMass (u : Fin 3 → ℂ) : ℝ :=
  massSq (fun i => (u i).re) + massSq (fun i => (u i).im)

theorem phaseMass_nonneg (u : Fin 3 → ℂ) : 0 ≤ phaseMass u :=
  add_nonneg (massSq_nonnegative _) (massSq_nonnegative _)

theorem phaseDotSq_le (a : Fin 3 → ℝ) (u : Fin 3 → ℂ) :
    phaseDotSq a u ≤ massSq a * phaseMass u := by
  unfold phaseDotSq phaseMass
  have hr := realDot_sq_le_mass a (fun i => (u i).re)
  have hi := realDot_sq_le_mass a (fun i => (u i).im)
  linarith [add_le_add hr hi, mul_add (massSq a)
    (massSq (fun i => (u i).re)) (massSq (fun i => (u i).im))]

theorem realDot_midpoint (η ξ a : Fin 3 → ℝ)
    (h : realDot η a = 0) :
    realDot ξ a = -2 * realDot (fun i => η i-ξ i/2) a := by
  simp only [realDot, Fin.sum_univ_three] at h ⊢
  linear_combination 2*h

/-- Squared same-source complex divergence factor has two simultaneous
bounds. Both input phase coordinates must be transverse. -/
theorem phase_midpoint_dual_bound (η ξ : Fin 3 → ℝ) (u : Fin 3 → ℂ)
    (hr : realDot η (fun i => (u i).re) = 0)
    (hi : realDot η (fun i => (u i).im) = 0) :
    phaseDotSq ξ u ≤
      min (massSq ξ * phaseMass u)
          (4 * massSq (fun i => η i-ξ i/2) * phaseMass u) := by
  apply le_min (phaseDotSq_le ξ u)
  have he : phaseDotSq ξ u =
      4 * phaseDotSq (fun i => η i-ξ i/2) u := by
    unfold phaseDotSq
    rw [realDot_midpoint η ξ _ hr, realDot_midpoint η ξ _ hi]
    ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left
    (phaseDotSq_le (fun i => η i-ξ i/2) u) (show (0:ℝ) ≤ 4 by norm_num)
  nlinarith only [hh]

/-- Reverse-solve against the original positive viscosity input rate:
both bounds remain simultaneously available on the literal carrier.
No absolute-value estimate on the integrated signed R406 is asserted. -/
theorem phase_midpoint_resolvent_bound (ν : ℝ) (hν : 0 < ν)
    (η ξ : Fin 3 → ℝ) (u : Fin 3 → ℂ)
    (hr : realDot η (fun i => (u i).re) = 0)
    (hi : realDot η (fun i => (u i).im) = 0)
    (hRate : 0 < massSq η + massSq (fun i => ξ i-η i)) :
    phaseDotSq ξ u / (ν*(massSq η + massSq (fun i => ξ i-η i))) ≤
      min (massSq ξ * phaseMass u)
          (4 * massSq (fun i => η i-ξ i/2) * phaseMass u) /
      (ν*(massSq ξ/2 + 2*massSq (fun i => η i-ξ i/2))) := by
  rw [← physical_midpoint_mass_identity]
  exact div_le_div_of_nonneg_right (phase_midpoint_dual_bound η ξ u hr hi)
    (le_of_lt (mul_pos hν hRate))


/-- Literal identification with the original complex Fourier dot, rather
than merely a convenient phase-pair proxy. -/
theorem phaseDotSq_eq_complex_normSq (a : Fin 3 → ℝ) (u : Fin 3 → ℂ) :
    phaseDotSq a u = Complex.normSq (∑ i : Fin 3, (a i : ℂ)*u i) := by
  simp [phaseDotSq, realDot, Fin.sum_univ_three, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, pow_two]
  <;> ring

theorem phaseMass_eq_complex_normSq_sum (u : Fin 3 → ℂ) :
    phaseMass u = ∑ i : Fin 3, Complex.normSq (u i) := by
  simp [phaseMass, massSq, Fin.sum_univ_three, Complex.normSq_apply, pow_two]
  <;> ring

/-- Actual original complex incompressibility supplies both real-phase
premises. This uses the same xi, eta and u as the earlier native module. -/
theorem physical_complex_phase_midpoint_bound (η ξ : Fin 3 → ℝ)
    (u : Fin 3 → ℂ) (hη : (∑ i : Fin 3, (η i : ℂ)*u i) = 0) :
    Complex.normSq (∑ i : Fin 3, (ξ i : ℂ)*u i) ≤
      min (massSq ξ * (∑ i : Fin 3, Complex.normSq (u i)))
          (4 * massSq (fun i => η i-ξ i/2) *
            (∑ i : Fin 3, Complex.normSq (u i))) := by
  have hr : realDot η (fun i => (u i).re) = 0 := by
    simpa [realDot, Fin.sum_univ_three, Complex.add_re, Complex.mul_re]
      using congrArg Complex.re hη
  have hi : realDot η (fun i => (u i).im) = 0 := by
    simpa [realDot, Fin.sum_univ_three, Complex.add_im, Complex.mul_im]
      using congrArg Complex.im hη
  simpa only [phaseDotSq_eq_complex_normSq, phaseMass_eq_complex_normSq_sum]
    using phase_midpoint_dual_bound η ξ u hr hi


/-- Both midpoint estimates together give a sharp uniform pair-rate
bound, without a lattice gap or division by an individual input norm.
min(A,4B) ≤ A/2+2B; the constant 1 is attained on the zero-input
boundary and approached by nonzero transverse pairs.
This is an actual single-cell viscous cancellation, not a bound on
the double R406 signed exterior or the spacetime continuation. -/
theorem transverse_pair_rate_bound (ν : ℝ) (hν : 0 < ν)
    (η ξ : Fin 3 → ℝ) (u : Fin 3 → ℂ)
    (hr : realDot η (fun i => (u i).re) = 0)
    (hi : realDot η (fun i => (u i).im) = 0)
    (hRate : 0 < massSq η + massSq (fun i => ξ i-η i)) :
    phaseDotSq ξ u / (ν*(massSq η+massSq (fun i => ξ i-η i))) ≤
      phaseMass u / ν := by
  have h := phase_midpoint_dual_bound η ξ u hr hi
  have h1 := le_trans h (min_le_left _ _)
  have h2 := le_trans h (min_le_right _ _)
  have hb : phaseDotSq ξ u ≤
      (massSq η+massSq (fun i => ξ i-η i))*phaseMass u := by
    rw [physical_midpoint_mass_identity]
    nlinarith only [h1,h2]
  apply (div_le_iff₀ (mul_pos hν hRate)).mpr
  calc
    phaseDotSq ξ u ≤
      (massSq η+massSq (fun i => ξ i-η i))*phaseMass u := hb
    _ = phaseMass u / ν * (ν*(massSq η+massSq (fun i => ξ i-η i))) := by
      field_simp [ne_of_gt hν] <;> ring

/-- Multiply by the actual second input's squared mass: the raw
divergence-form numerator divided by the literal pair rate is
bounded by the product of the two input energies divided by ν.
The existing original Bishop Leray contraction is the projection donor. -/
theorem raw_cell_pair_rate_bound (ν : ℝ) (hν : 0 < ν)
    (η ξ : Fin 3 → ℝ) (u v : Fin 3 → ℂ)
    (hr : realDot η (fun i => (u i).re) = 0)
    (hi : realDot η (fun i => (u i).im) = 0)
    (hRate : 0 < massSq η + massSq (fun i => ξ i-η i)) :
    (phaseDotSq ξ u * phaseMass v) /
      (ν*(massSq η+massSq (fun i => ξ i-η i))) ≤
      (phaseMass u * phaseMass v)/ν := by
  have h := mul_le_mul_of_nonneg_right
    (transverse_pair_rate_bound ν hν η ξ u hr hi hRate) (phaseMass_nonneg v)
  convert h using 1 <;> ring


/-- Direct input transversality also removes eta from the original output
dot. This is stronger than the averaged pair-rate bound when the other
input is small. No frequency-sign chart or division by |eta|. -/
theorem transverse_other_input_dot (η ξ a : Fin 3 → ℝ)
    (h : realDot η a = 0) :
    realDot ξ a = realDot (fun i => ξ i-η i) a := by
  simp only [realDot,Fin.sum_univ_three] at h ⊢
  linear_combination h

theorem transverse_other_input_bound (η ξ : Fin 3 → ℝ) (u : Fin 3 → ℂ)
    (hr : realDot η (fun i => (u i).re) = 0)
    (hi : realDot η (fun i => (u i).im) = 0) :
    phaseDotSq ξ u ≤ massSq (fun i => ξ i-η i)*phaseMass u := by
  have h : phaseDotSq ξ u = phaseDotSq (fun i => ξ i-η i) u := by
    unfold phaseDotSq
    rw [transverse_other_input_dot η ξ _ hr,
        transverse_other_input_dot η ξ _ hi]
  rw [h]
  exact phaseDotSq_le _ _

end DASHI.NavierStokes.EuclideanMidpoint

namespace DASHI.NavierStokes.SignedMeasure
open MeasureTheory

/-- Actual signed Bochner-integral perturbation bound on the SAME measure.
For R³ apply to Lebesgue volume on actual Cartesian input coordinates;
for T³ Fourier use counting measure (or scaled finite counting).
This is a conditional error transport, not a bare sum/integral identity. -/
theorem signed_integral_error {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g e : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (he : Integrable e μ)
    (h : ∀ x, |f x-g x| ≤ e x) :
    |(∫ x, f x ∂μ) - (∫ x, g x ∂μ)| ≤ ∫ x, e x ∂μ := by
  have hd : Integrable (fun x => f x-g x) μ := hf.sub hg
  have hu : (∫ x, f x-g x ∂μ) ≤ ∫ x, e x ∂μ :=
    integral_mono hd he (fun x => (abs_le.mp (h x)).2)
  have hl : (∫ x, -e x ∂μ) ≤ ∫ x, f x-g x ∂μ :=
    integral_mono he.neg hd (fun x => (abs_le.mp (h x)).1)
  rw [integral_sub hf hg] at hu hl
  rw [integral_neg] at hl
  exact abs_le.mpr ⟨hl,hu⟩

/-- Actual Lebesgue integral on the two independent Cartesian frequencies
of a same-output interaction, not a 27-voxel counting proxy. -/
theorem euclidean_pair_signed_integral_error
    (f g e : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ)
    (hf : Integrable f) (hg : Integrable g) (he : Integrable e)
    (h : ∀ x, |f x-g x| ≤ e x) :
    |(∫ x, f x) - (∫ x, g x)| ≤ ∫ x, e x :=
  signed_integral_error volume f g e hf hg he h


/-- R406 pairs TWO same-output interactions. Its rich frequency carrier
has three independent R³ coordinates (xi, eta, eta') after eliminating
both convolution constraints. Use actual product volume on those nine
coordinates, rather than accidentally integrating only one input pair.
The signed integrand and majorant must still be constructed on that carrier. -/
theorem euclidean_double_interaction_signed_integral_error
    (f g e : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ)
    (hf : Integrable f) (hg : Integrable g) (he : Integrable e)
    (h : ∀ x, |f x-g x| ≤ e x) :
    |(∫ x, f x) - (∫ x, g x)| ≤ ∫ x, e x :=
  signed_integral_error volume f g e hf hg he h

end DASHI.NavierStokes.SignedMeasure
