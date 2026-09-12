/-
Unconditional finite retention for the Gaussian taper.

`RiemannAnalytic.gridFiniteRetention` proves the one-sided lattice-tail /
finite-retention theorem *given* a tail-domination hypothesis.  For the
explicit Gaussian taper that hypothesis is not an assumption: the transverse
energies of the centred grid are computed in closed form here, they are
summable, and their tails tend to zero, so some finite window dominates its
own tail.  Consequently, whenever the transverse offset `α` is such that the
first grid sample has a nonzero imaginary part, a finite window carries a
strictly positive amount of energy and at least a quarter of the whole
two-sided transverse energy.
-/
import RiemannAnalytic.GaussianEnvelope

namespace RiemannAnalytic

open Complex Finset Filter

/-- Imaginary part of the Gaussian centred-grid samples in closed form. -/
theorem gridSample_gauss_im (h α : ℝ) (k : ℤ) :
    (gridSample gaussTaper h α k).im
      = Real.sqrt (2 * Real.pi) * Real.exp ((α ^ 2 - ((k : ℝ) * h) ^ 2) / 2)
        * Real.sin (((k : ℝ) * h) * α) := by
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  unfold gridSample
  rw [PhiExt_gaussTaper]
  have hhalf : ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) := by norm_num
  have hcast : ((2 * Real.pi : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) := by
    rw [hhalf, ← Complex.ofReal_cpow hpi, ← Real.sqrt_eq_rpow]
  have h2 : (-(((k : ℝ) : ℂ) * (h : ℂ) - Complex.I * (α : ℂ)) ^ 2 / 2).re
      = (α ^ 2 - ((k : ℝ) * h) ^ 2) / 2 := by simp [pow_two]
  have h3 : (-(((k : ℝ) : ℂ) * (h : ℂ) - Complex.I * (α : ℂ)) ^ 2 / 2).im
      = ((k : ℝ) * h) * α := by
    simp [pow_two]
    ring
  rw [hcast, im_ofReal_mul, Complex.exp_im, h2, h3]
  ring

/-- Closed form of the transverse (imaginary-channel) energy of the Gaussian
centred grid. -/
theorem transverseEnergy_gauss (h α : ℝ) (k : ℤ) :
    transverseEnergy gaussTaper h α k
      = 2 * Real.pi * Real.exp (α ^ 2 - ((k : ℝ) * h) ^ 2)
        * Real.sin (((k : ℝ) * h) * α) ^ 2 := by
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hexp : ∀ u : ℝ, Real.exp (u / 2) ^ 2 = Real.exp u := by
    intro u
    rw [sq, ← Real.exp_add]
    ring_nf
  unfold transverseEnergy
  rw [gridSample_gauss_im, mul_pow, mul_pow, Real.sq_sqrt hpi, hexp]

theorem transverseEnergy_gauss_nonneg (h α : ℝ) (k : ℤ) :
    0 ≤ transverseEnergy gaussTaper h α k := by
  unfold transverseEnergy
  positivity

/-- The Gaussian transverse energies are summable along the whole lattice. -/
theorem summable_transverseEnergy_gauss (h α : ℝ) (hh : h ≠ 0) :
    Summable (transverseEnergy gaussTaper h α) := by
  have hh2 : h * Real.sqrt 2 ≠ 0 := by
    have : Real.sqrt 2 ≠ 0 := by positivity
    exact mul_ne_zero hh this
  have hmaj : Summable fun k : ℤ =>
      2 * Real.pi * Real.exp ((((α * Real.sqrt 2) ^ 2
        - ((k : ℝ) * (h * Real.sqrt 2)) ^ 2)) / 2) :=
    summable_gaussEnvelope (h * Real.sqrt 2) (α * Real.sqrt 2) (2 * Real.pi) hh2
  have hmaj' : Summable fun k : ℤ => 2 * Real.pi * Real.exp (α ^ 2 - ((k : ℝ) * h) ^ 2) := by
    refine hmaj.congr fun k => ?_
    congr 2
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have e1 : (α * Real.sqrt 2) ^ 2 = 2 * α ^ 2 := by rw [mul_pow, h2]; ring
    have e2 : ((k : ℝ) * (h * Real.sqrt 2)) ^ 2 = 2 * ((k : ℝ) * h) ^ 2 := by
      rw [mul_pow, mul_pow, h2]; ring
    rw [e1, e2]
    ring
  refine Summable.of_nonneg_of_le (fun k => transverseEnergy_gauss_nonneg h α k)
    (fun k => ?_) hmaj'
  rw [transverseEnergy_gauss]
  have hs : Real.sin (((k : ℝ) * h) * α) ^ 2 ≤ 1 := by
    have := Real.neg_one_le_sin (((k : ℝ) * h) * α)
    have := Real.sin_le_one (((k : ℝ) * h) * α)
    nlinarith
  have hpos : (0 : ℝ) ≤ 2 * Real.pi * Real.exp (α ^ 2 - ((k : ℝ) * h) ^ 2) := by positivity
  nlinarith

/-- **Unconditional finite retention for the Gaussian taper.**  If the grid
spacing is nonzero and the first sample has nonzero imaginary part, then there
is a finite one-sided window which carries strictly positive transverse energy
and at least a quarter of the full two-sided transverse energy. -/
theorem gauss_finite_retention (h α : ℝ) (hh : h ≠ 0) (hsin : Real.sin (h * α) ≠ 0) :
    ∃ m : ℕ,
      0 < ∑ n ∈ range m, transverseEnergy gaussTaper h α ((n : ℤ) + 1) ∧
        ∑' k : ℤ, transverseEnergy gaussTaper h α k
          ≤ 4 * ∑ n ∈ range m, transverseEnergy gaussTaper h α ((n : ℤ) + 1) := by
  classical
  set E := transverseEnergy gaussTaper h α with hE
  have hsum : Summable E := summable_transverseEnergy_gauss h α hh
  have hnat : Summable fun n : ℕ => E (n : ℤ) :=
    hsum.comp_injective fun x y hxy => by exact_mod_cast hxy
  set a : ℕ → ℝ := fun n => E ((n : ℤ) + 1) with ha_def
  have ha : Summable a := by
    have : Summable fun n : ℕ => (fun m : ℕ => E (m : ℤ)) (n + 1) :=
      (summable_nat_add_iff 1).2 hnat
    refine this.congr fun n => ?_
    simp [ha_def]
  have ha_nonneg : ∀ n, 0 ≤ a n := fun n => transverseEnergy_gauss_nonneg h α _
  have ha0 : 0 < a 0 := by
    have hE1 : a 0 = 2 * Real.pi * Real.exp (α ^ 2 - h ^ 2) * Real.sin (h * α) ^ 2 := by
      simp only [ha_def, hE]
      rw [transverseEnergy_gauss]
      norm_num
    rw [hE1]
    have hs : 0 < Real.sin (h * α) ^ 2 := by positivity
    positivity
  have htail := tendsto_sum_nat_add a
  have hev : ∀ᶠ i in atTop, (∑' k, a (k + i)) < a 0 :=
    htail.eventually_lt_const ha0
  obtain ⟨m, hm, hm1⟩ := ((hev.and (eventually_ge_atTop 1)).exists)
  refine ⟨m, ?_, ?_⟩
  · have hmem : (0 : ℕ) ∈ range m := mem_range.2 (lt_of_lt_of_le Nat.zero_lt_one hm1)
    have := Finset.single_le_sum (f := a) (fun i _ => ha_nonneg i) hmem
    exact lt_of_lt_of_le ha0 this
  · have hdom : ∑' n : ℕ, E ((n : ℤ) + (m : ℤ) + 1) ≤ ∑ n ∈ range m, E ((n : ℤ) + 1) := by
      have hcongr : ∀ n : ℕ, a (n + m) = E ((n : ℤ) + (m : ℤ) + 1) := by
        intro n
        simp [ha_def]
      have : ∑' n : ℕ, a (n + m) ≤ a 0 := le_of_lt hm
      have hwin : a 0 ≤ ∑ n ∈ range m, a n := by
        have hmem : (0 : ℕ) ∈ range m := mem_range.2 (lt_of_lt_of_le Nat.zero_lt_one hm1)
        exact Finset.single_le_sum (f := a) (fun i _ => ha_nonneg i) hmem
      calc ∑' n : ℕ, E ((n : ℤ) + (m : ℤ) + 1)
          = ∑' n : ℕ, a (n + m) := (tsum_congr hcongr).symm
        _ ≤ a 0 := this
        _ ≤ ∑ n ∈ range m, a n := hwin
    exact gridFiniteRetention gaussTaper gaussTaper_even h α hsum m hdom

end RiemannAnalytic
