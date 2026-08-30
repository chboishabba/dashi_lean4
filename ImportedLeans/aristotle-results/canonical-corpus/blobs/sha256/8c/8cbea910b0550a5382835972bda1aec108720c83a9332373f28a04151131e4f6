/-
# The four-sample geometry of a single prime frequency

The parity/pole-quotient architecture of `PoleQuotientTransversality.lean`
observes a response at the four symmetric radii `r, −r, 2r, −2r`.  After the
parity decomposition, a single frequency `λ` (for the prime side, `λ = log n`)
contributes the sample vector

  `Φ_r(λ) = (cos (rλ), sin (rλ), cos (2rλ), sin (2rλ)) ∈ ℝ⁴`.

Two exact, purely algebraic facts about that vector are established here, both
*before* any analytic estimate is attempted.

* `primeFourSampleChebyshevConstraint` : the doubling relations
  `cos 2x = 2 cos²x − 1`, `sin 2x = 2 sin x cos x` say that the four-sample map
  is the degree-two (Veronese-like) lift of the unit circle: a single frequency
  lies on a rigid one-parameter algebraic curve inside the four-dimensional
  sample space.

* `primeFourSampleQuotientDecision` : nevertheless that curve is **not**
  contained in any two-dimensional subspace.  For every observation radius
  `r > 0` and every pair of pole directions `v, w ∈ ℝ⁴` there is a frequency
  `λ > 0` whose sample vector is not a linear combination of `v` and `w`.  The
  proof is exact: four explicit frequencies produce four linearly independent
  sample vectors, and four independent vectors cannot lie in the span of two.

  Equivalently `primeFourSample_annihilator_trivial`: no nonzero linear
  functional annihilates all single-frequency sample vectors.

So the answer to the binary "is the single-frequency four-sample image confined
to the two-dimensional pole span?" is **no**, and it is no for the whole family
of frequencies at once, at every radius: the quadratic Chebyshev constraint does
not buy any linear degeneracy.  This is a statement about the four-sample
geometry of individual log-frequencies; it does not by itself evaluate the
weighted prime sum of the Weil explicit formula, which is not formalised in this
development.

No `sorry`, no `axiom`, no numerical evidence.
-/

import Mathlib

namespace RiemannAnalytic
namespace PrimeFourSampleGeometry

/-- The parity four-sample vector of a single frequency `λ` at radius `r`:
`(cos (rλ), sin (rλ), cos (2rλ), sin (2rλ))`. -/
noncomputable def primeFourSample (r lam : ℝ) : Fin 4 → ℝ :=
  ![Real.cos (r * lam), Real.sin (r * lam), Real.cos (2 * (r * lam)),
    Real.sin (2 * (r * lam))]

/-! ## The Chebyshev (degree-two Veronese) constraint -/

/-- **Single-mode Chebyshev constraint.**  The two doubled samples are exact
quadratic functions of the two base samples: with `c₁ = cos (rλ)` and
`s₁ = sin (rλ)`, `c₂ = 2c₁² − 1` and `s₂ = 2 s₁ c₁`.  A single frequency
therefore lies on a two-parameter algebraic curve (the degree-two lift of the
unit circle) inside the four-dimensional sample space. -/
theorem primeFourSampleChebyshevConstraint (r lam : ℝ) :
    primeFourSample r lam 2 = 2 * primeFourSample r lam 0 ^ 2 - 1 ∧
    primeFourSample r lam 3 = 2 * primeFourSample r lam 1 * primeFourSample r lam 0 ∧
    primeFourSample r lam 0 ^ 2 + primeFourSample r lam 1 ^ 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [primeFourSample, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  · rw [Real.cos_two_mul]
  · rw [Real.sin_two_mul]
  · rw [add_comm]
    exact Real.sin_sq_add_cos_sq _

/-! ## Periodic normalisation of the samples -/

/-- Shifting the phase by `2π` does not change the four-sample vector. -/
theorem primeFourSample_of_shift {r lam x : ℝ} (h : r * lam = 2 * Real.pi + x) :
    primeFourSample r lam
      = ![Real.cos x, Real.sin x, Real.cos (2 * x), Real.sin (2 * x)] := by
  simp only [primeFourSample, h]
  have h1 : Real.cos (2 * Real.pi + x) = Real.cos x := by
    rw [add_comm]; exact Real.cos_add_two_pi x
  have h2 : Real.sin (2 * Real.pi + x) = Real.sin x := by
    rw [add_comm]; exact Real.sin_add_two_pi x
  have h3 : (2 : ℝ) * (2 * Real.pi + x) = 2 * x + 2 * Real.pi + 2 * Real.pi := by ring
  rw [h1, h2, h3, Real.cos_add_two_pi, Real.cos_add_two_pi, Real.sin_add_two_pi,
    Real.sin_add_two_pi]

/-- Every phase `x ≥ 0` is realised by a strictly positive frequency. -/
theorem exists_pos_freq {r : ℝ} (hr : 0 < r) (x : ℝ) (hx : 0 ≤ x) :
    ∃ lam : ℝ, 0 < lam ∧ r * lam = 2 * Real.pi + x := by
  refine ⟨(2 * Real.pi + x) / r, ?_, by field_simp⟩
  have := Real.pi_pos
  positivity

/-! ## No nonzero functional annihilates the single-frequency family -/

/-- **Trivial annihilator.**  If a linear functional vanishes on the sample
vector of *every* positive frequency, all four of its coefficients vanish.
Only the four phases `0, π, π/2, π/4` are needed. -/
theorem primeFourSample_annihilator_trivial {r : ℝ} (hr : 0 < r) {A B C D : ℝ}
    (h : ∀ lam : ℝ, 0 < lam →
      A * primeFourSample r lam 0 + B * primeFourSample r lam 1
        + C * primeFourSample r lam 2 + D * primeFourSample r lam 3 = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 := by
  have key : ∀ x : ℝ, 0 ≤ x →
      A * Real.cos x + B * Real.sin x + C * Real.cos (2 * x) + D * Real.sin (2 * x) = 0 := by
    intro x hx
    obtain ⟨lam, hlam, hrl⟩ := exists_pos_freq hr x hx
    have hs := primeFourSample_of_shift hrl
    have := h lam hlam
    rw [hs] at this
    simpa using this
  have hpi := Real.pi_pos
  have e0 := key 0 le_rfl
  have e1 := key Real.pi hpi.le
  have e2 := key (Real.pi / 2) (by positivity)
  have e3 := key (Real.pi / 4) (by positivity)
  rw [show (2 : ℝ) * Real.pi = Real.pi + Real.pi by ring] at e1
  rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring] at e2
  rw [show (2 : ℝ) * (Real.pi / 4) = Real.pi / 2 by ring] at e3
  simp [Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_add,
    Real.sin_add] at e0 e1 e2 e3
  have hA : A = 0 := by linarith
  have hB : B = 0 := by linarith
  subst hA; subst hB
  simp at e3
  exact ⟨rfl, rfl, by linarith, e3⟩

/-! ## Four independent single-frequency samples -/

/-- The four explicit sample vectors at the phases `0, π, π/2, π/4`. -/
noncomputable def sampleCorners : Fin 4 → (Fin 4 → ℝ) :=
  ![![1, 0, 1, 0], ![-1, 0, 1, 0], ![0, 1, -1, 0],
    ![Real.sqrt 2 / 2, Real.sqrt 2 / 2, 0, 1]]

/-- The four corner vectors are linearly independent — and the value
`√2/2` plays no role in the elimination. -/
theorem sampleCorners_linearIndependent : LinearIndependent ℝ sampleCorners := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h0 := congrFun hg 0
  have h1 := congrFun hg 1
  have h2 := congrFun hg 2
  have h3 := congrFun hg 3
  simp [sampleCorners, Fin.sum_univ_four] at h0 h1 h2 h3
  rw [h3, zero_mul, add_zero] at h0 h1
  fin_cases i <;> simp <;> linarith

/-- Each corner vector is an actual single-frequency sample at a strictly
positive frequency. -/
theorem sampleCorners_realized {r : ℝ} (hr : 0 < r) (i : Fin 4) :
    ∃ lam : ℝ, 0 < lam ∧ primeFourSample r lam = sampleCorners i := by
  have hpi := Real.pi_pos
  fin_cases i
  · obtain ⟨lam, hlam, hrl⟩ := exists_pos_freq hr 0 le_rfl
    exact ⟨lam, hlam, by
      rw [primeFourSample_of_shift hrl]
      norm_num [sampleCorners]⟩
  · obtain ⟨lam, hlam, hrl⟩ := exists_pos_freq hr Real.pi hpi.le
    refine ⟨lam, hlam, ?_⟩
    rw [primeFourSample_of_shift hrl,
      show (2 : ℝ) * Real.pi = Real.pi + Real.pi by ring]
    norm_num [sampleCorners, Real.cos_pi, Real.sin_pi, Real.cos_add, Real.sin_add]
  · obtain ⟨lam, hlam, hrl⟩ := exists_pos_freq hr (Real.pi / 2) (by positivity)
    refine ⟨lam, hlam, ?_⟩
    rw [primeFourSample_of_shift hrl, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring]
    norm_num [sampleCorners, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
  · obtain ⟨lam, hlam, hrl⟩ := exists_pos_freq hr (Real.pi / 4) (by positivity)
    refine ⟨lam, hlam, ?_⟩
    rw [primeFourSample_of_shift hrl, show (2 : ℝ) * (Real.pi / 4) = Real.pi / 2 by ring]
    norm_num [sampleCorners, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_pi_div_four,
      Real.sin_pi_div_four]

/-! ## The decision -/

/-- A span of two vectors in `ℝ⁴` has rank at most two. -/
theorem finrank_span_pair_le (v w : Fin 4 → ℝ) :
    Module.finrank ℝ (Submodule.span ℝ ({v, w} : Set (Fin 4 → ℝ))) ≤ 2 := by
  classical
  refine (finrank_span_le_card (R := ℝ) ({v, w} : Set (Fin 4 → ℝ))).trans ?_
  have hsub : ({v, w} : Set (Fin 4 → ℝ)).toFinset ⊆ ({v, w} : Finset (Fin 4 → ℝ)) := by
    intro x hx; simpa using Set.mem_toFinset.1 hx
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_insert_le _ _).trans (by simp))

/-- **Prime four-sample quotient decision.**  For every observation radius
`r > 0` and every pair of pole directions `v, w`, there is a strictly positive
frequency whose parity four-sample vector is *not* in the span of `v` and `w`.

So the single-frequency image is transverse to any two-dimensional nuisance
space: the quadratic Chebyshev constraint on a single mode does not confine the
family of modes to the pole plane. -/
theorem primeFourSampleQuotientDecision {r : ℝ} (hr : 0 < r) (v w : Fin 4 → ℝ) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ s t : ℝ, primeFourSample r lam ≠ s • v + t • w := by
  by_contra hcon
  push_neg at hcon
  have hmem : ∀ i, sampleCorners i ∈ Submodule.span ℝ ({v, w} : Set (Fin 4 → ℝ)) := by
    intro i
    obtain ⟨lam, hlam, hsample⟩ := sampleCorners_realized hr i
    obtain ⟨s, t, hst⟩ := hcon lam hlam
    rw [← hsample, hst]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hle : Submodule.span ℝ (Set.range sampleCorners)
      ≤ Submodule.span ℝ ({v, w} : Set (Fin 4 → ℝ)) :=
    Submodule.span_le.2 (by rintro x ⟨i, rfl⟩; exact hmem i)
  have h4 : Module.finrank ℝ (Submodule.span ℝ (Set.range sampleCorners)) = 4 := by
    rw [finrank_span_eq_card sampleCorners_linearIndependent]; simp
  have hmono := Submodule.finrank_mono (R := ℝ) hle
  have := finrank_span_pair_le v w
  omega

end PrimeFourSampleGeometry
end RiemannAnalytic
