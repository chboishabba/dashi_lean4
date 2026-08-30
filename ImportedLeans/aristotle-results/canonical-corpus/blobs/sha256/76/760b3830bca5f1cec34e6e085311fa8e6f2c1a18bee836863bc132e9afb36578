/-
**Q8 — the true trace scale of a single zero's window vector.**

The bounded-height programme replaces a localized second-trace explicit formula
by the elementary chain

    ∑_ρ m_ρ² Δ_ρ ≤ e₂(G_W^mult) ≤ ½ (tr G_W^mult)²,     tr G_W^mult ≤ C · N_mult(W) · (per-vector scale),

so everything hinges on the **per-vector squared norm** — the diagonal Gram
entry of one hypothetical zero's evaluation vector on the source grid.  This
file computes that scale from the actual definitions, in both directions.

*Upper bound, uniform in the window length.*  `sum_normSq_gridVec_le`: for a
`C¹` taper and grid spacing `h`,

    ∑_{0 ≤ k < d} ‖φ̂(kh − iα)‖²  ≤  taperMass(φ,α)² + 2 · derivMass(φ,α)²/h² ,

with **no dependence on the window length `d`**: the horizontal decay
`‖φ̂(kh − iα)‖ ≤ derivMass/(|k|h)` of `GridTail.lean` makes the grid energy a
convergent `∑ k⁻²`.  In the source normalisation `h = 2π/L` this reads

    ‖u_ρ‖²  ≤  taperMass(φ,α)² + derivMass(φ,α)² L²/(2π²)      (`gridVec_normSq_source_le`),

i.e. the per-vector scale is `L²` times taper masses — *not* `L`.

*Lower bound.*  `gridVec_re_normSq_ge_plateau`: the window contains the central
grid point, whose sample is real and at least the plateau width `2a`, so in the
source regime `a ≥ 3L/8`

    ‖a_ρ‖² ≥ (2a)² ≥ (9/16) L² .

*Consequence (the negative one).*  `not_linear_trace_bound`: a per-vector trace
bound of the linear shape `tr ≤ C_vec · L` — the shape the bounded-height
programme needs in order to reach a budget `O(L⁴)` — is **false** for the source
vectors once `L > 16 C_vec/9`.  The true diagonal scale is quadratic in `L`,
which moves the resulting budget from `L⁴` to `L⁶`: exactly the order of the
zero-side floor `c L⁶ α²`, hence critical rather than decaying.  See
`LocalBudgetScale.lean` for the asymptotic form of that dichotomy.

Everything is proved from the taper hypotheses already in use; nothing here
refers to `ζ`.
-/
import RiemannAnalytic.LocalWindow
import RiemannAnalytic.GridVectors

namespace RiemannAnalytic

open Complex Finset MeasureTheory

/-! ### The `L¹` mass of the twisted taper -/

/-- The `L¹` mass of the twisted taper: the constant in the trivial modulus
bound for a grid sample. -/
noncomputable def taperMass (φ : ℝ → ℝ) (α : ℝ) : ℝ :=
  ∫ u : ℝ, |φ u| * Real.exp (-α * u)

theorem taperMass_nonneg (φ : ℝ → ℝ) (α : ℝ) : 0 ≤ taperMass φ α :=
  integral_nonneg fun u => by positivity

/-- Every grid sample is bounded by the twisted taper mass. -/
theorem norm_gridSample_le_taperMass (φ : ℝ → ℝ) (h α : ℝ) (k : ℤ) :
    ‖gridSample φ h α k‖ ≤ taperMass φ α := by
  have hz := norm_PhiExt_le φ (((k : ℝ) : ℂ) * (h : ℂ) - Complex.I * (α : ℂ))
  have him : ((((k : ℝ)) : ℂ) * (h : ℂ) - Complex.I * (α : ℂ)).im = -α := by simp
  rw [him] at hz
  refine le_trans hz (le_of_eq ?_)
  unfold taperMass
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  ring_nf

/-- Squared form of the modulus bound for a grid sample. -/
theorem normSq_gridSample_le_taperMass_sq (φ : ℝ → ℝ) (h α : ℝ) (k : ℤ) :
    ‖gridSample φ h α k‖ ^ 2 ≤ taperMass φ α ^ 2 := by
  have h1 := norm_gridSample_le_taperMass φ h α k
  have h0 : 0 ≤ ‖gridSample φ h α k‖ := norm_nonneg _
  nlinarith

/-- Squared form of the horizontal decay bound: away from the central sample the
grid energy decays like `k⁻²`. -/
theorem normSq_gridSample_le_inv_sq {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R) {h : ℝ}
    (hh : 0 < h) (α : ℝ) {k : ℤ} (hk : k ≠ 0) :
    ‖gridSample φ h α k‖ ^ 2 ≤ derivMass φ α ^ 2 / (h ^ 2 * (k : ℝ) ^ 2) := by
  have hkabs : (0 : ℝ) < |(k : ℝ)| := by
    have : ((k : ℝ)) ≠ 0 := Int.cast_ne_zero.2 hk
    exact abs_pos.2 this
  have hdec := norm_gridSample_mul_le hφ hh α k
  have hnn : 0 ≤ ‖gridSample φ h α k‖ := norm_nonneg _
  have hbound : ‖gridSample φ h α k‖ ≤ derivMass φ α / (|(k : ℝ)| * h) := by
    rw [le_div_iff₀ (by positivity)]
    exact hdec
  have hsq : ‖gridSample φ h α k‖ ^ 2 ≤ (derivMass φ α / (|(k : ℝ)| * h)) ^ 2 :=
    pow_le_pow_left₀ hnn hbound 2
  have hval : (derivMass φ α / (|(k : ℝ)| * h)) ^ 2
      = derivMass φ α ^ 2 / (h ^ 2 * (k : ℝ) ^ 2) := by
    rw [div_pow, mul_pow, sq_abs]
    ring_nf
  linarith [hsq, hval.le, hval.symm.le]

/-! ### An elementary inverse-square sum -/

private theorem sum_ite_inv_sq_aux (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ range (m + 1), (if k = 0 then (0 : ℝ) else 1 / (k : ℝ) ^ 2) ≤ 2 - 1 / (m : ℝ) := by
  induction m with
  | zero => omega
  | succ m ih =>
      rcases Nat.eq_or_lt_of_le hm with h | h
      · have hm0 : m = 0 := by omega
        subst hm0
        simp [Finset.sum_range_succ]
        norm_num
      · have hm1 : 1 ≤ m := by omega
        have hstep := ih hm1
        have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
        rw [Finset.sum_range_succ]
        have hif : (if m + 1 = 0 then (0 : ℝ) else 1 / (((m + 1 : ℕ)) : ℝ) ^ 2)
            = 1 / ((m : ℝ) + 1) ^ 2 := by simp
        rw [hif]
        have key : 1 / ((m : ℝ) + 1) ^ 2 ≤ 1 / (m : ℝ) - 1 / ((m : ℝ) + 1) := by
          rw [div_sub_div _ _ (ne_of_gt hmpos) (by positivity),
            div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        have hc : (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        rw [hc]
        linarith

/-- `∑_{1 ≤ k < n} k⁻² ≤ 2`. -/
theorem sum_ite_inv_sq_le_two (n : ℕ) :
    ∑ k ∈ range n, (if k = 0 then (0 : ℝ) else 1 / (k : ℝ) ^ 2) ≤ 2 := by
  match n with
  | 0 => simp
  | 1 => simp
  | (m + 2) =>
      have hb := sum_ite_inv_sq_aux (m + 1) (by omega)
      have hc : (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [hc] at hb
      have hp : 0 < 1 / ((m : ℝ) + 1) := by positivity
      linarith

/-! ### The window-length-free bound on the retained energy -/

/-- **The per-vector trace scale, upper bound.**  The total retained energy of a
zero's evaluation vector on a one-sided window of *any* length is bounded by the
window-independent quantity `taperMass² + 2 derivMass²/h²`. -/
theorem sum_normSq_gridVec_le {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R) {h : ℝ} (hh : 0 < h)
    (α : ℝ) (d : ℕ) :
    ∑ k : Fin d, ‖gridVec φ h (-(Complex.I * (α : ℂ))) d k‖ ^ 2
      ≤ taperMass φ α ^ 2 + 2 * (derivMass φ α ^ 2 / h ^ 2) := by
  classical
  have hrw : ∀ k : Fin d, ‖gridVec φ h (-(Complex.I * (α : ℂ))) d k‖ ^ 2
      = ‖gridSample φ h α ((k : ℕ) : ℤ)‖ ^ 2 := by
    intro k
    rw [gridVec_eq_gridSample]
  rw [Finset.sum_congr rfl fun k _ => hrw k,
    Fin.sum_univ_eq_sum_range (fun n : ℕ => ‖gridSample φ h α (n : ℤ)‖ ^ 2) d]
  have hpt : ∀ n ∈ range d, ‖gridSample φ h α (n : ℤ)‖ ^ 2
      ≤ (if n = 0 then taperMass φ α ^ 2 else 0)
        + derivMass φ α ^ 2 / h ^ 2 * (if n = 0 then 0 else 1 / (n : ℝ) ^ 2) := by
    intro n _
    by_cases hn : n = 0
    · subst hn
      simpa using normSq_gridSample_le_taperMass_sq φ h α 0
    · have hz : ((n : ℤ)) ≠ 0 := by exact_mod_cast hn
      have hb := normSq_gridSample_le_inv_sq hφ hh α hz
      have hcast : (((n : ℕ) : ℤ) : ℝ) = (n : ℝ) := by push_cast; ring
      rw [hcast] at hb
      have hval : derivMass φ α ^ 2 / (h ^ 2 * (n : ℝ) ^ 2)
          = derivMass φ α ^ 2 / h ^ 2 * (1 / (n : ℝ) ^ 2) := by
        field_simp
      simp only [hn, if_false]
      rw [hval] at hb
      linarith
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 : ∑ n ∈ range d, (if n = 0 then taperMass φ α ^ 2 else 0) ≤ taperMass φ α ^ 2 := by
    rw [Finset.sum_ite_eq' (range d) 0 (fun _ => taperMass φ α ^ 2)]
    by_cases hd : (0 : ℕ) ∈ range d
    · simp [hd]
    · simp [hd]
      positivity
  have h2 : derivMass φ α ^ 2 / h ^ 2
      * ∑ n ∈ range d, (if n = 0 then (0 : ℝ) else 1 / (n : ℝ) ^ 2)
      ≤ derivMass φ α ^ 2 / h ^ 2 * 2 := by
    refine mul_le_mul_of_nonneg_left (sum_ite_inv_sq_le_two d) ?_
    positivity
  linarith

/-- **The per-vector trace scale in the source normalisation `h = 2π/L`.**
`‖u_ρ‖² ≤ taperMass² + derivMass² L²/(2π²)`: quadratic in `L`. -/
theorem gridVec_normSq_source_le {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R) {L : ℝ} (hL : 0 < L)
    (α : ℝ) (d : ℕ) :
    ∑ k : Fin d, ‖gridVec φ (2 * Real.pi / L) (-(Complex.I * (α : ℂ))) d k‖ ^ 2
      ≤ taperMass φ α ^ 2 + derivMass φ α ^ 2 * L ^ 2 / (2 * Real.pi ^ 2) := by
  have hh : (0 : ℝ) < 2 * Real.pi / L := by positivity
  have hb := sum_normSq_gridVec_le hφ hh α d
  have hval : 2 * (derivMass φ α ^ 2 / (2 * Real.pi / L) ^ 2)
      = derivMass φ α ^ 2 * L ^ 2 / (2 * Real.pi ^ 2) := by
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [hval] at hb
  exact hb

/-- The real and imaginary coordinate vectors are each bounded by the total
retained energy. -/
theorem reOf_dotProduct_self_le_total {d : ℕ} (u : Fin d → ℂ) :
    reOf u ⬝ᵥ reOf u ≤ ∑ k, ‖u k‖ ^ 2 := by
  have h := reOf_add_imOf_dotProduct u
  have hnn : 0 ≤ imOf u ⬝ᵥ imOf u := by
    rw [imOf_dotProduct_self]
    exact Finset.sum_nonneg fun k _ => sq_nonneg _
  linarith

theorem imOf_dotProduct_self_le_total {d : ℕ} (u : Fin d → ℂ) :
    imOf u ⬝ᵥ imOf u ≤ ∑ k, ‖u k‖ ^ 2 := by
  have h := reOf_add_imOf_dotProduct u
  have hnn : 0 ≤ reOf u ⬝ᵥ reOf u := by
    rw [reOf_dotProduct_self]
    exact Finset.sum_nonneg fun k _ => sq_nonneg _
  linarith

/-! ### The lower bound, and the failure of a linear trace bound -/

/-- **The per-vector trace scale, lower bound.**  The one-sided window contains
the central grid point, whose sample is real and at least the plateau width, so
the longitudinal energy of a single zero is already at least `(2a)²`. -/
theorem gridVec_re_normSq_ge_plateau {φ : ℝ → ℝ} {R : ℝ} (hφ : CompactTaper φ R)
    (hnn : ∀ t, 0 ≤ φ t) {a : ℝ} (ha : 0 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1)
    (h α : ℝ) (d : ℕ) (hd : 1 ≤ d) :
    (2 * a) ^ 2 ≤ reOf (gridVec φ h (-(Complex.I * (α : ℂ))) d) ⬝ᵥ
      reOf (gridVec φ h (-(Complex.I * (α : ℂ))) d) := by
  classical
  rw [reOf_dotProduct_self]
  have hterm : (2 * a) ^ 2
      ≤ (gridVec φ h (-(Complex.I * (α : ℂ))) d ⟨0, by omega⟩).re ^ 2 := by
    have hval : (gridVec φ h (-(Complex.I * (α : ℂ))) d ⟨0, by omega⟩)
        = gridSample φ h α ((0 : ℕ) : ℤ) := by
      have := gridVec_eq_gridSample φ h α d (⟨0, by omega⟩ : Fin d)
      simpa using this
    rw [hval]
    have hge := gridSample_zero_re_ge_plateau hφ hnn ha hplat h α
    have h2a : 0 ≤ 2 * a := by linarith
    have : (0 : ℤ) = ((0 : ℕ) : ℤ) := by norm_num
    rw [← this]
    nlinarith [hge]
  refine le_trans hterm ?_
  refine Finset.single_le_sum
    (f := fun k : Fin d => (gridVec φ h (-(Complex.I * (α : ℂ))) d k).re ^ 2)
    (fun k _ => sq_nonneg _) (Finset.mem_univ _)

/-- **A linear per-vector trace bound is false.**

The bounded-height programme needs a diagonal bound of the shape
`‖u_ρ‖² ≤ C_vec · L` in order to reach a local exterior budget of size `L⁴`.
For the source vectors that shape fails: in the source regime `a ≥ 3L/8` the
longitudinal energy of a *single* zero already exceeds `C_vec L` as soon as
`16 C_vec < 9 L`.  The true diagonal scale is quadratic in `L`. -/
theorem not_linear_trace_bound {φ : ℝ → ℝ} {R : ℝ} (hφ : CompactTaper φ R)
    (hnn : ∀ t, 0 ≤ φ t) {L a : ℝ} (hL : 0 < L) (ha : 3 * L / 8 ≤ a)
    (hplat : ∀ t, |t| ≤ a → φ t = 1) (h α : ℝ) {d : ℕ} (hd : 1 ≤ d)
    {Cvec : ℝ} (hC : 16 * Cvec < 9 * L) :
    Cvec * L < reOf (gridVec φ h (-(Complex.I * (α : ℂ))) d) ⬝ᵥ
      reOf (gridVec φ h (-(Complex.I * (α : ℂ))) d) := by
  have ha0 : 0 ≤ a := le_trans (by positivity) ha
  have hge := gridVec_re_normSq_ge_plateau hφ hnn ha0 hplat h α d hd
  have hsq : 9 / 16 * L ^ 2 ≤ (2 * a) ^ 2 := by nlinarith
  nlinarith

end RiemannAnalytic
