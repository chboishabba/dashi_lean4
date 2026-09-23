/-
# The beta projection annihilates a third-order lattice-derivative remainder

The coupling coefficient extracted from a lattice polarisation tensor is a
*second jet at zero momentum*: for `μ ≠ ν` it is the mixed second momentum
derivative `∂_{p_μ} ∂_{p_ν} Π_{μν}(p)` evaluated at `p = 0`.  This file proves
the source-boundary fact that makes that projection insensitive to the
irrelevant part of the polarisation:

> if every term of a remainder `R_{μν}(p)` carries at least three lattice
> derivative factors, then `∂_{p_μ} ∂_{p_ν} R_{μν}(0) = 0`.

The mechanism is a pigeonhole on the two-dimensional slice through the origin
spanned by the two differentiated directions.  On that slice every lattice
factor `d_κ(p)` with `κ ∉ {μ,ν}` is identically zero (`d(0) = 0`), so a term
survives only if all three of its factors are `d_μ` or `d_ν`; then one of the
two variables carries at least two factors, and a function of the shape
`u(x)^k · w(x)` with `u(0) = 0` and `k ≥ 2` has vanishing derivative at `0`.

`mixedD` is the mixed second derivative of a two-variable function at the
origin, and `mixedMomentumD R μ ν` is the beta projection of a momentum-space
function.  The results are stated for a general lattice factor `u` with
`u 0 = 0`, and instantiated at the literal `phat` of `LatticeMomentum`.
-/
import RequestProject.YangMills.LatticeMomentum

namespace YangMills

open Real

/-- The mixed second derivative at the origin of a two-variable function. -/
noncomputable def mixedD (F : ℝ → ℝ → ℝ) : ℝ := deriv (fun s => deriv (fun t => F s t) 0) 0

/-- A factor vanishing at `0` to order at least two kills the derivative there. -/
lemma deriv_pow_mul_eq_zero {u w : ℝ → ℝ} (hu0 : u 0 = 0) (hu : DifferentiableAt ℝ u 0)
    (hw : DifferentiableAt ℝ w 0) {k : ℕ} (hk : 2 ≤ k) :
    deriv (fun s => u s ^ k * w s) 0 = 0 := by
  have hp : DifferentiableAt ℝ (fun s => u s ^ k) 0 := hu.pow k
  have h1 : (0 : ℝ) ^ (k - 1) = 0 := zero_pow (by omega)
  have h2 : (0 : ℝ) ^ k = 0 := zero_pow (by omega)
  rw [deriv_fun_mul hp hw, deriv_fun_pow hu, hu0, h1, h2]
  ring

/-- Two or more factors in the *first* variable kill the mixed derivative. -/
theorem mixedD_eq_zero_of_sq_factor_left {u : ℝ → ℝ} (hu0 : u 0 = 0)
    (hu : DifferentiableAt ℝ u 0) {a : ℕ} (ha : 2 ≤ a) (F : ℝ → ℝ → ℝ)
    (hc : DifferentiableAt ℝ (fun s => deriv (fun t => F s t) 0) 0) :
    mixedD (fun s t => u s ^ a * F s t) = 0 := by
  have hin : ∀ s : ℝ, deriv (fun t => u s ^ a * F s t) 0 = u s ^ a * deriv (fun t => F s t) 0 :=
    fun s => deriv_const_mul_field _
  rw [mixedD, funext hin]
  exact deriv_pow_mul_eq_zero hu0 hu hc ha

/-- Two or more factors in the *second* variable kill the mixed derivative. -/
theorem mixedD_eq_zero_of_sq_factor_right {u : ℝ → ℝ} (hu0 : u 0 = 0)
    (hu : DifferentiableAt ℝ u 0) {b : ℕ} (hb : 2 ≤ b) (H : ℝ → ℝ → ℝ)
    (hH : ∀ s, DifferentiableAt ℝ (fun t => H s t) 0) :
    mixedD (fun s t => H s t * u t ^ b) = 0 := by
  have hin : ∀ s : ℝ, deriv (fun t => H s t * u t ^ b) 0 = 0 := by
    intro s
    have he : (fun t => H s t * u t ^ b) = fun t => u t ^ b * H s t := by funext t; ring
    rw [he]
    exact deriv_pow_mul_eq_zero hu0 hu (hH s) hb
  rw [mixedD, funext hin]
  simp

/-- **`betaProjection_kills_thirdOrderRemainder`.**  A term carrying three
lattice derivative factors distributed over the two differentiated directions
has vanishing mixed second derivative at the origin, whatever the smooth
prefactor `g`. -/
theorem betaProjection_kills_thirdOrder {u : ℝ → ℝ} (hu0 : u 0 = 0)
    (hu : DifferentiableAt ℝ u 0) {g : ℝ → ℝ → ℝ}
    (hg : ∀ s, DifferentiableAt ℝ (fun t => g s t) 0)
    (hdg : DifferentiableAt ℝ (fun s => deriv (fun t => g s t) 0) 0)
    (hg0 : DifferentiableAt ℝ (fun s => g s 0) 0)
    {a b : ℕ} (hab : a + b = 3) :
    mixedD (fun s t => u s ^ a * (u t ^ b * g s t)) = 0 := by
  rcases le_or_gt 2 b with hb | hb
  · have he : (fun s t => u s ^ a * (u t ^ b * g s t))
        = fun s t => u s ^ a * g s t * u t ^ b := by
      funext s t; ring
    rw [he]
    exact mixedD_eq_zero_of_sq_factor_right hu0 hu hb _ fun s => (hg s).const_mul _
  · interval_cases b
    · have ha : 2 ≤ a := by omega
      refine mixedD_eq_zero_of_sq_factor_left hu0 hu ha _ ?_
      have he : (fun s => deriv (fun t => u t ^ 0 * g s t) 0)
          = fun s => deriv (fun t => g s t) 0 := by
        funext s; simp
      rw [he]; exact hdg
    · have ha : 2 ≤ a := by omega
      refine mixedD_eq_zero_of_sq_factor_left hu0 hu ha _ ?_
      have he : (fun s => deriv (fun t => u t ^ 1 * g s t) 0)
          = fun s => deriv u 0 * g s 0 := by
        funext s
        simp only [pow_one]
        rw [deriv_fun_mul hu (hg s), hu0]
        ring
      rw [he]
      exact hg0.const_mul _

/-- The beta projection is homogeneous: no differentiability hypothesis needed. -/
theorem mixedD_const_mul (c : ℝ) (F : ℝ → ℝ → ℝ) :
    mixedD (fun s t => c * F s t) = c * mixedD F := by
  have hin : ∀ s : ℝ, deriv (fun t => c * F s t) 0 = c * deriv (fun t => F s t) 0 :=
    fun s => deriv_const_mul_field _
  rw [mixedD, funext hin, deriv_const_mul_field, mixedD]

/-- The beta projection is additive on functions whose slices are differentiable. -/
theorem mixedD_add {F G : ℝ → ℝ → ℝ}
    (hF : ∀ s, DifferentiableAt ℝ (fun t => F s t) 0)
    (hG : ∀ s, DifferentiableAt ℝ (fun t => G s t) 0)
    (hF' : DifferentiableAt ℝ (fun s => deriv (fun t => F s t) 0) 0)
    (hG' : DifferentiableAt ℝ (fun s => deriv (fun t => G s t) 0) 0) :
    mixedD (fun s t => F s t + G s t) = mixedD F + mixedD G := by
  have hin : ∀ s : ℝ, deriv (fun t => F s t + G s t) 0
      = deriv (fun t => F s t) 0 + deriv (fun t => G s t) 0 :=
    fun s => deriv_fun_add (hF s) (hG s)
  rw [mixedD, funext hin, deriv_fun_add hF' hG', mixedD, mixedD]

/-- The `t`-slice of a term with `b` lattice factors in `t` is differentiable. -/
theorem slice_differentiableAt {u : ℝ → ℝ} (hu : DifferentiableAt ℝ u 0)
    {g : ℝ → ℝ → ℝ} (hg : ∀ s, DifferentiableAt ℝ (fun t => g s t) 0) (a b : ℕ) (x : ℝ) :
    DifferentiableAt ℝ (fun t => u x ^ a * (u t ^ b * g x t)) 0 :=
  ((hu.pow b).mul (hg x)).const_mul _

/-- The inner `t`-derivative of a term with `b` lattice factors in `t`, seen as a
function of the other variable, is differentiable at the origin. -/
theorem slice_innerDeriv_differentiableAt {u : ℝ → ℝ} (hu0 : u 0 = 0)
    (hu : DifferentiableAt ℝ u 0) {g : ℝ → ℝ → ℝ}
    (hg : ∀ s, DifferentiableAt ℝ (fun t => g s t) 0)
    (hdg : DifferentiableAt ℝ (fun s => deriv (fun t => g s t) 0) 0)
    (hg0 : DifferentiableAt ℝ (fun s => g s 0) 0) (b : ℕ) :
    DifferentiableAt ℝ (fun x => deriv (fun t => u t ^ b * g x t) 0) 0 := by
  match b with
  | 0 =>
      have he : (fun x : ℝ => deriv (fun t => u t ^ 0 * g x t) 0)
          = fun x : ℝ => deriv (fun t => g x t) 0 := by
        funext x; simp
      rw [he]; exact hdg
  | 1 =>
      have he : (fun x : ℝ => deriv (fun t => u t ^ 1 * g x t) 0)
          = fun x : ℝ => deriv u 0 * g x 0 := by
        funext x
        simp only [pow_one]
        rw [deriv_fun_mul hu (hg x), hu0]
        ring
      rw [he]; exact hg0.const_mul _
  | (k + 2) =>
      have he : (fun x : ℝ => deriv (fun t => u t ^ (k + 2) * g x t) 0)
          = fun _ : ℝ => (0 : ℝ) := by
        funext x
        exact deriv_pow_mul_eq_zero hu0 hu (hg x) (by omega)
      rw [he]; exact differentiableAt_const _

/-- The full inner derivative of a third-order term is differentiable in the
remaining variable. -/
theorem thirdOrder_innerDeriv_differentiableAt {u : ℝ → ℝ} (hu0 : u 0 = 0)
    (hu : DifferentiableAt ℝ u 0) {g : ℝ → ℝ → ℝ}
    (hg : ∀ s, DifferentiableAt ℝ (fun t => g s t) 0)
    (hdg : DifferentiableAt ℝ (fun s => deriv (fun t => g s t) 0) 0)
    (hg0 : DifferentiableAt ℝ (fun s => g s 0) 0) (a b : ℕ) :
    DifferentiableAt ℝ
      (fun x => deriv (fun t => u x ^ a * (u t ^ b * g x t)) 0) 0 := by
  have he : (fun x : ℝ => deriv (fun t => u x ^ a * (u t ^ b * g x t)) 0)
      = fun x : ℝ => u x ^ a * deriv (fun t => u t ^ b * g x t) 0 := by
    funext x
    exact deriv_const_mul_field _
  rw [he]
  exact (hu.pow a).mul (slice_innerDeriv_differentiableAt hu0 hu hg hdg hg0 b)

/-! ## The beta projection in momentum space -/

/-- The two-dimensional slice through zero momentum spanned by the directions
`μ` and `ν`. -/
def momentumSlice (mu nu : Fin 4) (s t : ℝ) : Fin 4 → ℝ :=
  fun k => if k = mu then s else if k = nu then t else 0

@[simp] lemma momentumSlice_mu {mu nu : Fin 4} (s t : ℝ) :
    momentumSlice mu nu s t mu = s := by simp [momentumSlice]

@[simp] lemma momentumSlice_nu {mu nu : Fin 4} (h : nu ≠ mu) (s t : ℝ) :
    momentumSlice mu nu s t nu = t := by simp [momentumSlice, h]

lemma momentumSlice_other {mu nu kappa : Fin 4} (h1 : kappa ≠ mu) (h2 : kappa ≠ nu) (s t : ℝ) :
    momentumSlice mu nu s t kappa = 0 := by simp [momentumSlice, h1, h2]

/-- The beta projection `∂_{p_μ}∂_{p_ν} R (0)` of a momentum-space function. -/
noncomputable def mixedMomentumD (R : (Fin 4 → ℝ) → ℝ) (mu nu : Fin 4) : ℝ :=
  mixedD fun s t => R (momentumSlice mu nu s t)

/-- A term carrying a lattice derivative factor in a direction other than the two
differentiated ones vanishes identically on the slice, hence is annihilated by
the beta projection. -/
theorem mixedMomentumD_eq_zero_of_offSlice_factor {R rest : (Fin 4 → ℝ) → ℝ}
    {mu nu kappa : Fin 4} (h1 : kappa ≠ mu) (h2 : kappa ≠ nu)
    (hR : ∀ p, R p = phat (p kappa) * rest p) :
    mixedMomentumD R mu nu = 0 := by
  have hzero : ∀ s t : ℝ, R (momentumSlice mu nu s t) = 0 := by
    intro s t
    rw [hR, momentumSlice_other h1 h2, phat_zero, zero_mul]
  have he : (fun s t => R (momentumSlice mu nu s t)) = fun _ _ : ℝ => (0 : ℝ) := by
    funext s t; exact hzero s t
  rw [mixedMomentumD, he, mixedD]
  simp

/-- The literal lattice factor `p̂` vanishes at zero momentum and is smooth. -/
lemma differentiableAt_phat (x : ℝ) : DifferentiableAt ℝ phat x := by
  unfold phat sinAtom
  fun_prop

/-- **The beta projection annihilates a third-order remainder, for the literal
lattice factor `p̂`.**  If, on the slice spanned by the two differentiated
directions, the remainder is a product of three factors `p̂` with a smooth
prefactor, its beta projection vanishes. -/
theorem mixedMomentumD_eq_zero_of_thirdOrder {R : (Fin 4 → ℝ) → ℝ} {mu nu : Fin 4}
    {g : ℝ → ℝ → ℝ} {a b : ℕ} (hab : a + b = 3)
    (hR : ∀ s t : ℝ, R (momentumSlice mu nu s t)
      = phat s ^ a * (phat t ^ b * g s t))
    (hg : ∀ s, DifferentiableAt ℝ (fun t => g s t) 0)
    (hdg : DifferentiableAt ℝ (fun s => deriv (fun t => g s t) 0) 0)
    (hg0 : DifferentiableAt ℝ (fun s => g s 0) 0) :
    mixedMomentumD R mu nu = 0 := by
  have he : (fun s t => R (momentumSlice mu nu s t))
      = fun s t => phat s ^ a * (phat t ^ b * g s t) := by
    funext s t; exact hR s t
  rw [mixedMomentumD, he]
  exact betaProjection_kills_thirdOrder phat_zero (differentiableAt_phat 0) hg hdg hg0 hab

end YangMills
