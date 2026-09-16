/-
# Row A1a — the literal gauge-projection variation `R_gauge`

`AveragingLorentzDiagonal` and `LorentzBlockDiagonal` remove the averaging piece
`Q` and the constrained (`ker Q`) part of `R` from every mixed Lorentz component
of the constrained first variation `V = W + Q + R`.  What is left of `R` is the
genuinely non–block-diagonal part: the *gauge* projection along the gauge orbit
directions.

At a background configuration the gauge orbit direction of a colour function `ω`
is the covariant gradient `(D_α ω)_α`; in momentum space, at the trivial
background, that is the longitudinal vector `k_α`, and a background perturbation
in Lorentz direction `ρ` with structure-constant amplitude `f` deforms it to
`k_α + t · f δ_{αρ}`.  The gauge projection is the rank-one longitudinal
projector along this vector, and `R_gauge` is its derivative at `t = 0`.  This
file *computes* that derivative rather than budgeting it:

* `hasDerivAt_gaugeProjector` :

      d/dt |_{t=0}  (v_α v_β / |v|²)   with  v = k + t·c
        =  (c_α k_β + k_α c_β)/|k|²  −  2 k_α k_β (k·c)/|k|⁴,

  an honest `HasDerivAt` statement, not a postulated symbol.
* `gaugeVariationSymbol_eq` : the closed form for the background direction
  `c_α = f δ_{αρ}`.
* `gaugeVariationSymbol_mixed_eq`, `abs_gaugeVariationSymbol_mixed_le` : on a
  mixed Lorentz component `α ≠ β = ρ` the symbol is exactly
  `f k_α (|k|² − 2k_ρ²)/|k|⁴`, whose modulus is at most `|f| |k_α| / |k|²`.

The essential structural point is the factor `1/|k|²`: the gauge-projection
variation is *suppressed at large lattice momentum*, whereas the Wilson piece is
not.  That is what makes a patch pushed towards large transverse momentum a
good patch, and it is used in `MixedComponentPatch`.

**Honest status.**  The model here is the literal longitudinal projector of the
lattice gauge slice at the trivial background; identifying `f` with Bałaban's
normalisation of the background perturbation relative to the Wilson vertex
normalisation is a source obligation and is carried as an explicit parameter
throughout, never fixed silently.
-/
import RequestProject.YangMills.LatticeMomentum

namespace YangMills

open Real Finset

/-! ## 1. The longitudinal (gauge) projector and its variation -/

/-- The longitudinal projector along the vector `v`: `P_{αβ} = v_α v_β / |v|²`. -/
noncomputable def gaugeProjector (v : Fin 4 → ℝ) (al be : Fin 4) : ℝ :=
  v al * v be / ∑ ga : Fin 4, (v ga) ^ 2

/-- The first variation of the longitudinal projector in the direction `c`:

    (c_α k_β + k_α c_β)/|k|² − 2 k_α k_β (k·c)/|k|⁴. -/
noncomputable def gaugeProjectionVariation (k cv : Fin 4 → ℝ) (al be : Fin 4) : ℝ :=
  (cv al * k be + k al * cv be) / (∑ ga : Fin 4, (k ga) ^ 2)
    - 2 * (k al * k be) * (∑ ga : Fin 4, k ga * cv ga) / (∑ ga : Fin 4, (k ga) ^ 2) ^ 2

/-- **The gauge-projection variation is a genuine derivative.** -/
theorem hasDerivAt_gaugeProjector (k cv : Fin 4 → ℝ) (al be : Fin 4)
    (hk : (∑ ga : Fin 4, (k ga) ^ 2) ≠ 0) :
    HasDerivAt (fun t : ℝ => gaugeProjector (fun ga => k ga + t * cv ga) al be)
      (gaugeProjectionVariation k cv al be) 0 := by
  have hv : ∀ ga : Fin 4, HasDerivAt (fun t : ℝ => k ga + t * cv ga) (cv ga) 0 := by
    intro ga
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (cv ga)).const_add (k ga)
  have hnum : HasDerivAt (fun t : ℝ => (k al + t * cv al) * (k be + t * cv be))
      (cv al * k be + k al * cv be) 0 := by
    have := (hv al).mul (hv be)
    simpa using this
  have hsq : ∀ ga : Fin 4,
      HasDerivAt (fun t : ℝ => (k ga + t * cv ga) ^ 2) (2 * k ga * cv ga) 0 := by
    intro ga
    have := (hv ga).pow 2
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  have hden : HasDerivAt (fun t : ℝ => ∑ ga : Fin 4, (k ga + t * cv ga) ^ 2)
      (2 * ∑ ga : Fin 4, k ga * cv ga) 0 := by
    have := HasDerivAt.sum (u := Finset.univ) (fun ga _ => hsq ga)
    rw [Finset.mul_sum]
    simpa [mul_assoc] using this
  have hden0 : (∑ ga : Fin 4, (k ga + (0 : ℝ) * cv ga) ^ 2) ≠ 0 := by simpa using hk
  have hdiv := hnum.div hden hden0
  have hfun : (fun t : ℝ => gaugeProjector (fun ga => k ga + t * cv ga) al be)
      = fun t : ℝ => ((k al + t * cv al) * (k be + t * cv be))
          / ∑ ga : Fin 4, (k ga + t * cv ga) ^ 2 := rfl
  rw [hfun]
  convert hdiv using 1
  have hz : (∑ ga : Fin 4, (k ga + (0 : ℝ) * cv ga) ^ 2) = ∑ ga : Fin 4, (k ga) ^ 2 := by
    simp
  rw [gaugeProjectionVariation, hz]
  simp only [zero_mul, add_zero]
  field_simp

/-! ## 2. The symbol for a background perturbation in one Lorentz direction -/

/-- The gauge-projection variation for a background perturbation of amplitude
`f` in Lorentz direction `ρ`, i.e. `c_α = f δ_{αρ}`. -/
noncomputable def gaugeVariationSymbol (f : ℝ) (k : Fin 4 → ℝ) (rho al be : Fin 4) : ℝ :=
  gaugeProjectionVariation k (fun ga => if ga = rho then f else 0) al be

/-- Closed form of the gauge-projection variation symbol. -/
theorem gaugeVariationSymbol_eq (f : ℝ) (k : Fin 4 → ℝ) (rho al be : Fin 4) :
    gaugeVariationSymbol f k rho al be
      = ((if al = rho then f else 0) * k be + k al * (if be = rho then f else 0))
          / (∑ ga : Fin 4, (k ga) ^ 2)
        - 2 * (k al * k be) * (f * k rho) / (∑ ga : Fin 4, (k ga) ^ 2) ^ 2 := by
  unfold gaugeVariationSymbol gaugeProjectionVariation
  congr 2
  · have : (∑ ga : Fin 4, k ga * (if ga = rho then f else 0)) = k rho * f := by
      simp
    rw [this]; ring

/-- **The mixed component.**  For `α ≠ β` with the background index `ρ = β`, the
gauge-projection variation is exactly `f k_α (|k|² − 2 k_ρ²)/|k|⁴`. -/
theorem gaugeVariationSymbol_mixed_eq (f : ℝ) (k : Fin 4 → ℝ) {rho al : Fin 4}
    (hne : al ≠ rho) (hk : (∑ ga : Fin 4, (k ga) ^ 2) ≠ 0) :
    gaugeVariationSymbol f k rho al rho
      = f * k al * ((∑ ga : Fin 4, (k ga) ^ 2) - 2 * (k rho) ^ 2)
          / (∑ ga : Fin 4, (k ga) ^ 2) ^ 2 := by
  rw [gaugeVariationSymbol_eq, if_neg hne, if_pos rfl]
  field_simp
  ring

/-- Scalar bound used for the mixed component: `|u·A/N²| ≤ |u|/N` when
`|A| ≤ N`. -/
theorem abs_mul_div_sq_le {u A N : ℝ} (hN : 0 < N) (hA : |A| ≤ N) :
    |u * A / N ^ 2| ≤ |u| / N := by
  rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < N ^ 2)]
  have h1 : |u| * |A| ≤ |u| * N := by
    exact mul_le_mul_of_nonneg_left hA (abs_nonneg u)
  have h2 : |u| * N / N ^ 2 = |u| / N := by
    field_simp
  calc |u| * |A| / N ^ 2 ≤ |u| * N / N ^ 2 := by gcongr
    _ = |u| / N := h2

/-- **The mixed gauge-projection variation is suppressed by `1/|k|²`.** -/
theorem abs_gaugeVariationSymbol_mixed_le (f : ℝ) (k : Fin 4 → ℝ) {rho al : Fin 4}
    (hne : al ≠ rho) (hk : 0 < ∑ ga : Fin 4, (k ga) ^ 2) :
    |gaugeVariationSymbol f k rho al rho| ≤ |f| * |k al| / (∑ ga : Fin 4, (k ga) ^ 2) := by
  have hrho : (k rho) ^ 2 ≤ ∑ ga : Fin 4, (k ga) ^ 2 :=
    Finset.single_le_sum (f := fun ga : Fin 4 => (k ga) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ rho)
  have hfac : |(∑ ga : Fin 4, (k ga) ^ 2) - 2 * (k rho) ^ 2| ≤ ∑ ga : Fin 4, (k ga) ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (k rho)]
  have hmul : |f * k al| = |f| * |k al| := abs_mul _ _
  rw [gaugeVariationSymbol_mixed_eq f k hne hk.ne', ← hmul]
  exact abs_mul_div_sq_le hk hfac

end YangMills
