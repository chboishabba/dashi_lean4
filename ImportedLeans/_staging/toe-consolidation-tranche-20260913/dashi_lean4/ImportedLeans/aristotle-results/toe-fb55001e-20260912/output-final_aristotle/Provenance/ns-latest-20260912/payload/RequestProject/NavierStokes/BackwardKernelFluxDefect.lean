/-
# `A*`: the backward-kernel flux defect and the logarithmic-defect theorem

Instead of differentiating the sharp cylinder quantity `Q_∇(r)` one localizes
with a smoothed backward caloric kernel,

  `𝒟(r) = ∫∫ |∇u|² Γ_{r,z₀} χ_{r,z₀}`,

and derives the **exact scale derivative**

  `r·𝒟'(r) = 𝓕_{adv+pres}(r) + 𝓛(r)`,                                  (A-HK)

with `𝓛` supported in the cutoff annulus.  The goal is then not a sign for the
flux, but the *logarithmic* integrability

  `∫_{1/M}^{M^{-2/3}} [𝓕(r) + 𝓛(r)]_+ / 𝒟(r) · dr/r ≤ C`.                (A*)

This file makes that statement precise and proves everything downstream of it:

* `ClayNS.nsLogDefect` — the defect density is *identified*, not postulated:
  `D_NS(r) = [𝓕(r)+𝓛(r)]_+ / (r·𝒟(r))`, so that `∫ D_NS dr` is literally the
  left-hand side of (A*) (`nsLogDefect_eq_log_density`).
* `ClayNS.scale_derivative_le_nsLogDefect` — (A-HK) implies, with **no sign
  hypothesis on the flux at all**, the almost-monotonicity inequality
  `r𝒟'(r) ≤ r·D_NS(r)·𝒟(r)`.
* `ClayNS.backward_kernel_flux_defect_propagates` — hence the defect propagates
  from the energy scale to the velocity scale with the single loss
  `e^{−(Φ(b)−Φ(a))}`, `Φ` a primitive of `D_NS`.
* `ClayNS.backward_kernel_flux_defect_integrable` — **`BackwardKernelFluxDefectIntegrable`**
  in its usable form: if the logarithmic defect (A*) is bounded by `C`, the
  defect survives at the bottom scale with the constant `e^{−C}ε`, which is
  independent of the number of dyadic steps and hence of `M`.
* `ClayNS.clay_A_dyn_of_uniform_log_defect` — and, applied along a singular
  sequence with `𝒟 = Q_∇`, that constant yields the gate
  `DynamicVelocityScaleDefect`, i.e. `A_dyn`.

What is **not** proved here is (A*) itself, nor (A-HK): both are hypotheses of
the statements below.  That is exactly the frontier item `A*`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.FrequencyAlmostMonotone
import RequestProject.NavierStokes.DynamicDefectReduction

open Filter Topology Set

noncomputable section

namespace ClayNS

/-! ## The identified defect density -/

/-- **The Navier–Stokes logarithmic defect density.**  With `F` the localized
signed flux of (A-HK) and `Dsc` the backward-kernel dissipation `𝒟`,

`D_NS(r) = [F(r)]_+ / (r·𝒟(r))`.

This is not an abstract `D(r)`: it is read off the scale-derivative identity. -/
def nsLogDefect (F Dsc : ℝ → ℝ) : ℝ → ℝ := fun r => max (F r) 0 / (r * Dsc r)

/-- `D_NS` is a logarithmic density: `D_NS(r)·dr = ([F]_+/𝒟)·dr/r`. -/
lemma nsLogDefect_eq_log_density (F Dsc : ℝ → ℝ) (r : ℝ) :
    nsLogDefect F Dsc r = (max (F r) 0 / Dsc r) / r := by
  simp only [nsLogDefect]
  rw [div_div, mul_comm]

lemma nsLogDefect_nonneg {F Dsc : ℝ → ℝ} {r : ℝ} (hr : 0 < r) (hD : 0 < Dsc r) :
    0 ≤ nsLogDefect F Dsc r :=
  div_nonneg (le_max_right _ _) (by positivity)

/-! ## (A-HK) gives almost monotonicity, with no sign hypothesis -/

/-- **The scale-derivative identity implies the almost-monotonicity
inequality.**  If `r·𝒟'(r) = F(r)` then `r·𝒟'(r) ≤ r·D_NS(r)·𝒟(r)`: the flux
need not have a sign, its positive part is simply absorbed into the defect
density. -/
theorem scale_derivative_le_nsLogDefect {F Dsc : ℝ → ℝ} {Dd : ℝ → ℝ} {r : ℝ}
    (hr : 0 < r) (hD : 0 < Dsc r) (hexact : r * Dd r = F r) :
    r * Dd r ≤ r * nsLogDefect F Dsc r * Dsc r := by
  have hpos : 0 < r * Dsc r := by positivity
  have hcancel : r * nsLogDefect F Dsc r * Dsc r = max (F r) 0 := by
    simp only [nsLogDefect]
    field_simp
  rw [hexact, hcancel]
  exact le_max_left _ _

/-- **The defect propagates under (A-HK).**  With `Φ` a primitive of the
identified defect density `D_NS`, an `ε`-defect at the top scale `b` survives
at the bottom scale `a` with the single factor `e^{−(Φ(b)−Φ(a))}`. -/
theorem backward_kernel_flux_defect_propagates {F Dsc Dd Phi : ℝ → ℝ} {a b eps : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hpos : ∀ r ∈ Icc a b, 0 < Dsc r)
    (hderiv : ∀ r ∈ Icc a b, HasDerivAt Dsc (Dd r) r)
    (hPhi : ∀ r ∈ Icc a b, HasDerivAt Phi (nsLogDefect F Dsc r) r)
    (hexact : ∀ r ∈ Icc a b, r * Dd r = F r)
    (hstart : eps ≤ Dsc b) :
    Real.exp (-(Phi b - Phi a)) * eps ≤ Dsc a := by
  refine almostMonotone_defect_propagates (H := Dsc) (H' := Dd)
    (D := nsLogDefect F Dsc) ha hab hpos hderiv hPhi (fun r hr => ?_) hstart
  exact scale_derivative_le_nsLogDefect (lt_of_lt_of_le ha hr.1) (hpos r hr) (hexact r hr)

/-- **`BackwardKernelFluxDefectIntegrable`.**  If, in addition, the logarithmic
defect (A*) is bounded by `C` — i.e. `∫_a^b [F]_+/𝒟 · dr/r ≤ C`, which is
`Φ(b) − Φ(a) ≤ C` for a primitive `Φ` of `D_NS` — then the bottom-scale defect
is at least `e^{−C}·ε`, a constant that does not degrade as the scale range
grows. -/
theorem backward_kernel_flux_defect_integrable {F Dsc Dd Phi : ℝ → ℝ} {a b eps C : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (heps : 0 ≤ eps)
    (hpos : ∀ r ∈ Icc a b, 0 < Dsc r)
    (hderiv : ∀ r ∈ Icc a b, HasDerivAt Dsc (Dd r) r)
    (hPhi : ∀ r ∈ Icc a b, HasDerivAt Phi (nsLogDefect F Dsc r) r)
    (hexact : ∀ r ∈ Icc a b, r * Dd r = F r)
    (hlog : Phi b - Phi a ≤ C)
    (hstart : eps ≤ Dsc b) :
    Real.exp (-C) * eps ≤ Dsc a := by
  have hmain := backward_kernel_flux_defect_propagates ha hab hpos hderiv hPhi hexact hstart
  have hmono : Real.exp (-C) ≤ Real.exp (-(Phi b - Phi a)) := Real.exp_le_exp.mpr (by linarith)
  exact le_trans (mul_le_mul_of_nonneg_right hmono heps) hmain

/-! ## The consequence for the `A` frontier item -/

/-- **`A*` ⇒ `A_dyn`.**  Along a singular sequence, if the scale-invariant
gradient energy obeys the exact scale-derivative identity (A-HK) on
`[1/M_k, cascadeStart M_k]` with a logarithmic defect bounded by a single
constant `C` *uniformly in `k`*, then the velocity-scale defect gate holds:
there are `c, ε' > 0` with `Q_∇(u_k; x_k, t_k, c/M_k) ≥ ε'` for every `k`. -/
theorem clay_A_dyn_of_uniform_log_defect {G : ℕ → ℝ → E3 → ℝ} {M : ℕ → ℝ}
    {t : ℕ → ℝ} {x : ℕ → E3} {F Qd Phi : ℕ → ℝ → ℝ} {eps C : ℝ}
    (heps : 0 < eps) (hM : ∀ k, 0 < M k)
    (hle : ∀ k, 1 / M k ≤ cascadeStart (M k))
    (hpos : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)), 0 < QgradCyl (G k) (t k) (x k) r)
    (hderiv : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      HasDerivAt (fun s => QgradCyl (G k) (t k) (x k) s) (Qd k r) r)
    (hPhi : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      HasDerivAt (Phi k) (nsLogDefect (F k) (fun s => QgradCyl (G k) (t k) (x k) s) r) r)
    (hexact : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)), r * Qd k r = F k r)
    (hlog : ∀ k, Phi k (cascadeStart (M k)) - Phi k (1 / M k) ≤ C)
    (hstart : ∀ k, eps ≤ QgradCyl (G k) (t k) (x k) (cascadeStart (M k))) :
    DynamicVelocityScaleDefect G M t x := by
  refine dynamicVelocityScaleDefect_of_almostMonotone (E := C) heps fun k => ?_
  exact backward_kernel_flux_defect_integrable (by have := hM k; positivity) (hle k) heps.le
    (hpos k) (hderiv k) (hPhi k) (hexact k) (hlog k) (hstart k)

end ClayNS
