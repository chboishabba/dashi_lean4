import Mathlib
import Integration.Experiment.ParameterRegion
import Integration.Experiment.InformationMatrix
import Integration.Experiment.ModelDiscrepancy

/-!
# Stage 7 — the acceptance specimen: an RC circuit

The Stage-6 acceptance instance was a synthetic scalar cell.  The Stage-7
specimen is a *recognisably scientific* dynamical system with a closed-form
solution, chosen because it exhibits the antipattern this stage is about:

```
C dV/dt = (V_in − V)/R,        V(t) = V_in + (V₀ − V_in) e^{−t/(RC)}
```

Two unknowns `(R, C)`, one observable `V(t)`.  Because the solution depends on
`(R, C)` **only through the product** `τ = RC`, no experiment of this kind can
separate them:

```
perfect measurements  ⇏  parameter identifiability.
```

That is a *structural* obstruction, not a noise problem, and this file proves it
in the strongest available form: for **every** finite set of measurement times,
and with **zero** tolerance, the surviving region contains a whole hyperbola,
and the measurement Jacobian has the invisible direction `(R, −C)` — hence the
information matrix of every such design is singular.

Reparameterising by `τ` removes the obstruction entirely, and then the design
question has a clean answer: `t = τ` is the most informative sampling time.

## What is proved

| Statement | Kind | Content |
|---|---|---|
| `voltage_hasDerivAt`, `rc_solves_the_ode` | theorem | the closed form really solves `C V̇ = (V_in − V)/R` |
| `voltage_at_zero` | theorem | and meets the initial condition |
| `voltage_depends_only_on_the_product` | theorem | `(R,C)` enters only through `RC` |
| **`perfect_measurements_do_not_identify_R_and_C`** | theorem | for *any* dataset, `(R,C)` compatible ⇒ `(2R, C/2)` compatible and different |
| **`no_dataset_identifies_the_pair`** | theorem | hence no dataset of any size makes the surviving region a single point |
| `vtau_injOn`, `exact_reading_identifies_tau` | theorem | after reparameterisation by `τ = RC` a single exact reading identifies the parameter |
| `vtau_hasDerivAt_tau` | theorem | the certified parameter sensitivity `∂V/∂τ = (V₀−V_in) e^{−t/τ} t/τ²` |
| **`most_informative_time_is_tau`** | theorem | `t e^{−t/τ} ≤ τ e^{−1}` with equality at `t = τ`: the optimal sampling time is one time constant |
| `voltage_hasDerivAt_R`, `voltage_hasDerivAt_C` | theorem | the certified `(∂V/∂R, ∂V/∂C)` row |
| **`rc_design_has_an_invisible_direction`** | theorem | `(R, −C)` is killed by the Jacobian of *every* multi-time design |
| **`rc_information_is_singular`** | theorem | so `det F = 0` for every weighting: the D-criterion detects the obstruction |
| `family_falsified_by_an_impossible_reading` | theorem | and the family is still genuinely refutable |

## Claim boundary

`voltage` is a declared function; no theorem says a physical capacitor obeys it.
"Identifiable" means injectivity of the declared measurement map, and
"information" is `JᵀWJ` for the certified `J` — see `InformationMatrix` for what
that name does and does not license.
-/

namespace Integration.Experiment.RCCircuit

open Set Matrix
open Integration.Experiment.ParameterRegion
open Integration.Experiment.JacobianSensitivity
open Integration.Experiment.InformationMatrix

/-! ## §1 The model and its closed form -/

/-- The step response of an RC circuit, in the time constant `τ`. -/
noncomputable def vtau (Vin V0 τ t : ℝ) : ℝ := Vin + (V0 - Vin) * Real.exp (-t / τ)

/-- The step response in the physical parameters `(R, C)`. -/
noncomputable def voltage (Vin V0 R C t : ℝ) : ℝ := vtau Vin V0 (R * C) t

@[simp] theorem voltage_eq_vtau (Vin V0 R C t : ℝ) :
    voltage Vin V0 R C t = vtau Vin V0 (R * C) t := rfl

@[simp] theorem voltage_at_zero (Vin V0 R C : ℝ) : voltage Vin V0 R C 0 = V0 := by
  simp [voltage, vtau]

/-- The certified time derivative of the closed form. -/
theorem vtau_hasDerivAt_time (Vin V0 τ : ℝ) (hτ : τ ≠ 0) (t : ℝ) :
    HasDerivAt (fun s => vtau Vin V0 τ s) ((Vin - vtau Vin V0 τ t) / τ) t := by
  have hlin : HasDerivAt (fun s : ℝ => -s / τ) (-1 / τ) t := by
    simpa [neg_div] using ((hasDerivAt_id t).neg.div_const τ)
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-s / τ))
      (Real.exp (-t / τ) * (-1 / τ)) t := by
    simpa [mul_comm] using (Real.hasDerivAt_exp (-t / τ)).comp t hlin
  have hmul := hexp.const_mul (V0 - Vin)
  have hres := hmul.const_add Vin
  have heq : (V0 - Vin) * (Real.exp (-t / τ) * (-1 / τ)) = (Vin - vtau Vin V0 τ t) / τ := by
    simp only [vtau]
    field_simp
    ring
  rw [heq] at hres
  exact hres

/-- **The closed form solves the circuit equation** `C V̇ = (V_in − V)/R`. -/
theorem rc_solves_the_ode (Vin V0 R C : ℝ) (hR : R ≠ 0) (hC : C ≠ 0) (t : ℝ) :
    HasDerivAt (fun s => voltage Vin V0 R C s)
      ((Vin - voltage Vin V0 R C t) / (R * C)) t :=
  vtau_hasDerivAt_time Vin V0 (R * C) (mul_ne_zero hR hC) t

/-! ## §2 The structural obstruction -/

/-- **The observable depends on `(R, C)` only through the product.** -/
theorem voltage_depends_only_on_the_product (Vin V0 R C R' C' : ℝ) (h : R * C = R' * C')
    (t : ℝ) : voltage Vin V0 R C t = voltage Vin V0 R' C' t := by
  simp [voltage, h]

/-- The two-parameter RC family: positive `R` and `C`, observable `V(t)`. -/
noncomputable def rcFamily (Vin V0 : ℝ) : ParamFamily (ℝ × ℝ) where
  prior := {q | 0 < q.1 ∧ 0 < q.2}
  predict := fun q t => voltage Vin V0 q.1 q.2 t

@[simp] theorem rcFamily_predict (Vin V0 : ℝ) (q : ℝ × ℝ) (t : ℝ) :
    (rcFamily Vin V0).predict q t = voltage Vin V0 q.1 q.2 t := rfl

/-- **Perfect measurements do not identify `R` and `C`.**  Whatever the dataset —
however many readings, however tight the tolerances, even exact — if `(R, C)`
survives then so does the different pair `(2R, C/2)`. -/
theorem perfect_measurements_do_not_identify_R_and_C (Vin V0 : ℝ) (E : List Reading)
    {R C : ℝ} (h : (R, C) ∈ Compatible (rcFamily Vin V0) E) :
    ((2 * R, C / 2) ∈ Compatible (rcFamily Vin V0) E) ∧ (2 * R, C / 2) ≠ (R, C) := by
  obtain ⟨⟨hR, hC⟩, hfit⟩ := h
  have hprod : (2 * R) * (C / 2) = R * C := by ring
  constructor
  · refine ⟨⟨by linarith, by linarith⟩, fun r hr => ?_⟩
    have hthis := hfit r hr
    rw [Fits] at hthis ⊢
    simp only [rcFamily_predict, voltage_eq_vtau] at hthis ⊢
    rw [show (2 * R) * (C / 2) = R * C by ring]
    exact hthis
  · intro hcon
    have : 2 * R = R := congrArg Prod.fst hcon
    linarith

/-- **No dataset identifies the pair.**  The surviving region is never a single
point: there is no experiment in this language that measures `R` and `C`
separately.  This is the promised

```
perfect measurements  ⇏  parameter identifiability.
```
-/
theorem no_dataset_identifies_the_pair (Vin V0 : ℝ) (E : List Reading)
    (hne : (Compatible (rcFamily Vin V0) E).Nonempty) :
    ¬ ∃ q : ℝ × ℝ, Compatible (rcFamily Vin V0) E = {q} := by
  rintro ⟨q, hq⟩
  obtain ⟨w, hw⟩ := hne
  have hwq : w = q := by rw [hq] at hw; exact hw
  subst hwq
  obtain ⟨hmem, hne'⟩ :=
    perfect_measurements_do_not_identify_R_and_C Vin V0 E (R := w.1) (C := w.2) (by simpa using hw)
  rw [hq] at hmem
  exact hne' hmem

/-! ## §3 The reparameterised family is identifiable -/

/-- **`τ ↦ V(t)` is injective on the positive time constants**, for any fixed
positive reading time and any non-degenerate step.  Reparameterising by
`τ = RC` removes the obstruction completely. -/
theorem vtau_injOn (Vin V0 t : ℝ) (ht : 0 < t) (hV : V0 ≠ Vin) :
    InjOn (fun τ => vtau Vin V0 τ t) (Ioi 0) := by
  intro τ₁ h₁ τ₂ h₂ heq
  simp only [vtau, add_right_inj] at heq
  have hsub : V0 - Vin ≠ 0 := sub_ne_zero.mpr hV
  have hexp : Real.exp (-t / τ₁) = Real.exp (-t / τ₂) := mul_left_cancel₀ hsub heq
  have harg : -t / τ₁ = -t / τ₂ := Real.exp_eq_exp.mp hexp
  have h1 : (0 : ℝ) < τ₁ := h₁
  have h2 : (0 : ℝ) < τ₂ := h₂
  rw [neg_div, neg_div, neg_inj] at harg
  have hcross := (div_eq_div_iff (ne_of_gt h1) (ne_of_gt h2)).mp harg
  exact (mul_left_cancel₀ (ne_of_gt ht) hcross).symm

/-- The reparameterised family. -/
noncomputable def tauFamily (Vin V0 : ℝ) : ParamFamily ℝ where
  prior := Ioi 0
  predict := fun τ t => vtau Vin V0 τ t

/-- **One exact reading identifies the time constant.** -/
theorem exact_reading_identifies_tau (Vin V0 : ℝ) (hV : V0 ≠ Vin) {t : ℝ} (ht : 0 < t)
    {τ₀ : ℝ} (hτ₀ : 0 < τ₀) {τ : ℝ}
    (h : τ ∈ Compatible (tauFamily Vin V0) [⟨t, vtau Vin V0 τ₀ t, 0, le_refl 0⟩]) :
    τ = τ₀ := by
  obtain ⟨hp, hfit⟩ := h
  have h1 : |vtau Vin V0 τ₀ t - vtau Vin V0 τ t| ≤ 0 :=
    hfit ⟨t, vtau Vin V0 τ₀ t, 0, le_refl 0⟩ (List.mem_cons_self ..)
  have h2 : vtau Vin V0 τ₀ t - vtau Vin V0 τ t = 0 := abs_nonpos_iff.mp h1
  exact vtau_injOn Vin V0 t ht hV hp hτ₀ (by linarith)

/-! ## §4 The parameter sensitivity and the best sampling time -/

/-- **The certified parameter sensitivity** `∂V/∂τ = (V₀ − V_in) e^{−t/τ} · t/τ²`. -/
theorem vtau_hasDerivAt_tau (Vin V0 t : ℝ) {τ : ℝ} (hτ : τ ≠ 0) :
    HasDerivAt (fun s => vtau Vin V0 s t)
      ((V0 - Vin) * Real.exp (-t / τ) * (t / τ ^ 2)) τ := by
  have hlin : HasDerivAt (fun s : ℝ => -t / s) (t / τ ^ 2) τ := by
    have hinv : HasDerivAt (fun s : ℝ => s⁻¹) (-(τ ^ 2)⁻¹) τ := hasDerivAt_inv hτ
    have hmul := hinv.const_mul (-t)
    have heq : -t * -(τ ^ 2)⁻¹ = t / τ ^ 2 := by field_simp
    rw [heq] at hmul
    simpa [div_eq_mul_inv] using hmul
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-t / s))
      (Real.exp (-t / τ) * (t / τ ^ 2)) τ := by
    simpa [mul_comm] using (Real.hasDerivAt_exp (-t / τ)).comp τ hlin
  have hmul := hexp.const_mul (V0 - Vin)
  have hres := hmul.const_add Vin
  have heq : (V0 - Vin) * (Real.exp (-t / τ) * (t / τ ^ 2))
      = (V0 - Vin) * Real.exp (-t / τ) * (t / τ ^ 2) := by ring
  rw [heq] at hres
  exact hres

/-- **The most informative sampling time is one time constant.**  The size of the
parameter sensitivity at time `t` is proportional to `t e^{−t/τ}`, which is
maximised exactly at `t = τ`. -/
theorem most_informative_time_is_tau {τ : ℝ} (hτ : 0 < τ) :
    (∀ t, t * Real.exp (-t / τ) ≤ τ * Real.exp (-1)) ∧
      τ * Real.exp (-τ / τ) = τ * Real.exp (-1) := by
  have hτ' : τ ≠ 0 := ne_of_gt hτ
  constructor
  · intro t
    have hkey : t / τ ≤ Real.exp (t / τ - 1) := by
      have := Real.add_one_le_exp (t / τ - 1)
      linarith
    have hpos : (0 : ℝ) < Real.exp (-(t / τ)) := Real.exp_pos _
    have hmul : (t / τ) * Real.exp (-(t / τ)) ≤ Real.exp (t / τ - 1) * Real.exp (-(t / τ)) :=
      mul_le_mul_of_nonneg_right hkey (le_of_lt hpos)
    have hsimp : Real.exp (t / τ - 1) * Real.exp (-(t / τ)) = Real.exp (-1) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hfac : t * Real.exp (-(t / τ)) = τ * ((t / τ) * Real.exp (-(t / τ))) := by
      field_simp
    rw [neg_div]
    calc t * Real.exp (-(t / τ)) = τ * ((t / τ) * Real.exp (-(t / τ))) := hfac
      _ ≤ τ * (Real.exp (t / τ - 1) * Real.exp (-(t / τ))) :=
          mul_le_mul_of_nonneg_left hmul (le_of_lt hτ)
      _ = τ * Real.exp (-1) := by rw [hsimp]
  · rw [neg_div, div_self hτ']

/-! ## §5 The Jacobian in the physical parameters -/

/-- The certified `∂V/∂R`. -/
theorem voltage_hasDerivAt_R (Vin V0 C t : ℝ) {R : ℝ} (hR : R ≠ 0) (hC : C ≠ 0) :
    HasDerivAt (fun r => voltage Vin V0 r C t)
      ((V0 - Vin) * Real.exp (-t / (R * C)) * (t / (R ^ 2 * C))) R := by
  have hτ : R * C ≠ 0 := mul_ne_zero hR hC
  have hcomp : HasDerivAt (fun r : ℝ => r * C) C R := by
    simpa using (hasDerivAt_id R).mul_const C
  have h := (vtau_hasDerivAt_tau Vin V0 t hτ).comp R hcomp
  have heq : (V0 - Vin) * Real.exp (-t / (R * C)) * (t / (R * C) ^ 2) * C
      = (V0 - Vin) * Real.exp (-t / (R * C)) * (t / (R ^ 2 * C)) := by
    field_simp
  rw [heq] at h
  exact h

/-- The certified `∂V/∂C`. -/
theorem voltage_hasDerivAt_C (Vin V0 R t : ℝ) {C : ℝ} (hR : R ≠ 0) (hC : C ≠ 0) :
    HasDerivAt (fun c => voltage Vin V0 R c t)
      ((V0 - Vin) * Real.exp (-t / (R * C)) * (t / (R * C ^ 2))) C := by
  have hτ : R * C ≠ 0 := mul_ne_zero hR hC
  have hcomp : HasDerivAt (fun c : ℝ => R * c) R C := by
    simpa using (hasDerivAt_id C).const_mul R
  have h := (vtau_hasDerivAt_tau Vin V0 t hτ).comp C hcomp
  have heq : (V0 - Vin) * Real.exp (-t / (R * C)) * (t / (R * C) ^ 2) * R
      = (V0 - Vin) * Real.exp (-t / (R * C)) * (t / (R * C ^ 2)) := by
    field_simp
  rw [heq] at h
  exact h

/-- The measurement Jacobian of a design that reads the voltage at the times
`ts`: row `i` is `(∂V/∂R, ∂V/∂C)` at time `ts i`. -/
noncomputable def rcJacobian (Vin V0 R C : ℝ) {m : ℕ} (ts : Fin m → ℝ) :
    Matrix (Fin m) (Fin 2) ℝ :=
  fun i k =>
    if k = 0 then (V0 - Vin) * Real.exp (-ts i / (R * C)) * (ts i / (R ^ 2 * C))
    else (V0 - Vin) * Real.exp (-ts i / (R * C)) * (ts i / (R * C ^ 2))

/-- Each entry of `rcJacobian` is the corresponding certified partial
derivative. -/
theorem rcJacobian_is_certified (Vin V0 : ℝ) {R C : ℝ} (hR : R ≠ 0) (hC : C ≠ 0)
    {m : ℕ} (ts : Fin m → ℝ) (i : Fin m) :
    HasDerivAt (fun r => voltage Vin V0 r C (ts i)) (rcJacobian Vin V0 R C ts i 0) R ∧
      HasDerivAt (fun c => voltage Vin V0 R c (ts i)) (rcJacobian Vin V0 R C ts i 1) C := by
  constructor
  · simpa [rcJacobian] using voltage_hasDerivAt_R Vin V0 C (ts i) hR hC
  · simpa [rcJacobian] using voltage_hasDerivAt_C Vin V0 R (ts i) hR hC

/-- **Every RC design has the invisible direction `(R, −C)`.**  However many
times are sampled, the Jacobian kills the direction along which `R` and `C`
change with `RC` fixed. -/
theorem rc_design_has_an_invisible_direction (Vin V0 : ℝ) {R C : ℝ} (hR : R ≠ 0) (hC : C ≠ 0)
    {m : ℕ} (ts : Fin m → ℝ) :
    rcJacobian Vin V0 R C ts *ᵥ ![R, -C] = 0 := by
  funext i
  have h0 : rcJacobian Vin V0 R C ts i 0
      = (V0 - Vin) * Real.exp (-ts i / (R * C)) * (ts i / (R ^ 2 * C)) := by
    simp [rcJacobian]
  have h1 : rcJacobian Vin V0 R C ts i 1
      = (V0 - Vin) * Real.exp (-ts i / (R * C)) * (ts i / (R * C ^ 2)) := by
    simp [rcJacobian]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0, h1, Matrix.cons_val_zero,
    Matrix.cons_val_one, Pi.zero_apply]
  field_simp
  ring

/-- The invisible direction is nonzero. -/
theorem rc_invisible_direction_ne_zero {R C : ℝ} (hR : R ≠ 0) : (![R, -C] : Fin 2 → ℝ) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp at this
  exact hR this

/-- **The information matrix of every RC design is singular**, for every
weighting.  The D-criterion of `InformationMatrix` therefore *detects* the
structural non-identifiability: no choice of sampling times can make it
nonzero. -/
theorem rc_information_is_singular (Vin V0 : ℝ) {R C : ℝ} (hR : R ≠ 0) (hC : C ≠ 0)
    {m : ℕ} (ts : Fin m → ℝ) (W : RCov m) (hW : PosDefWeight W) :
    (infoMatrix (rcJacobian Vin V0 R C ts) W).toMatrix.det = 0 :=
  (singular_iff_invisible_direction hW).2
    ⟨![R, -C], rc_invisible_direction_ne_zero hR,
      rc_design_has_an_invisible_direction Vin V0 hR hC ts⟩

/-! ## §6 The family is still refutable -/

/-- With `V_in = 0` and `V₀ = 1` the response never exceeds `1`, so a reading of
`2` refutes the whole family: structural non-identifiability is not vacuity. -/
theorem family_falsified_by_an_impossible_reading :
    Compatible (rcFamily 0 1) [⟨1, 2, 0, le_refl 0⟩] = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro q ⟨⟨hR, hC⟩, hfit⟩
  have h1 : |(2 : ℝ) - voltage 0 1 q.1 q.2 1| ≤ 0 :=
    hfit ⟨1, 2, 0, le_refl 0⟩ (List.mem_cons_self ..)
  have h2 : (2 : ℝ) - voltage 0 1 q.1 q.2 1 = 0 := abs_nonpos_iff.mp h1
  have hle : voltage 0 1 q.1 q.2 1 ≤ 1 := by
    have hpos : 0 < q.1 * q.2 := mul_pos hR hC
    have : Real.exp (-1 / (q.1 * q.2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (le_of_lt hpos)
    simpa [voltage, vtau] using this
  linarith

end Integration.Experiment.RCCircuit
