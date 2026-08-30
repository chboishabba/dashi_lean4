/-
# The cutoff-weighted structure function and its separation derivatives

This file builds the two-point objects of the Kármán–Howarth/Monin picture for
the increments `δ_h u = u(·+h) − u` of a smooth periodic solution:

* `ClayNS.strFun Φ u t h = ∫_cell Φ(x)|u(t,x+h) − u(t,x)|² dx` — the
  cutoff-weighted second-order structure function;
* `ClayNS.strFlux Φ u t h j = ∫_cell Φ(x) δ_h u_j |δ_h u|² dx` — the
  cutoff-weighted third-order structure flux.

and it differentiates them in the *separation* variable `h`.  All separation
derivatives are taken along coordinate rays `h ↦ h + s·e_j`, which is enough for
the gradient and the Laplacian in `h`, and which lets the differentiation under
the integral sign of `hasDerivAt_cellInt` be reused verbatim: the ray parameter
is fed into the (unused) time slot of a spacetime field.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.IncrementEnergyPeriodic

open scoped BigOperators

noncomputable section

namespace ClayNS

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## Affine reparametrisations of spacetime, and the chain rule for `dvec` -/

/-- The chain rule for `dvec` along an affine reparametrisation of spacetime. -/
lemma dvec_comp_affine (V : STime → F) (hV : Differentiable ℝ V) (A : STime →L[ℝ] STime)
    (c : STime) (a z : STime) :
    dvec a (fun w => V (c + A w)) z = dvec (A a) V (c + A z) := by
  have hA : HasFDerivAt (fun w : STime => c + A w) A z := by
    simpa using (A.hasFDerivAt (x := z)).const_add c
  have hcomp : HasFDerivAt (fun w => V (c + A w))
      ((fderiv ℝ V (c + A z)).comp A) z := (hV (c + A z)).hasFDerivAt.comp z hA
  have := congrArg (fun L : STime →L[ℝ] F => L a) hcomp.fderiv
  simpa [dvec] using this

lemma contDiff_comp_affine (V : STime → F) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (A : STime →L[ℝ] STime)
    (c : STime) : ContDiff ℝ (⊤ : ℕ∞) (fun w => V (c + A w)) :=
  hV.comp (contDiff_const.add A.contDiff)

/-- The linear part of the coordinate ray `z ↦ (t, z.2 + h + z.1 • e_j)`: the
first (time) slot of the argument is used as the *separation* parameter. -/
def rayLin (j : Fin 3) : STime →L[ℝ] STime :=
  (ContinuousLinearMap.inr ℝ ℝ E3).comp
    ((ContinuousLinearMap.snd ℝ ℝ E3) + (ContinuousLinearMap.fst ℝ ℝ E3).smulRight (ee j))

@[simp] lemma rayLin_apply (j : Fin 3) (a : STime) :
    rayLin j a = ((0 : ℝ), a.2 + a.1 • ee j) := rfl

@[simp] lemma rayLin_time (j : Fin 3) : rayLin j (1, 0) = ((0 : ℝ), ee j) := by
  simp [rayLin]

@[simp] lemma rayLin_space (j i : Fin 3) : rayLin j ((0 : ℝ), ee i) = ((0 : ℝ), ee i) := by
  simp [rayLin]

/-- The point `(t, x + h + s·e_j)` of spacetime, as an affine function of the
pair `z = (s, x)`. -/
def rayPt (t : ℝ) (h : E3) (j : Fin 3) : STime → STime := fun z => (t, h) + rayLin j z

@[simp] lemma rayPt_apply (t : ℝ) (h : E3) (j : Fin 3) (z : STime) :
    rayPt t h j z = (t, z.2 + (h + z.1 • ee j)) := by
  simp [rayPt, Prod.ext_iff]
  abel

/-- The linear part of the time slice `z ↦ (t, z.2)`. -/
def sliceLin : STime →L[ℝ] STime :=
  (ContinuousLinearMap.inr ℝ ℝ E3).comp (ContinuousLinearMap.snd ℝ ℝ E3)

@[simp] lemma sliceLin_apply (a : STime) : sliceLin a = ((0 : ℝ), a.2) := rfl

/-- The point `(t, x)`, as an affine function of `z = (s, x)`. -/
def slicePt (t : ℝ) : STime → STime := fun z => (t, 0) + sliceLin z

@[simp] lemma slicePt_apply (t : ℝ) (z : STime) : slicePt t z = (t, z.2) := by
  simp [slicePt]

@[simp] lemma sliceLin_time : sliceLin ((1 : ℝ), (0 : E3)) = 0 := by
  simp [sliceLin, Prod.ext_iff]

/-- A `dvec` in the zero direction vanishes. -/
@[simp] lemma dvec_zero_dir (V : STime → F) (z : STime) : dvec (0 : STime) V z = 0 := by
  simp [dvec]

/-! ## The two-point fields, as functions of a separation ray parameter -/

/-- `δ_{h+s e_j} u_a` written as a function of `z = (s, x)`. -/
def rayIncrComp (V : STime → E3) (t : ℝ) (h : E3) (j a : Fin 3) : STime → ℝ :=
  fun z => V (rayPt t h j z) a - V (slicePt t z) a

lemma contDiff_rayIncrComp {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) (h : E3)
    (j a : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (rayIncrComp V t h j a) :=
  (contDiff_comp_affine (fun w => V w a) (contDiff_coord V hV a) (rayLin j) (t, h)).sub
    (contDiff_comp_affine (fun w => V w a) (contDiff_coord V hV a) sliceLin (t, 0))

/-- The separation derivative of the increment is the spatial derivative of the
velocity at the shifted point. -/
lemma dvec_time_rayIncrComp {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) (h : E3)
    (j a : Fin 3) (z : STime) :
    dvec (1, 0) (rayIncrComp V t h j a) z
      = dvec (0, ee j) (fun w => V w a) (rayPt t h j z) := by
  have hVa : Differentiable ℝ (fun w : STime => V w a) :=
    differentiable_of_contDiffTop (contDiff_coord V hV a)
  have h1 := dvec_comp_affine (fun w : STime => V w a) hVa (rayLin j) (t, h) (1, 0) z
  have h2 := dvec_comp_affine (fun w : STime => V w a) hVa sliceLin (t, 0) (1, 0) z
  have hsub : dvec (1, 0) (rayIncrComp V t h j a) z
      = dvec (1, 0) (fun w => V (rayPt t h j w) a) z
        - dvec (1, 0) (fun w => V (slicePt t w) a) z :=
    dvec_sub _ _ z
      (differentiable_of_contDiffTop
        (contDiff_comp_affine (fun w => V w a) (contDiff_coord V hV a) (rayLin j) (t, h)) z)
      (differentiable_of_contDiffTop
        (contDiff_comp_affine (fun w => V w a) (contDiff_coord V hV a) sliceLin (t, 0)) z) (1, 0)
  rw [hsub]
  rw [show (fun w : STime => V (rayPt t h j w) a) = fun w => (fun u : STime => V u a)
      ((t, h) + rayLin j w) from rfl,
    show (fun w : STime => V (slicePt t w) a) = fun w => (fun u : STime => V u a)
      ((t, 0) + sliceLin w) from rfl, h1, h2]
  simp only [rayPt, dvec, rayLin_time, sliceLin_time, map_zero, sub_zero]

/-- The increment vanishes at zero separation. -/
@[simp] lemma rayIncrComp_zero (V : STime → E3) (t : ℝ) (j a : Fin 3) (x : E3) :
    rayIncrComp V t 0 j a (0, x) = 0 := by
  simp [rayIncrComp]

/-! ## Calculus helpers -/

/-- A field that does not see the ray parameter has vanishing ray derivative. -/
lemma dvec_time_comp_slice (f : STime → ℝ) (hf : Differentiable ℝ f) (t : ℝ) (z : STime) :
    dvec (1, 0) (fun w => f (slicePt t w)) z = 0 := by
  rw [show (fun w : STime => f (slicePt t w)) = fun w => f ((t, 0) + sliceLin w) from rfl,
    dvec_comp_affine f hf sliceLin (t, 0) (1, 0) z]
  rw [sliceLin_time]
  exact dvec_zero_dir f _

/-- The derivative of a sum of squares. -/
lemma dvec_sumSq (W : Fin 3 → STime → ℝ) (hW : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (W a))
    (c z : STime) :
    dvec c (fun w => ∑ a, W a w * W a w) z = 2 * ∑ a, W a z * dvec c (W a) z := by
  rw [dvec_sum Finset.univ (fun (a : Fin 3) (w : STime) => W a w * W a w) z
    (fun a _ => (differentiable_of_contDiffTop ((hW a).mul (hW a))) z) c]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dvec_mul (W a) (W a) z ((differentiable_of_contDiffTop (hW a)) z)
    ((differentiable_of_contDiffTop (hW a)) z) c]
  ring

/-- The ray derivative of a field evaluated at the shifted point. -/
lemma dvec_time_comp_ray (f : STime → ℝ) (hf : Differentiable ℝ f) (t : ℝ) (h : E3) (j : Fin 3)
    (z : STime) :
    dvec (1, 0) (fun w => f (rayPt t h j w)) z = dvec (0, ee j) f (rayPt t h j z) := by
  rw [show (fun w : STime => f (rayPt t h j w)) = fun w => f ((t, h) + rayLin j w) from rfl,
    dvec_comp_affine f hf (rayLin j) (t, h) (1, 0) z]
  simp [rayPt]

/-! ## The structure function and the structure flux -/

/-- **The cutoff-weighted second-order structure function**
`S₂(h,t) = ∫_cell Φ(x)|u(t,x+h) − u(t,x)|² dx`. -/
def strFun (Phi : STime → ℝ) (V : STime → E3) (t : ℝ) (h : E3) : ℝ :=
  cellInt fun x => Phi (t, x) * ∑ a, (V (t, x + h) a - V (t, x) a) * (V (t, x + h) a - V (t, x) a)

/-- **The cutoff-weighted third-order structure flux**, component `m`:
`F₃(h,t)_m = ∫_cell Φ(x) δ_h u_m |δ_h u|² dx`. -/
def strFlux (Phi : STime → ℝ) (V : STime → E3) (t : ℝ) (h : E3) (m : Fin 3) : ℝ :=
  cellInt fun x => Phi (t, x) * ((V (t, x + h) m - V (t, x) m)
    * ∑ a, (V (t, x + h) a - V (t, x) a) * (V (t, x + h) a - V (t, x) a))

/-- The integrand of `strFun` along the separation ray `h + s·e_j`. -/
def strDens (Phi : STime → ℝ) (V : STime → E3) (t : ℝ) (h : E3) (j : Fin 3) : STime → ℝ :=
  fun z => Phi (slicePt t z) * ∑ a, rayIncrComp V t h j a z * rayIncrComp V t h j a z

/-- The integrand of `strFlux` along the separation ray `h + s·e_j`. -/
def strFluxDens (Phi : STime → ℝ) (V : STime → E3) (t : ℝ) (h : E3) (j m : Fin 3) : STime → ℝ :=
  fun z => Phi (slicePt t z) * (rayIncrComp V t h j m z
    * ∑ a, rayIncrComp V t h j a z * rayIncrComp V t h j a z)

lemma strFun_ray (Phi : STime → ℝ) (V : STime → E3) (t : ℝ) (h : E3) (j : Fin 3) (s : ℝ) :
    strFun Phi V t (h + s • ee j) = cellInt fun x => strDens Phi V t h j (s, x) :=
  cellInt_congr fun x => by simp [strDens, rayIncrComp]

lemma strFlux_ray (Phi : STime → ℝ) (V : STime → E3) (t : ℝ) (h : E3) (j m : Fin 3) (s : ℝ) :
    strFlux Phi V t (h + s • ee j) m = cellInt fun x => strFluxDens Phi V t h j m (s, x) :=
  cellInt_congr fun x => by simp [strFluxDens, rayIncrComp]

/-! ## Elementary properties -/

lemma contDiff_slicePhi {Phi : STime → ℝ} (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : STime => Phi (slicePt t z)) :=
  contDiff_comp_affine Phi hPhi sliceLin (t, 0)

lemma contDiff_strDens {Phi : STime → ℝ} {V : STime → E3} (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) (h : E3) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (strDens Phi V t h j) :=
  (contDiff_slicePhi hPhi t).mul
    (ContDiff.sum fun a _ => (contDiff_rayIncrComp hV t h j a).mul (contDiff_rayIncrComp hV t h j a))

lemma contDiff_strFluxDens {Phi : STime → ℝ} {V : STime → E3} (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) (h : E3) (j m : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (strFluxDens Phi V t h j m) :=
  (contDiff_slicePhi hPhi t).mul ((contDiff_rayIncrComp hV t h j m).mul
    (ContDiff.sum fun a _ =>
      (contDiff_rayIncrComp hV t h j a).mul (contDiff_rayIncrComp hV t h j a)))

/-- The structure function is nonnegative for a nonnegative cutoff. -/
theorem strFun_nonneg {Phi : STime → ℝ} (V : STime → E3) (t : ℝ) (h : E3)
    (hPhi : ∀ x : E3, 0 ≤ Phi (t, x)) : 0 ≤ strFun Phi V t h :=
  cellInt_nonneg fun x => mul_nonneg (hPhi x)
    (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)

/-- The structure function vanishes at zero separation: `S₂(0,t) = 0`. -/
@[simp] theorem strFun_zero (Phi : STime → ℝ) (V : STime → E3) (t : ℝ) :
    strFun Phi V t 0 = 0 := by
  have : (fun x : E3 => Phi (t, x)
      * ∑ a, (V (t, x + 0) a - V (t, x) a) * (V (t, x + 0) a - V (t, x) a))
      = fun _ : E3 => (0 : ℝ) := by
    funext x; simp
  rw [strFun, this]
  simp [cellInt]

/-- The structure flux vanishes at zero separation. -/
@[simp] theorem strFlux_zero (Phi : STime → ℝ) (V : STime → E3) (t : ℝ) (m : Fin 3) :
    strFlux Phi V t 0 m = 0 := by
  have : (fun x : E3 => Phi (t, x) * ((V (t, x + 0) m - V (t, x) m)
      * ∑ a, (V (t, x + 0) a - V (t, x) a) * (V (t, x + 0) a - V (t, x) a)))
      = fun _ : E3 => (0 : ℝ) := by
    funext x; simp
  rw [strFlux, this]
  simp [cellInt]

/-- Pointwise linearization of the cubic weight. -/
lemma abs_weighted_cube_le {p w S B : ℝ} (hp : 0 ≤ p) (hS : 0 ≤ S) (hw : |w| ≤ B) :
    |p * (w * S)| ≤ B * (p * S) := by
  have h1 : |p * (w * S)| = p * (|w| * S) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hS]
  have h2 : |w| * S ≤ B * S := mul_le_mul_of_nonneg_right hw hS
  have h3 : p * (|w| * S) ≤ p * (B * S) := mul_le_mul_of_nonneg_left h2 hp
  have h4 : p * (B * S) = B * (p * S) := by ring
  rw [h1]
  linarith

/-- **Linearization of the third-order flux.**  If the increment component `m`
is bounded by `B` on the cell, then `|F₃(h,t)_m| ≤ B·S₂(h,t)`: after a sup-norm
normalization the cubic structure flux is linear in the second-order structure
function. -/
theorem abs_strFlux_le {Phi : STime → ℝ} {V : STime → E3} (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) (h : E3) (m : Fin 3) {B : ℝ}
    (hPhinn : ∀ x : E3, 0 ≤ Phi (t, x))
    (hB : ∀ x : E3, |V (t, x + h) m - V (t, x) m| ≤ B) :
    |strFlux Phi V t h m| ≤ B * strFun Phi V t h := by
  have hcontPhi : Continuous fun x : E3 => Phi (t, x) :=
    hPhi.continuous.comp (continuous_const.prodMk continuous_id)
  have hcontD : ∀ a : Fin 3, Continuous fun x : E3 => V (t, x + h) a - V (t, x) a := by
    intro a
    exact ((contDiff_coord V hV a).continuous.comp
        (continuous_const.prodMk (continuous_id.add continuous_const))).sub
      ((contDiff_coord V hV a).continuous.comp (continuous_const.prodMk continuous_id))
  have hsq : Continuous fun x : E3 =>
      ∑ a, (V (t, x + h) a - V (t, x) a) * (V (t, x + h) a - V (t, x) a) :=
    continuous_finset_sum _ fun a _ => (hcontD a).mul (hcontD a)
  have hc1 : Continuous fun x : E3 => Phi (t, x) * ((V (t, x + h) m - V (t, x) m)
      * ∑ a, (V (t, x + h) a - V (t, x) a) * (V (t, x + h) a - V (t, x) a)) :=
    hcontPhi.mul ((hcontD m).mul hsq)
  have hc2 : Continuous fun x : E3 => B * (Phi (t, x)
      * ∑ a, (V (t, x + h) a - V (t, x) a) * (V (t, x + h) a - V (t, x) a)) :=
    continuous_const.mul (hcontPhi.mul hsq)
  have hkey : ∀ x : E3, |Phi (t, x) * ((V (t, x + h) m - V (t, x) m)
        * ∑ a, (V (t, x + h) a - V (t, x) a) * (V (t, x + h) a - V (t, x) a))|
      ≤ B * (Phi (t, x) * ∑ a, (V (t, x + h) a - V (t, x) a)
        * (V (t, x + h) a - V (t, x) a)) := fun x =>
    abs_weighted_cube_le (hPhinn x) (Finset.sum_nonneg fun a _ => mul_self_nonneg _) (hB x)
  have hupper : cellInt (fun x : E3 => B * (Phi (t, x)
      * ∑ a, (V (t, x + h) a - V (t, x) a) * (V (t, x + h) a - V (t, x) a)))
      = B * strFun Phi V t h := cellInt_const_mul _ _
  have hup : strFlux Phi V t h m ≤ B * strFun Phi V t h := by
    have := cellInt_mono hc1 hc2 fun x => (abs_le.mp (hkey x)).2
    rwa [hupper] at this
  have hdown : - (B * strFun Phi V t h) ≤ strFlux Phi V t h m := by
    have hmono := cellInt_mono hc2.neg hc1 fun x => (abs_le.mp (hkey x)).1
    have hneg : cellInt (fun x : E3 => - (B * (Phi (t, x)
        * ∑ a, (V (t, x + h) a - V (t, x) a) * (V (t, x + h) a - V (t, x) a))))
        = - (B * strFun Phi V t h) := by
      rw [cellInt_neg, hupper]
    rwa [hneg] at hmono
  exact abs_le.mpr ⟨hdown, hup⟩

/-! ## Separation derivatives along a coordinate ray -/

/-- The integrand of the first separation derivative of `strFun`. -/
def strDensD (Phi : STime → ℝ) (V : STime → E3) (t : ℝ) (h : E3) (j : Fin 3) : STime → ℝ :=
  fun z => 2 * (Phi (slicePt t z)
    * ∑ a, rayIncrComp V t h j a z * dvec (0, ee j) (fun w => V w a) (rayPt t h j z))

/-- The integrand of the second separation derivative of `strFun`. -/
def strDensD2 (Phi : STime → ℝ) (V : STime → E3) (t : ℝ) (h : E3) (j : Fin 3) : STime → ℝ :=
  fun z => 2 * (Phi (slicePt t z) * ∑ a,
    (dvec (0, ee j) (fun w => V w a) (rayPt t h j z)
        * dvec (0, ee j) (fun w => V w a) (rayPt t h j z)
      + rayIncrComp V t h j a z
        * dvec (0, ee j) (dvec (0, ee j) (fun w => V w a)) (rayPt t h j z)))

/-- The integrand of the first separation derivative of `strFlux`. -/
def strFluxDensD (Phi : STime → ℝ) (V : STime → E3) (t : ℝ) (h : E3) (j m : Fin 3) :
    STime → ℝ :=
  fun z => Phi (slicePt t z) * (dvec (0, ee j) (fun w => V w m) (rayPt t h j z)
      * ∑ a, rayIncrComp V t h j a z * rayIncrComp V t h j a z
    + rayIncrComp V t h j m z
      * (2 * ∑ a, rayIncrComp V t h j a z * dvec (0, ee j) (fun w => V w a) (rayPt t h j z)))

/-- Constants pull out of `dvec`. -/
lemma dvec_const_mul (c : ℝ) (g : STime → ℝ) (z : STime) (hg : DifferentiableAt ℝ g z)
    (a : STime) : dvec a (fun w => c * g w) z = c * dvec a g z := by
  rw [dvec_mul (fun _ => c) g z (differentiableAt_const c) hg a]
  simp [dvec]

lemma contDiff_rayGrad {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) (h : E3)
    (j a : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : STime => dvec (0, ee j) (fun w => V w a) (rayPt t h j z)) :=
  contDiff_comp_affine _ (contDiff_dvec _ (contDiff_coord V hV a) (0, ee j)) (rayLin j) (t, h)

lemma contDiff_strDensD {Phi : STime → ℝ} {V : STime → E3} (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) (h : E3) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (strDensD Phi V t h j) :=
  contDiff_const.mul ((contDiff_slicePhi hPhi t).mul
    (ContDiff.sum fun a _ => (contDiff_rayIncrComp hV t h j a).mul (contDiff_rayGrad hV t h j a)))

/-- The first separation derivative of the structure-function density. -/
lemma dvec_time_strDens {Phi : STime → ℝ} {V : STime → E3} (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) (h : E3) (j : Fin 3) (z : STime) :
    dvec (1, 0) (strDens Phi V t h j) z = strDensD Phi V t h j z := by
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun z : STime => Phi (slicePt t z)) := contDiff_slicePhi hPhi t
  have hW : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (rayIncrComp V t h j a) :=
    fun a => contDiff_rayIncrComp hV t h j a
  have hB : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : STime => ∑ a, rayIncrComp V t h j a z * rayIncrComp V t h j a z) :=
    ContDiff.sum fun a _ => (hW a).mul (hW a)
  have hprod := dvec_mul (fun z : STime => Phi (slicePt t z))
    (fun z : STime => ∑ a, rayIncrComp V t h j a z * rayIncrComp V t h j a z) z
    (differentiable_of_contDiffTop hA z) (differentiable_of_contDiffTop hB z) (1, 0)
  have hstr : strDens Phi V t h j = fun z : STime => Phi (slicePt t z)
      * ∑ a, rayIncrComp V t h j a z * rayIncrComp V t h j a z := rfl
  rw [hstr, hprod, dvec_time_comp_slice Phi (differentiable_of_contDiffTop hPhi) t z,
    dvec_sumSq (rayIncrComp V t h j) hW (1, 0) z]
  simp only [strDensD, dvec_time_rayIncrComp hV t h j]
  ring

/-- The second separation derivative of the structure-function density. -/
lemma dvec_time_strDensD {Phi : STime → ℝ} {V : STime → E3} (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) (h : E3) (j : Fin 3) (z : STime) :
    dvec (1, 0) (strDensD Phi V t h j) z = strDensD2 Phi V t h j z := by
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun z : STime => Phi (slicePt t z)) := contDiff_slicePhi hPhi t
  have hW : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (rayIncrComp V t h j a) :=
    fun a => contDiff_rayIncrComp hV t h j a
  have hG : ∀ a, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : STime => dvec (0, ee j) (fun w => V w a) (rayPt t h j z)) :=
    fun a => contDiff_rayGrad hV t h j a
  have hC : ContDiff ℝ (⊤ : ℕ∞) (fun z : STime =>
      ∑ a, rayIncrComp V t h j a z * dvec (0, ee j) (fun w => V w a) (rayPt t h j z)) :=
    ContDiff.sum fun a _ => (hW a).mul (hG a)
  have hstr : strDensD Phi V t h j = fun z : STime => 2 * (Phi (slicePt t z)
      * ∑ a, rayIncrComp V t h j a z * dvec (0, ee j) (fun w => V w a) (rayPt t h j z)) := rfl
  have hcmul := dvec_const_mul (2 : ℝ) (fun z : STime => Phi (slicePt t z)
      * ∑ a, rayIncrComp V t h j a z * dvec (0, ee j) (fun w => V w a) (rayPt t h j z)) z
    (differentiable_of_contDiffTop (hA.mul hC) z) (1, 0)
  have hprod := dvec_mul (fun z : STime => Phi (slicePt t z))
    (fun z : STime => ∑ a, rayIncrComp V t h j a z
      * dvec (0, ee j) (fun w => V w a) (rayPt t h j z)) z
    (differentiable_of_contDiffTop hA z) (differentiable_of_contDiffTop hC z) (1, 0)
  have hsum : dvec (1, 0) (fun z : STime => ∑ a, rayIncrComp V t h j a z
        * dvec (0, ee j) (fun w => V w a) (rayPt t h j z)) z
      = ∑ a, (dvec (0, ee j) (fun w => V w a) (rayPt t h j z)
            * dvec (0, ee j) (fun w => V w a) (rayPt t h j z)
          + rayIncrComp V t h j a z
            * dvec (0, ee j) (dvec (0, ee j) (fun w => V w a)) (rayPt t h j z)) := by
    rw [dvec_sum Finset.univ (fun (a : Fin 3) (w : STime) => rayIncrComp V t h j a w
      * dvec (0, ee j) (fun u => V u a) (rayPt t h j w)) z
      (fun a _ => (differentiable_of_contDiffTop ((hW a).mul (hG a))) z) (1, 0)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [dvec_mul (rayIncrComp V t h j a)
      (fun z : STime => dvec (0, ee j) (fun w => V w a) (rayPt t h j z)) z
      (differentiable_of_contDiffTop (hW a) z) (differentiable_of_contDiffTop (hG a) z) (1, 0),
      dvec_time_rayIncrComp hV t h j a z,
      dvec_time_comp_ray (dvec (0, ee j) (fun w => V w a))
        (differentiable_of_contDiffTop (contDiff_dvec _ (contDiff_coord V hV a) (0, ee j)))
        t h j z]
  have hslice := dvec_time_comp_slice Phi (differentiable_of_contDiffTop hPhi) t z
  rw [hstr, hcmul, hprod, hslice, hsum]
  simp only [strDensD2]
  ring

/-- The first separation derivative of the structure-flux density. -/
lemma dvec_time_strFluxDens {Phi : STime → ℝ} {V : STime → E3} (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) (h : E3) (j m : Fin 3) (z : STime) :
    dvec (1, 0) (strFluxDens Phi V t h j m) z = strFluxDensD Phi V t h j m z := by
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun z : STime => Phi (slicePt t z)) := contDiff_slicePhi hPhi t
  have hW : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (rayIncrComp V t h j a) :=
    fun a => contDiff_rayIncrComp hV t h j a
  have hQ : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : STime => ∑ a, rayIncrComp V t h j a z * rayIncrComp V t h j a z) :=
    ContDiff.sum fun a _ => (hW a).mul (hW a)
  have hstr : strFluxDens Phi V t h j m = fun z : STime => Phi (slicePt t z)
      * (rayIncrComp V t h j m z
        * ∑ a, rayIncrComp V t h j a z * rayIncrComp V t h j a z) := rfl
  have hprod := dvec_mul (fun z : STime => Phi (slicePt t z))
    (fun z : STime => rayIncrComp V t h j m z
      * ∑ a, rayIncrComp V t h j a z * rayIncrComp V t h j a z) z
    (differentiable_of_contDiffTop hA z)
    (differentiable_of_contDiffTop ((hW m).mul hQ) z) (1, 0)
  have hinner := dvec_mul (rayIncrComp V t h j m)
    (fun z : STime => ∑ a, rayIncrComp V t h j a z * rayIncrComp V t h j a z) z
    (differentiable_of_contDiffTop (hW m) z) (differentiable_of_contDiffTop hQ z) (1, 0)
  rw [hstr, hprod, dvec_time_comp_slice Phi (differentiable_of_contDiffTop hPhi) t z, hinner,
    dvec_sumSq (rayIncrComp V t h j) hW (1, 0) z, dvec_time_rayIncrComp hV t h j m z]
  simp only [strFluxDensD, dvec_time_rayIncrComp hV t h j]
  ring

/-! ## Differentiating the integrals -/

/-- **The first separation derivative of the structure function.** -/
theorem hasDerivAt_strFun_ray {Phi : STime → ℝ} {V : STime → E3} (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) (h : E3) (j : Fin 3) (s : ℝ) :
    HasDerivAt (fun r : ℝ => strFun Phi V t (h + r • ee j))
      (cellInt fun x => strDensD Phi V t h j (s, x)) s := by
  have hfun : (fun r : ℝ => strFun Phi V t (h + r • ee j))
      = fun r : ℝ => cellInt fun x => strDens Phi V t h j (r, x) :=
    funext fun r => strFun_ray Phi V t h j r
  have hbase := hasDerivAt_cellInt (strDens Phi V t h j) (contDiff_strDens hPhi hV t h j) s
  have heq : (cellInt fun x => dvec (1, 0) (strDens Phi V t h j) (s, x))
      = cellInt fun x => strDensD Phi V t h j (s, x) :=
    cellInt_congr fun x => dvec_time_strDens hPhi hV t h j (s, x)
  rw [hfun, ← heq]
  exact hbase

/-- **The second separation derivative of the structure function.** -/
theorem hasDerivAt_strFunD_ray {Phi : STime → ℝ} {V : STime → E3} (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) (h : E3) (j : Fin 3) (s : ℝ) :
    HasDerivAt (fun r : ℝ => cellInt fun x => strDensD Phi V t h j (r, x))
      (cellInt fun x => strDensD2 Phi V t h j (s, x)) s := by
  have hbase := hasDerivAt_cellInt (strDensD Phi V t h j) (contDiff_strDensD hPhi hV t h j) s
  have heq : (cellInt fun x => dvec (1, 0) (strDensD Phi V t h j) (s, x))
      = cellInt fun x => strDensD2 Phi V t h j (s, x) :=
    cellInt_congr fun x => dvec_time_strDensD hPhi hV t h j (s, x)
  rw [← heq]
  exact hbase

/-- **The first separation derivative of the structure flux.** -/
theorem hasDerivAt_strFlux_ray {Phi : STime → ℝ} {V : STime → E3} (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) (h : E3) (j m : Fin 3) (s : ℝ) :
    HasDerivAt (fun r : ℝ => strFlux Phi V t (h + r • ee j) m)
      (cellInt fun x => strFluxDensD Phi V t h j m (s, x)) s := by
  have hfun : (fun r : ℝ => strFlux Phi V t (h + r • ee j) m)
      = fun r : ℝ => cellInt fun x => strFluxDens Phi V t h j m (r, x) :=
    funext fun r => strFlux_ray Phi V t h j m r
  have hbase := hasDerivAt_cellInt (strFluxDens Phi V t h j m)
    (contDiff_strFluxDens hPhi hV t h j m) s
  have heq : (cellInt fun x => dvec (1, 0) (strFluxDens Phi V t h j m) (s, x))
      = cellInt fun x => strFluxDensD Phi V t h j m (s, x) :=
    cellInt_congr fun x => dvec_time_strFluxDens hPhi hV t h j m (s, x)
  rw [hfun, ← heq]
  exact hbase

/-! ## Zero separation: the gradient, the flux divergence and the Laplacian -/

@[simp] lemma rayPt_zero (t : ℝ) (j : Fin 3) (x : E3) : rayPt t 0 j (0, x) = (t, x) := by
  simp

/-- The weighted squared `j`-th directional derivative of the velocity. -/
def dirGradSq (Phi : STime → ℝ) (V : STime → E3) (t : ℝ) (j : Fin 3) : ℝ :=
  cellInt fun x => Phi (t, x) * ∑ a, dvec (0, ee j) (fun w => V w a) (t, x)
    * dvec (0, ee j) (fun w => V w a) (t, x)

/-- The weighted squared velocity gradient `∫_cell Φ|∇u|²`. -/
def weightedGradSq (Phi : STime → ℝ) (V : STime → E3) (t : ℝ) : ℝ :=
  cellInt fun x => Phi (t, x) * ∑ j, ∑ a, dvec (0, ee j) (fun w => V w a) (t, x)
    * dvec (0, ee j) (fun w => V w a) (t, x)

@[simp] lemma strDensD_zero (Phi : STime → ℝ) (V : STime → E3) (t : ℝ) (j : Fin 3) (x : E3) :
    strDensD Phi V t 0 j (0, x) = 0 := by
  simp [strDensD]

@[simp] lemma strFluxDensD_zero (Phi : STime → ℝ) (V : STime → E3) (t : ℝ) (j m : Fin 3)
    (x : E3) : strFluxDensD Phi V t 0 j m (0, x) = 0 := by
  simp [strFluxDensD]

lemma strDensD2_zero (Phi : STime → ℝ) (V : STime → E3) (t : ℝ) (j : Fin 3) (x : E3) :
    strDensD2 Phi V t 0 j (0, x)
      = 2 * (Phi (t, x) * ∑ a, dvec (0, ee j) (fun w => V w a) (t, x)
          * dvec (0, ee j) (fun w => V w a) (t, x)) := by
  simp [strDensD2]

/-- **The separation gradient of `S₂` vanishes at zero separation.** -/
theorem hasDerivAt_strFun_ray_at_zero {Phi : STime → ℝ} {V : STime → E3}
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) (j : Fin 3) :
    HasDerivAt (fun r : ℝ => strFun Phi V t (r • ee j)) 0 0 := by
  have hbase := hasDerivAt_strFun_ray hPhi hV t 0 j 0
  have hzero : (cellInt fun x => strDensD Phi V t 0 j (0, x)) = 0 := by
    rw [cellInt_congr (fun x => strDensD_zero Phi V t j x)]
    simp [cellInt]
  rw [hzero] at hbase
  simpa using hbase

/-- **The separation divergence of `F₃` vanishes at zero separation**: the
third-order flux is cubic in the increment. -/
theorem hasDerivAt_strFlux_ray_at_zero {Phi : STime → ℝ} {V : STime → E3}
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) (j m : Fin 3) :
    HasDerivAt (fun r : ℝ => strFlux Phi V t (r • ee j) m) 0 0 := by
  have hbase := hasDerivAt_strFlux_ray hPhi hV t 0 j m 0
  have hzero : (cellInt fun x => strFluxDensD Phi V t 0 j m (0, x)) = 0 := by
    rw [cellInt_congr (fun x => strFluxDensD_zero Phi V t j m x)]
    simp [cellInt]
  rw [hzero] at hbase
  simpa using hbase

/-- **The second separation derivative of `S₂` at zero separation** is twice the
weighted squared directional derivative of the velocity. -/
theorem hasDerivAt_strFunD_ray_at_zero {Phi : STime → ℝ} {V : STime → E3}
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) (j : Fin 3) :
    HasDerivAt (fun r : ℝ => cellInt fun x => strDensD Phi V t 0 j (r, x))
      (2 * dirGradSq Phi V t j) 0 := by
  have hbase := hasDerivAt_strFunD_ray hPhi hV t 0 j 0
  have hval : (cellInt fun x => strDensD2 Phi V t 0 j (0, x)) = 2 * dirGradSq Phi V t j := by
    rw [cellInt_congr (fun x => strDensD2_zero Phi V t j x)]
    exact cellInt_const_mul _ _
  rwa [hval] at hbase

lemma continuous_dirGradSq_integrand {Phi : STime → ℝ} {V : STime → E3}
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) (j : Fin 3) :
    Continuous fun x : E3 => Phi (t, x) * ∑ a, dvec (0, ee j) (fun w => V w a) (t, x)
      * dvec (0, ee j) (fun w => V w a) (t, x) := by
  have hslice : Continuous fun x : E3 => (t, x) := continuous_const.prodMk continuous_id
  refine (hPhi.continuous.comp hslice).mul (continuous_finset_sum _ fun a _ => ?_)
  have hd : Continuous fun x : E3 => dvec (0, ee j) (fun w => V w a) (t, x) :=
    (contDiff_dvec _ (contDiff_coord V hV a) (0, ee j)).continuous.comp hslice
  exact hd.mul hd

/-- The three directional pieces add up to the full weighted gradient energy. -/
theorem sum_dirGradSq {Phi : STime → ℝ} {V : STime → E3} (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) :
    ∑ j, dirGradSq Phi V t j = weightedGradSq Phi V t := by
  set f : Fin 3 → E3 → ℝ := fun j x => Phi (t, x) * ∑ a, dvec (0, ee j) (fun w => V w a) (t, x)
    * dvec (0, ee j) (fun w => V w a) (t, x) with hf
  have hc : ∀ j, Continuous (f j) := fun j => continuous_dirGradSq_integrand hPhi hV t j
  have hsplit : weightedGradSq Phi V t = cellInt (fun x => f 0 x + (f 1 x + f 2 x)) :=
    cellInt_congr fun x => by simp only [hf, Fin.sum_univ_three]; ring
  have e1 : cellInt (fun x => f 1 x + f 2 x) = cellInt (f 1) + cellInt (f 2) :=
    cellInt_add (hc 1) (hc 2)
  have e0 : cellInt (fun x => f 0 x + (f 1 x + f 2 x))
      = cellInt (f 0) + cellInt (fun x => f 1 x + f 2 x) :=
    cellInt_add (hc 0) ((hc 1).add (hc 2))
  have hdir : ∀ j, dirGradSq Phi V t j = cellInt (f j) := fun j => rfl
  rw [hsplit, e0, e1, Fin.sum_univ_three, hdir 0, hdir 1, hdir 2, add_assoc]

/-- **The separation Laplacian of `S₂` at zero separation equals `2∫Φ|∇u|²`.**
Together with `hasDerivAt_strFun_ray_at_zero` and
`hasDerivAt_strFlux_ray_at_zero` this is the whole content of the
Kármán–Howarth–Monin balance at `h = 0`. -/
theorem lapH_strFun_at_zero {Phi : STime → ℝ} {V : STime → E3} (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) :
    ∑ j, (2 * dirGradSq Phi V t j) = 2 * weightedGradSq Phi V t := by
  rw [← Finset.mul_sum, sum_dirGradSq hPhi hV t]

/-- **The Kármán–Howarth–Monin balance carries no information at zero
separation.**  At `h = 0` the time derivative of `S₂` vanishes (`S₂(0,t) = 0`
identically), the separation divergence of the third-order flux vanishes (the
flux is cubic), and the viscous term `2ν Δ_h S₂(0)` is *exactly* cancelled by
the dissipation source `−4ν∫Φ|∇u|²`.  So the two sides of

`∂_t S₂ + ∇_h·F₃ = 2ν Δ_h S₂ − 2ν(∫Φ|∇u(·+h)|² + ∫Φ|∇u|²)`

reduce to `0 = 0` there: an interior-minimum ("strong minimum principle")
argument applied at `h = 0` cannot extract any rigidity. -/
theorem khm_balance_at_zero_separation {Phi : STime → ℝ} {V : STime → E3}
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (nu t : ℝ) :
    (0 : ℝ) + ∑ _j : Fin 3, (0 : ℝ)
      = 2 * nu * (∑ j, (2 * dirGradSq Phi V t j))
        - 2 * nu * (weightedGradSq Phi V t + weightedGradSq Phi V t) := by
  rw [lapH_strFun_at_zero hPhi hV t]
  simp
  ring

end ClayNS
