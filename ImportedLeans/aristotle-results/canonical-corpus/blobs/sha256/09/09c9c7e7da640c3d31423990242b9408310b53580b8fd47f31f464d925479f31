/-
# `R₀A` is the derivative of the contour holonomy

`CMP98Eq119Transport` *defines* Bałaban's transported one-form by the recursion

    R₀A (s :: F) = A s + Ad (U s) (R₀A F),      R₀A [] = 0 ,

and the rest of the Eq. (119) lane consumes it under that name.  This file
proves that the name is earned: `R₀A` is exactly the right-trivialised
derivative of the contour holonomy along the physical perturbation of the link
field,

    U_t (x, s) = e^{t A(x,s)} · U(x, s) ,

namely

    d/dt  U_t(Γ) |_{t=0}  =  (R₀A Γ) · U(Γ) .

The proof is an induction on the contour word using the product rule and the
derivative of `exp` at the identity (a special case of `hasDerivAt_exp_dexp`
from `CMP98Eq119Dexp`); the inductive step is *literally* the recursion above,
with the adjoint transport arising from `U_s R' U_s^{-1} · U_s = U_s R'`.

Consequences proved here:

* `hasDerivAt_hol` — the general statement, for every signed contour word;
* `hasDerivAt_hol_physicalContour` — its specialisation to the `13⁴`
  constructed Eq. (119) averaging contours;
* `hasDerivAt_hol_coarseBond` — and to the canonical coarse bond.

So the `R₀A` legs appearing in `eq119Physical` are not a notational stand-in
for a derivative: they *are* the derivative.
-/
import RequestProject.YangMills.CMP98Eq119Dexp
import RequestProject.YangMills.CMP98Eq119Producer

namespace YangMills.CMP98Eq119

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A] [Nontrivial A]
  [CompleteSpace A]

/-! ## 1. The exponential as a unit, and its derivative at the identity -/

/-- `e^{z}` as a unit of the Banach algebra, with inverse `e^{-z}`. -/
noncomputable def expUnit (z : A) : Aˣ where
  val := NormedSpace.exp z
  inv := NormedSpace.exp (-z)
  val_inv := by
    letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
    rw [← NormedSpace.exp_add_of_commute (Commute.neg_right (Commute.refl z)),
      add_neg_cancel, NormedSpace.exp_zero]
  inv_val := by
    letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
    rw [← NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl z)),
      neg_add_cancel, NormedSpace.exp_zero]

omit [NormOneClass A] [Nontrivial A] in
@[simp] theorem expUnit_val (z : A) : ((expUnit z : Aˣ) : A) = NormedSpace.exp z := rfl

omit [NormOneClass A] [Nontrivial A] in
@[simp] theorem expUnit_zero : expUnit (0 : A) = 1 := by
  ext
  simp

omit [NormOneClass A] [Nontrivial A] [CompleteSpace A] in
@[simp] theorem adOp_zero' : adOp (0 : A) = 0 := by
  ext z
  simp

/-- The derivative of `t ↦ e^{tZ}` at `t = 0` is `Z`.  This is the `Y = 0` case
of `hasDerivAt_exp_dexp`, i.e. of the noncommutative dexp formula. -/
theorem hasDerivAt_exp_smul (Z : A) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Z)) Z 0 := by
  have h := hasDerivAt_exp_dexp (0 : A) Z
  rw [dexpD_eq] at h
  simpa using h

/-! ## 2. The physical perturbation of the link field -/

variable {d L : ℕ}

/-- The perturbed link field `U_t (x,s) = e^{t A(x,s)} · U(x,s)`. -/
noncomputable def pertLink (link : PSite d L → Step d → Aˣ)
    (Afield : PSite d L → Step d → A) (t : ℝ) : PSite d L → Step d → Aˣ :=
  fun x s => expUnit (t • Afield x s) * link x s

omit [NormOneClass A] [Nontrivial A] in
@[simp] theorem pertLink_zero (link : PSite d L → Step d → Aˣ)
    (Afield : PSite d L → Step d → A) : pertLink link Afield 0 = link := by
  funext x s
  simp [pertLink]

omit [NormOneClass A] [Nontrivial A] [CompleteSpace A] in
theorem adjHom_mul_val (u : Aˣ) (z : A) : adjHom u z * (u : A) = (u : A) * z := by
  simp [adjHom_apply, mul_assoc]

/-! ## 3. `R₀A` is the derivative of the holonomy -/

/-- **Bałaban's `R₀A` is the right-trivialised derivative of the contour
holonomy.**  Perturbing every link by `U ↦ e^{tA} U` and differentiating the
holonomy of an arbitrary signed contour word at `t = 0` returns
`(R₀A Γ) · U(Γ)`. -/
theorem hasDerivAt_hol (link : PSite d L → Step d → Aˣ)
    (Afield : PSite d L → Step d → A) (x : PSite d L) (ss : List (Step d)) :
    HasDerivAt (fun t : ℝ => ((hol (pertLink link Afield t) x ss : Aˣ) : A))
      (rzero link adjHom Afield x ss * ((hol link x ss : Aˣ) : A)) 0 := by
  induction ss generalizing x with
  | nil => simpa using (hasDerivAt_const (0 : ℝ) (1 : A))
  | cons s ss ih =>
      have hfun : (fun t : ℝ => ((hol (pertLink link Afield t) x (s :: ss) : Aˣ) : A))
          = (fun t : ℝ => NormedSpace.exp (t • Afield x s) * ((link x s : Aˣ) : A))
            * (fun t : ℝ => ((hol (pertLink link Afield t) (move s x) ss : Aˣ) : A)) := by
        funext t
        simp [hol_cons, pertLink, Pi.mul_apply, mul_assoc]
      have hc : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Afield x s) * ((link x s : Aˣ) : A))
          (Afield x s * ((link x s : Aˣ) : A)) 0 :=
        (hasDerivAt_exp_smul (Afield x s)).mul_const _
      rw [hfun]
      convert hc.mul (ih (move s x)) using 1
      simp only [pertLink_zero, zero_smul, NormedSpace.exp_zero, one_mul]
      rw [rzero_cons, hol_cons, Units.val_mul, add_mul,
        ← mul_assoc (adjHom (link x s) (rzero link adjHom Afield (move s x) ss))
          ((link x s : Aˣ) : A), adjHom_mul_val]
      simp [mul_assoc]

/-! ## 4. The Eq. (119) contours -/

variable {N : ℕ}

/-- The `R₀A` leg that Eq. (119) attaches to a block point really is the
derivative of the holonomy of the *constructed* averaging contour at that
point. -/
theorem hasDerivAt_hol_physicalContour (link : PSite 4 N → Step 4 → Aˣ)
    (Afield : PSite 4 N → Step 4 → A) (cMinus : PSite 4 N) (μ : Fin 4) (o : Bool)
    (p : BlockOffset) :
    HasDerivAt
      (fun t : ℝ =>
        ((hol (pertLink link Afield t) cMinus (physicalContour μ o p) : Aˣ) : A))
      (rzero link adjHom Afield cMinus (physicalContour μ o p)
        * ((hol link cMinus (physicalContour μ o p) : Aˣ) : A)) 0 :=
  hasDerivAt_hol link Afield cMinus _

/-- The same for the canonical coarse bond. -/
theorem hasDerivAt_hol_coarseBond (link : PSite 4 N → Step 4 → Aˣ)
    (Afield : PSite 4 N → Step 4 → A) (cMinus : PSite 4 N) (μ : Fin 4) (o : Bool) :
    HasDerivAt
      (fun t : ℝ => ((hol (pertLink link Afield t) cMinus (coarseBond μ o) : Aˣ) : A))
      (rzero link adjHom Afield cMinus (coarseBond μ o)
        * ((hol link cMinus (coarseBond μ o) : Aˣ) : A)) 0 :=
  hasDerivAt_hol link Afield cMinus _

/-! ## 5. Axiom audit -/

#print axioms hasDerivAt_exp_smul
#print axioms hasDerivAt_hol
#print axioms hasDerivAt_hol_physicalContour

end YangMills.CMP98Eq119
