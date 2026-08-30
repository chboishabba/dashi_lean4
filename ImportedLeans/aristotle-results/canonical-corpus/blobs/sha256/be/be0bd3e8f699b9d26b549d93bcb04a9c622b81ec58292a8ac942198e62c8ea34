/-
# The literal right-exponential link jet, and the mixed third variation of a
# Wilson plaquette

`MixedThirdVariation` supplies the generic ordered recursion for a mixed third
variation.  This file instantiates it on the *physical* link family used in the
lattice construction: a background link multiplied on the right by three
one-parameter exponentials,

    U(s,t,u) = U₀ · exp(sX) · exp(tY) · exp(uZ).

Its jet is computed — not assumed — from the matrix-exponential derivative:

    v = U₀,  d₁ = U₀X,  d₂ = U₀Y,  d₃ = U₀Z,
    d₁₂ = U₀XY,  d₁₃ = U₀XZ,  d₂₃ = U₀YZ,  d₁₂₃ = U₀XYZ,

with the noncommutative order preserved throughout (`expLinkCarrier`).

Consequences:

* `hasMixedD3_expLink` : the link family's own mixed third variation is `U₀XYZ`.
* `hasMixedD3_plaquette_exp` : the mixed third variation of an ordered product
  of four such links — a Wilson plaquette — is the top component of the
  four-fold ordered Leibniz product of their jets.
* `hasMixedD3R_trace` : the mixed third variation passes through the trace.
* `hasMixedD3_wilsonPlaquetteAction` : hence the mixed third variation of the
  Wilson plaquette action `S = 1 − tr(P)/N` is `−tr((jetMul₄ …).d123)/N`.

This is `D³S`, the object `ConstraintCoordinateGaussian` calls `A'` — the
genuine operator variation entering `W = CᵀA'C`.  Nothing here fixes the
generators `X, Y, Z` or the background `U₀` of Bałaban's construction; what is
computed is the literal jet of the right-exponential family and its plaquette
recursion.

Everything is stated for real matrices, the setting in which the project's
lattice symbols live; for a complex group one takes the real part of the trace,
which does not affect the recursion.
-/
import RequestProject.YangMills.MixedThirdVariation

namespace YangMills

open Matrix NormedSpace
open scoped Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- A derivative in the normed matrix algebra is an entrywise derivative. -/
theorem hasMatDerivAt_of_hasDerivAt {f : ℝ → Matrix n n ℝ} {f' : Matrix n n ℝ} {t : ℝ}
    (h : HasDerivAt f f' t) : HasMatDerivAt f f' t := by
  intro i j
  set hlin : Matrix n n ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun A => A i j
      map_add' := by intros; simp
      map_smul' := by intros; simp } with hdef
  have hcomp := (LinearMap.toContinuousLinearMap hlin).hasFDerivAt.comp_hasDerivAt t h
  simpa [Function.comp, hdef] using hcomp

/-- **The right-exponential link derivative.** -/
theorem hasMatDerivAt_expLink (M X : Matrix n n ℝ) :
    HasMatDerivAt (fun s : ℝ => M * exp (s • X)) (M * X) 0 := by
  refine hasMatDerivAt_of_hasDerivAt ?_
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (𝔸 := Matrix n n ℝ) X 0
  simp only [zero_smul, exp_zero] at h
  simpa using h.const_mul M

namespace Jet3

/-- The jet of the right-exponential link family
`U₀ exp(sX) exp(tY) exp(uZ)`. -/
def expLinkJet (M X Y Z : Matrix n n ℝ) : Jet3 n where
  v := M
  d1 := M * X
  d2 := M * Y
  d3 := M * Z
  d12 := M * X * Y
  d13 := M * X * Z
  d23 := M * Y * Z
  d123 := M * X * Y * Z

end Jet3

/-- **The right-exponential link family is a jet carrier**, with the jet
computed from the matrix-exponential derivative. -/
noncomputable def expLinkCarrier (M X Y Z : Matrix n n ℝ) : JetCarrier n where
  F := fun s t u => M * exp (s • X) * exp (t • Y) * exp (u • Z)
  X0 := fun s t => M * exp (s • X) * exp (t • Y)
  X3 := fun s t => M * exp (s • X) * exp (t • Y) * Z
  a := fun s => M * exp (s • X)
  b := fun s => M * exp (s • X) * Y
  c := fun s => M * exp (s • X) * Z
  e := fun s => M * exp (s • X) * Y * Z
  jet := Jet3.expLinkJet M X Y Z
  hF0 := by intro s t; simp
  hFu := by
    intro s t
    have h := HasMatDerivAt.const_mul (M * exp (s • X) * exp (t • Y))
      (hasMatDerivAt_expLink (1 : Matrix n n ℝ) Z)
    simpa [Matrix.mul_assoc] using h
  hX0t0 := by intro s; simp
  hX0t := by
    intro s
    simpa using hasMatDerivAt_expLink (M * exp (s • X)) Y
  hX3t0 := by intro s; simp
  hX3t := by
    intro s
    simpa using (hasMatDerivAt_expLink (M * exp (s • X)) Y).mul_const Z
  ha0 := by simp [Jet3.expLinkJet]
  has := by simpa [Jet3.expLinkJet] using hasMatDerivAt_expLink M X
  hb0 := by simp [Jet3.expLinkJet]
  hbs := by simpa [Jet3.expLinkJet] using (hasMatDerivAt_expLink M X).mul_const Y
  hc0 := by simp [Jet3.expLinkJet]
  hcs := by simpa [Jet3.expLinkJet] using (hasMatDerivAt_expLink M X).mul_const Z
  he0 := by simp [Jet3.expLinkJet]
  hes := by
    simpa [Jet3.expLinkJet] using ((hasMatDerivAt_expLink M X).mul_const Y).mul_const Z

@[simp] theorem expLinkCarrier_jet (M X Y Z : Matrix n n ℝ) :
    (expLinkCarrier M X Y Z).jet = Jet3.expLinkJet M X Y Z := rfl

@[simp] theorem expLinkCarrier_F (M X Y Z : Matrix n n ℝ) :
    (expLinkCarrier M X Y Z).F = fun s t u => M * exp (s • X) * exp (t • Y) * exp (u • Z) :=
  rfl

/-- **The link family's own mixed third variation is `U₀XYZ`.** -/
theorem hasMixedD3_expLink (M X Y Z : Matrix n n ℝ) :
    HasMixedD3 (fun s t u => M * exp (s • X) * exp (t • Y) * exp (u • Z))
      (M * X * Y * Z) :=
  (expLinkCarrier M X Y Z).hasMixedD3

/-- **The mixed third variation of a Wilson plaquette.**  For an ordered product
of four right-exponential links it is the top component of the four-fold ordered
Leibniz product of their jets. -/
theorem hasMixedD3_plaquette_exp
    (M₁ X₁ Y₁ Z₁ M₂ X₂ Y₂ Z₂ M₃ X₃ Y₃ Z₃ M₄ X₄ Y₄ Z₄ : Matrix n n ℝ) :
    HasMixedD3
      (fun s t u =>
        (M₁ * exp (s • X₁) * exp (t • Y₁) * exp (u • Z₁))
        * (M₂ * exp (s • X₂) * exp (t • Y₂) * exp (u • Z₂))
        * (M₃ * exp (s • X₃) * exp (t • Y₃) * exp (u • Z₃))
        * (M₄ * exp (s • X₄) * exp (t • Y₄) * exp (u • Z₄)))
      (Jet3.jetMul (Jet3.jetMul (Jet3.jetMul
        (Jet3.expLinkJet M₁ X₁ Y₁ Z₁) (Jet3.expLinkJet M₂ X₂ Y₂ Z₂))
        (Jet3.expLinkJet M₃ X₃ Y₃ Z₃)) (Jet3.expLinkJet M₄ X₄ Y₄ Z₄)).d123 :=
  JetCarrier.mixedD3_plaquette (expLinkCarrier M₁ X₁ Y₁ Z₁) (expLinkCarrier M₂ X₂ Y₂ Z₂)
    (expLinkCarrier M₃ X₃ Y₃ Z₃) (expLinkCarrier M₄ X₄ Y₄ Z₄)

/-! ## Passing to the action -/

/-- The scalar mixed third derivative at the origin. -/
def HasMixedD3R (f : ℝ → ℝ → ℝ → ℝ) (w : ℝ) : Prop :=
  ∃ g : ℝ → ℝ → ℝ, (∀ s t, HasDerivAt (fun u => f s t u) (g s t) 0) ∧
    ∃ h : ℝ → ℝ, (∀ s, HasDerivAt (fun t => g s t) (h s) 0) ∧ HasDerivAt h w 0

omit [DecidableEq n] in
private theorem hasDerivAt_trace {F : ℝ → Matrix n n ℝ} {W : Matrix n n ℝ} {t : ℝ}
    (h : HasMatDerivAt F W t) :
    HasDerivAt (fun s => Matrix.trace (F s)) (Matrix.trace W) t := by
  have hsum : HasDerivAt (∑ i : n, fun s => F s i i) (∑ i : n, W i i) t :=
    HasDerivAt.sum (fun i _ => h i i)
  have hfun : (∑ i : n, fun s => F s i i) = fun s => Matrix.trace (F s) := by
    funext s; simp [Matrix.trace, Matrix.diag, Finset.sum_apply]
  rw [hfun] at hsum
  simpa [Matrix.trace, Matrix.diag] using hsum

omit [DecidableEq n] in
/-- **The mixed third variation passes through the trace.** -/
theorem hasMixedD3R_trace {F : ℝ → ℝ → ℝ → Matrix n n ℝ} {W : Matrix n n ℝ}
    (h : HasMixedD3 F W) :
    HasMixedD3R (fun s t u => Matrix.trace (F s t u)) (Matrix.trace W) := by
  obtain ⟨G, hG, H, hH, hW⟩ := h
  exact ⟨fun s t => Matrix.trace (G s t), fun s t => hasDerivAt_trace (hG s t),
    fun s => Matrix.trace (H s), fun s => hasDerivAt_trace (hH s), hasDerivAt_trace hW⟩

/-- The (real-matrix) Wilson plaquette action, `S = 1 − tr(P)/N`. -/
noncomputable def wilsonPlaquetteAction (N : ℝ) (P : Matrix n n ℝ) : ℝ := 1 - Matrix.trace P / N

omit [DecidableEq n] in
/-- **The mixed third variation of the Wilson plaquette action.** -/
theorem hasMixedD3_wilsonPlaquetteAction {F : ℝ → ℝ → ℝ → Matrix n n ℝ}
    {W : Matrix n n ℝ} (N : ℝ) (h : HasMixedD3 F W) :
    HasMixedD3R (fun s t u => wilsonPlaquetteAction N (F s t u))
      (-(Matrix.trace W / N)) := by
  obtain ⟨G, hG, H, hH, hW⟩ := h
  refine ⟨fun s t => -(Matrix.trace (G s t) / N), ?_,
    fun s => -(Matrix.trace (H s) / N), ?_, ?_⟩
  · intro s t
    have := ((hasDerivAt_trace (hG s t)).div_const N).const_sub (1 : ℝ)
    simpa [wilsonPlaquetteAction] using this
  · intro s
    have := ((hasDerivAt_trace (hH s)).div_const N).neg
    exact this
  · have := (hasDerivAt_trace hW).div_const N
    exact this.neg

end YangMills
