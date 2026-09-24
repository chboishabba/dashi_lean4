/-
# The similarity-variable energy identity and the projective scale speed

This file supplies the exact-calculus layer of the "scale expenditure" route.

Write the solution in similarity variables based at the candidate singular
point,

  `τ = −log(T−t)`, `y = (x−x_*)/√(T−t)`, `V(y,τ) = √(T−t)·u(x,t)`,

so that the equation becomes

  `∂_τ V = ν∆V − ½ y·∇V − ½ V − (V·∇)V − ∇P`,

and pair it in the Gaussian space `L²(ρ_ν)`, `ρ_ν(y) ∝ exp(−|y|²/(4ν))`, in
which the Ornstein–Uhlenbeck part `L₀ = ν∆ − ½y·∇` is symmetric with
`⟪f, L₀f⟫ = −ν‖∇f‖²`.

Everything below is stated at exactly the level of generality at which it is
*true by calculus*: a curve `V` in a real inner product space, a symmetric
continuous bilinear form `𝔞` playing the role of `ν⟪∇·,∇·⟫_ρ`, and the weak
form of the similarity equation.  No Navier–Stokes-specific hypothesis is used
here, and none is hidden: the physical content enters only when the abstract
statements are instantiated, and is confined to the two inputs named at the
bottom of this file.

## What is proved

* `ClayNS.projective_speed_sq` — the algebraic Gram identity
  `‖A^{-1/2}W − ⟪V,W⟫A^{-3/2}V‖² = (AB − C²)/A²`;
* `ClayNS.hasDerivAt_normalize` — that vector *is* the derivative of the
  normalized profile `V̂ = V/‖V‖`;
* `ClayNS.projective_gram_speed` — hence **(P)**: the squared speed of the
  normalized profile through similarity space equals the scale-Gram defect
  divided by `A²`;
* `ClayNS.gram_projective_speed_weighted` — the same identity in the weighted
  integral language of `GaussianScaleGram.lean`, where the scale-Gram defect
  `Δ = AB − C²` of the pair `(U, ΛU)` already lives;
* `ClayNS.similarity_energy_identity` — **(S)**: `ℋ′(τ) = −‖V_τ‖² − ⟪N,V_τ⟫`
  for `ℋ = ½𝔞(V,V) + ¼‖V‖²`;
* `ClayNS.transverse_quadratic_debt` — the completion of squares: cross terms
  are paid at quadratic cost `c²/λ`, never at cost `c`;
* `ClayNS.similarity_transverse_expenditure` — **the telescope**: absorbing the
  nonlinear/pressure pairing into `η‖V_τ‖²` plus a remainder turns (S) into a
  *finite* expenditure budget `(1−η)∫‖V_τ‖² ≤ ℋ(τ₀) − ℋ(τ₁) + ∫ℛ`;
* `ClayNS.scaleGram_payment_of_expenditure` and
  `ClayNS.scaleGram_payment_of_similarity_absorption` — the bridge that turns
  that budget into the hypothesis `hstar` of `ScaleGramChargeAssembly.lean`
  (`Ψ(b) − Ψ(a) ≤ C_*`), via the change of variable `τ = −log r`.

## What this changes

`hstar` was a global integral hypothesis about the scale-Gram defect.  After
this file it is a consequence of

1. the exact identity (S) — proved here;
2. a *pointwise* domination `Δ_scale(r)/𝒟(r) ≤ K·‖(V_τ)(−log r)‖²` — the
   statement that the scale-Gram defect at radius `r` is the projective speed
   at similarity time `−log r` (see `projective_gram_speed`);
3. the marginal/transverse absorption estimate `|⟪N+∇P, V_τ⟫| ≤ η‖V_τ‖² + ℛ`
   with `∫ℛ < ∞` — the one remaining physical input.

No `sorry`, no postulates, no axioms beyond the standard three.
-/
import RequestProject.NavierStokes.GaussianScaleGram
import RequestProject.NavierStokes.ScaleGramChargeAssembly

open MeasureTheory Set
open RealInnerProductSpace
open scoped BigOperators

noncomputable section

namespace ClayNS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## The projective Gram identity -/

/-- The scalar algebra behind `projective_speed_sq`. -/
private lemma proj_speed_alg {A B C : ℝ} (hA : 0 < A) :
    (Real.sqrt A)⁻¹ ^ 2 * B
        - 2 * ((Real.sqrt A)⁻¹ * (C / (A * Real.sqrt A))) * C
        + (C / (A * Real.sqrt A)) ^ 2 * A
      = (A * B - C ^ 2) / A ^ 2 := by
  obtain ⟨s, hs, hspos⟩ : ∃ s : ℝ, s ^ 2 = A ∧ 0 < s :=
    ⟨Real.sqrt A, Real.sq_sqrt hA.le, Real.sqrt_pos.2 hA⟩
  subst hs
  rw [Real.sqrt_sq hspos.le]
  have hne : s ≠ 0 := ne_of_gt hspos
  field_simp
  ring

/-- **The algebraic form of (P).**  With `A = ⟪V,V⟫`, `B = ⟪W,W⟫`,
`C = ⟪V,W⟫`, the vector `A^{-1/2}W − C·A^{-3/2}V` — the derivative of the
normalized profile, see `hasDerivAt_normalize` — has squared length exactly
`(AB − C²)/A²`. -/
theorem projective_speed_sq (V W : E) (hA : 0 < ⟪V, V⟫) :
    ‖(Real.sqrt ⟪V, V⟫)⁻¹ • W - (⟪V, W⟫ / (⟪V, V⟫ * Real.sqrt ⟪V, V⟫)) • V‖ ^ 2
      = (⟪V, V⟫ * ⟪W, W⟫ - ⟪V, W⟫ ^ 2) / ⟪V, V⟫ ^ 2 := by
  set A : ℝ := ⟪V, V⟫ with hAdef
  set B : ℝ := ⟪W, W⟫ with hBdef
  set C : ℝ := ⟪V, W⟫ with hCdef
  have hexp : ‖(Real.sqrt A)⁻¹ • W - (C / (A * Real.sqrt A)) • V‖ ^ 2
      = (Real.sqrt A)⁻¹ ^ 2 * B
        - 2 * ((Real.sqrt A)⁻¹ * (C / (A * Real.sqrt A))) * C
        + (C / (A * Real.sqrt A)) ^ 2 * A := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_sub_self, real_inner_smul_left, real_inner_smul_right]
    rw [show (⟪V, W⟫ : ℝ) = C from rfl, show (⟪W, W⟫ : ℝ) = B from rfl,
      show (⟪V, V⟫ : ℝ) = A from rfl, show (⟪W, V⟫ : ℝ) = C from real_inner_comm V W]
    ring
  rw [hexp]
  exact proj_speed_alg (A := A) (B := B) (C := C) hA

/-- The derivative of the normalized profile `V̂ = V/‖V‖ = V/√⟪V,V⟫`. -/
theorem hasDerivAt_normalize {V : ℝ → E} {W : E} {t : ℝ} (h : HasDerivAt V W t)
    (hA : 0 < ⟪V t, V t⟫) :
    HasDerivAt (fun s => (Real.sqrt ⟪V s, V s⟫)⁻¹ • V s)
      ((Real.sqrt ⟪V t, V t⟫)⁻¹ • W
        - (⟪V t, W⟫ / (⟪V t, V t⟫ * Real.sqrt ⟪V t, V t⟫)) • V t) t := by
  have hAd : HasDerivAt (fun s => (⟪V s, V s⟫ : ℝ)) (2 * ⟪V t, W⟫) t := by
    have := h.inner ℝ h
    simpa [real_inner_comm (V t) W, two_mul] using this
  have hsq : HasDerivAt (fun s => Real.sqrt ⟪V s, V s⟫)
      (2 * ⟪V t, W⟫ / (2 * Real.sqrt ⟪V t, V t⟫)) t := hAd.sqrt (ne_of_gt hA)
  have hspos : 0 < Real.sqrt ⟪V t, V t⟫ := Real.sqrt_pos.2 hA
  have hinv : HasDerivAt (fun s => (Real.sqrt ⟪V s, V s⟫)⁻¹)
      (-(2 * ⟪V t, W⟫ / (2 * Real.sqrt ⟪V t, V t⟫)) / (Real.sqrt ⟪V t, V t⟫) ^ 2) t :=
    hsq.inv (ne_of_gt hspos)
  have hmul := hinv.smul h
  have hcoef : -(2 * ⟪V t, W⟫ / (2 * Real.sqrt ⟪V t, V t⟫)) / (Real.sqrt ⟪V t, V t⟫) ^ 2
      = -(⟪V t, W⟫ / (⟪V t, V t⟫ * Real.sqrt ⟪V t, V t⟫)) := by
    rw [Real.sq_sqrt hA.le]
    field_simp
  rw [hcoef] at hmul
  simpa [sub_eq_add_neg, neg_smul, add_comm] using hmul

/-- **(P): the scale-Gram defect is the squared projective speed.**  For a
differentiable curve `V` in the weighted space, the squared speed of the
*normalized* profile `V̂ = V/‖V‖` equals `Δ/A²` with `Δ = AB − C²` the Gram
determinant of the pair `(V, V_τ)`.

This is the statement that the object the scale-Gram machinery measures is
literally the distance travelled through similarity space, after the marginal
(pure amplitude) direction has been divided out. -/
theorem projective_gram_speed {V : ℝ → E} {W : E} {t : ℝ} (h : HasDerivAt V W t)
    (hA : 0 < ⟪V t, V t⟫) :
    ∃ P : E, HasDerivAt (fun s => (Real.sqrt ⟪V s, V s⟫)⁻¹ • V s) P t ∧
      ‖P‖ ^ 2 = (⟪V t, V t⟫ * ⟪W, W⟫ - ⟪V t, W⟫ ^ 2) / ⟪V t, V t⟫ ^ 2 :=
  ⟨_, hasDerivAt_normalize h hA, projective_speed_sq (V t) W hA⟩

/-! ## The same identity in the weighted integral language -/

variable {α : Type*} [MeasurableSpace α]

/-- **(P) for the weighted Gram quantities of `GaussianScaleGram.lean`.**  The
weighted squared distance from the normalized scaling derivative to the
marginal direction is `Δ/A²`: dividing the profile by its own weighted norm
converts the scale-Gram defect into a projective speed. -/
theorem gram_projective_speed_weighted {μ : Measure α} {Gam : α → ℝ} {f g : α → E3}
    (hf : Integrable (fun x => Gam x * ∑ a, (f x a) ^ 2) μ)
    (hg : Integrable (fun x => Gam x * ∑ a, (g x a) ^ 2) μ)
    (hfg : Integrable (fun x => Gam x * ∑ a, f x a * g x a) μ)
    (hA : 0 < gramA μ Gam f) :
    (1 / gramA μ Gam f)
        * ∫ x, Gam x * ∑ a, (g x a - (gramC μ Gam f g / gramA μ Gam f) * f x a) ^ 2 ∂μ
      = gramDefect μ Gam f g / (gramA μ Gam f) ^ 2 := by
  rw [gram_orbit_distance hf hg hfg hA]
  field_simp

/-! ## The similarity energy identity -/

/-- **(S): the exact similarity-variable energy identity.**

Hypotheses: `V` is a differentiable curve with `V′(τ) = W`; `𝔞` is a symmetric
continuous bilinear form (the Dirichlet form `ν⟪∇·,∇·⟫_ρ`); and the weak form
of the similarity equation holds at time `τ`,

  `⟪V_τ, w⟫ = −𝔞(V,w) − ½⟪V,w⟫ − ⟪N,w⟫`  for every test vector `w`.

Conclusion: the similarity energy `ℋ = ½𝔞(V,V) + ¼‖V‖²` obeys

  `ℋ′(τ) = −‖V_τ‖² − ⟪N,V_τ⟫`.

The dissipative term is *exactly* the squared speed of the solution through
scale space; the only enemy is the pairing of the nonlinear and pressure terms
with that same velocity. -/
theorem similarity_energy_identity {V : ℝ → E} {W N : E} {t : ℝ}
    (bil : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ u v : E, bil u v = bil v u)
    (h : HasDerivAt V W t)
    (heq : ∀ w : E, ⟪W, w⟫ = -bil (V t) w - (1 / 2) * ⟪V t, w⟫ - ⟪N, w⟫) :
    HasDerivAt (fun s => (1 / 2) * bil (V s) (V s) + (1 / 4) * ⟪V s, V s⟫)
      (-⟪W, W⟫ - ⟪N, W⟫) t := by
  have hb : HasDerivAt (fun s => bil (V s)) (bil W) t :=
    (bil.hasFDerivAt (x := V t)).comp_hasDerivAt t h
  have hbil : HasDerivAt (fun s => bil (V s) (V s)) (bil W (V t) + bil (V t) W) t :=
    hb.clm_apply h
  have hbil2 : HasDerivAt (fun s => bil (V s) (V s)) (2 * bil (V t) W) t := by
    have : bil W (V t) + bil (V t) W = 2 * bil (V t) W := by
      rw [hsymm W (V t)]; ring
    rwa [this] at hbil
  have hin : HasDerivAt (fun s => (⟪V s, V s⟫ : ℝ)) (2 * ⟪V t, W⟫) t := by
    have := h.inner ℝ h
    simpa [real_inner_comm (V t) W, two_mul] using this
  have hsum := (hbil2.const_mul (1 / 2 : ℝ)).add (hin.const_mul (1 / 4 : ℝ))
  have hkey : (1 / 2 : ℝ) * (2 * bil (V t) W) + (1 / 4 : ℝ) * (2 * ⟪V t, W⟫)
      = -⟪W, W⟫ - ⟪N, W⟫ := by
    have hW := heq W
    have hsy : bil (V t) W = bil W (V t) := hsymm (V t) W
    have hvw : (⟪V t, W⟫ : ℝ) = ⟪W, V t⟫ := real_inner_comm W (V t)
    rw [hsy, hvw]
    linarith [hW]
  rw [hkey] at hsum
  exact hsum

/-! ## The transverse completion of squares -/

/-- **The quadratic debt.**  A cross term `2cpq` against a coercive transverse
direction `λq²` is paid at cost `c²/λ`, not at cost `c`: this is the algebraic
content of "complete the square before taking absolute values". -/
theorem transverse_quadratic_debt (p q c lam : ℝ) (hlam : 0 < lam) :
    2 * c * p * q ≤ lam * q ^ 2 + (c ^ 2 / lam) * p ^ 2 := by
  obtain ⟨s, hs, hspos⟩ : ∃ s : ℝ, s ^ 2 = lam ∧ 0 < s :=
    ⟨Real.sqrt lam, Real.sq_sqrt hlam.le, Real.sqrt_pos.2 hlam⟩
  subst hs
  have hne : s ≠ 0 := ne_of_gt hspos
  have h := sq_nonneg (s * q - (c / s) * p)
  have hexp : (s * q - (c / s) * p) ^ 2
      = s ^ 2 * q ^ 2 - 2 * c * p * q + (c ^ 2 / s ^ 2) * p ^ 2 := by
    field_simp
    ring
  linarith [hexp ▸ h]

/-! ## The telescopic expenditure -/

/-- **Finite scale expenditure.**  If the similarity energy `ℋ` has derivative
`−‖V_τ‖² − ⟪N,V_τ⟫` (identity (S)) and the pairing is absorbed,
`|⟪N,V_τ⟫| ≤ η‖V_τ‖² + ℛ` with `0 ≤ η < 1`, then the total expenditure over any
window is bounded by the energy drop plus the remainder:

  `(1−η)·∫_{τ₀}^{τ₁} ‖V_τ‖² ≤ ℋ(τ₀) − ℋ(τ₁) + ∫_{τ₀}^{τ₁} ℛ`.

Stated with primitives: `Ecal` is a primitive of `q`, `Rcal` a primitive of
`rem`.  This is the telescope: a *single* payment of the energy drop, not a
worst-case bound paid once per scale. -/
theorem similarity_transverse_expenditure {Hcal Ecal Rcal Hd q rem : ℝ → ℝ}
    {t0 t1 eta : ℝ} (h01 : t0 ≤ t1)
    (hH : ∀ s ∈ Icc t0 t1, HasDerivAt Hcal (Hd s) s)
    (hHle : ∀ s ∈ Icc t0 t1, Hd s ≤ -(1 - eta) * q s + rem s)
    (hE : ∀ s ∈ Icc t0 t1, HasDerivAt Ecal (q s) s)
    (hR : ∀ s ∈ Icc t0 t1, HasDerivAt Rcal (rem s) s) :
    (1 - eta) * (Ecal t1 - Ecal t0) ≤ Hcal t0 - Hcal t1 + (Rcal t1 - Rcal t0) := by
  set G : ℝ → ℝ := fun s => Hcal s + (1 - eta) * Ecal s - Rcal s with hG
  have hderiv : ∀ s ∈ Icc t0 t1,
      HasDerivAt G (Hd s + (1 - eta) * q s - rem s) s := fun s hs =>
    ((hH s hs).add ((hE s hs).const_mul (1 - eta))).sub (hR s hs)
  have hnn : ∀ s ∈ Icc t0 t1, 0 ≤ -(Hd s + (1 - eta) * q s - rem s) := by
    intro s hs
    linarith [hHle s hs]
  have hmono : G t1 ≤ G t0 := by
    have := le_of_hasDerivAt_nonneg_on_Icc (H := fun s => -G s)
      (H' := fun s => -(Hd s + (1 - eta) * q s - rem s))
      h01 (fun s hs => (hderiv s hs).neg) hnn
    linarith [this]
  simp only [hG] at hmono
  linarith [hmono]

/-! ## The bridge to `hstar` -/

/-- **The change of variable `τ = −log r`, and the payment of the scale-Gram
expenditure.**

If the dimensionless scale-Gram ratio `Δ_scale(r)/𝒟(r)` is dominated pointwise
by `K` times the similarity-space speed at similarity time `τ = −log r`, and
the total expenditure over the corresponding `τ`-window is at most `C`, then
the telescopic payment hypothesis `hstar` of `ScaleGramChargeAssembly.lean`
holds with constant `K·C`:

  `Ψ(b) − Ψ(a) ≤ K·C`,   `Ψ′(r) = Δ_scale(r)/(r·𝒟(r))`.

No integrability of the defect over the whole scale range is assumed: the
budget comes from the energy drop through `similarity_transverse_expenditure`.
-/
theorem scaleGram_payment_of_expenditure {Delta Dsc Psi Ecal q : ℝ → ℝ}
    {a b K C : ℝ} (ha : 0 < a) (hab : a ≤ b) (hK : 0 ≤ K)
    (hD : ∀ r ∈ Icc a b, 0 < Dsc r)
    (hPsi : ∀ r ∈ Icc a b, HasDerivAt Psi (Delta r / (r * Dsc r)) r)
    (hE : ∀ s : ℝ, HasDerivAt Ecal (q s) s)
    (hdom : ∀ r ∈ Icc a b, Delta r / Dsc r ≤ K * q (-Real.log r))
    (hbudget : Ecal (-Real.log a) - Ecal (-Real.log b) ≤ C) :
    Psi b - Psi a ≤ K * C := by
  have hpos : ∀ r ∈ Icc a b, 0 < r := fun r hr => lt_of_lt_of_le ha hr.1
  -- `Θ(r) = −K·Ecal(−log r)` is a primitive of `K·q(−log r)/r`
  have hTheta : ∀ r ∈ Icc a b,
      HasDerivAt (fun s => -(K * Ecal (-Real.log s))) (K * q (-Real.log r) / r) r := by
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt (hpos r hr)
    have hlog : HasDerivAt (fun s : ℝ => -Real.log s) (-(1 / r)) r := by
      simpa [one_div] using (Real.hasDerivAt_log hr0).neg
    have hcomp : HasDerivAt (fun s : ℝ => Ecal (-Real.log s))
        (q (-Real.log r) * -(1 / r)) r := (hE (-Real.log r)).comp r hlog
    have := (hcomp.const_mul K).neg
    have heq : -(K * (q (-Real.log r) * -(1 / r))) = K * q (-Real.log r) / r := by
      field_simp
    rwa [heq] at this
  set F : ℝ → ℝ := fun r => -(K * Ecal (-Real.log r)) - Psi r with hF
  have hderiv : ∀ r ∈ Icc a b,
      HasDerivAt F (K * q (-Real.log r) / r - Delta r / (r * Dsc r)) r := fun r hr =>
    (hTheta r hr).sub (hPsi r hr)
  have hnn : ∀ r ∈ Icc a b, 0 ≤ K * q (-Real.log r) / r - Delta r / (r * Dsc r) := by
    intro r hr
    have hr0 : 0 < r := hpos r hr
    have hDr : 0 < Dsc r := hD r hr
    have hdiv : Delta r / (r * Dsc r) = (Delta r / Dsc r) / r := by
      field_simp
    rw [hdiv, sub_nonneg, div_le_div_iff_of_pos_right hr0]
    exact hdom r hr
  have hmono : F a ≤ F b := le_of_hasDerivAt_nonneg_on_Icc hab hderiv hnn
  simp only [hF] at hmono
  have : Psi b - Psi a ≤ K * (Ecal (-Real.log a) - Ecal (-Real.log b)) := by
    nlinarith [hmono]
  calc Psi b - Psi a ≤ K * (Ecal (-Real.log a) - Ecal (-Real.log b)) := this
    _ ≤ K * C := by nlinarith [hbudget, hK]

/-- **The assembled A-side reduction.**  Combining the telescope with the
change of variable: the `hstar` input of `ScaleGramChargeAssembly.lean` follows
from

* the similarity energy identity (S) with absorbed pairing — hypothesis `hH`,
  which `similarity_energy_identity` supplies once the absorption estimate is
  known;
* the pointwise identification of the scale-Gram ratio with the projective
  speed — hypothesis `hdom`, which `projective_gram_speed` makes exact;
* a finite remainder budget — hypothesis `hrembound`.

The conclusion is exactly `Ψ(b) − Ψ(a) ≤ C_*` with
`C_* = (Hcal(τ₀) − Hcal(τ₁) + remainder)·K/(1−η)`. -/
theorem scaleGram_payment_of_similarity_absorption
    {Delta Dsc Psi Hcal Ecal Rcal Hd q rem : ℝ → ℝ} {a b K eta Crem : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hK : 0 ≤ K) (heta : eta < 1)
    (hD : ∀ r ∈ Icc a b, 0 < Dsc r)
    (hPsi : ∀ r ∈ Icc a b, HasDerivAt Psi (Delta r / (r * Dsc r)) r)
    (hH : ∀ s ∈ Icc (-Real.log b) (-Real.log a), HasDerivAt Hcal (Hd s) s)
    (hHle : ∀ s ∈ Icc (-Real.log b) (-Real.log a), Hd s ≤ -(1 - eta) * q s + rem s)
    (hE : ∀ s : ℝ, HasDerivAt Ecal (q s) s)
    (hR : ∀ s ∈ Icc (-Real.log b) (-Real.log a), HasDerivAt Rcal (rem s) s)
    (hrembound : Rcal (-Real.log a) - Rcal (-Real.log b) ≤ Crem)
    (hdom : ∀ r ∈ Icc a b, Delta r / Dsc r ≤ K * q (-Real.log r)) :
    Psi b - Psi a
      ≤ K * ((Hcal (-Real.log b) - Hcal (-Real.log a) + Crem) / (1 - eta)) := by
  have hlog : -Real.log b ≤ -Real.log a := by
    have : Real.log a ≤ Real.log b := Real.log_le_log ha hab
    linarith
  have hexp := similarity_transverse_expenditure (Hcal := Hcal) (Ecal := Ecal)
    (Rcal := Rcal) (Hd := Hd) (q := q) (rem := rem) (eta := eta) hlog hH hHle
    (fun s _ => hE s) hR
  have h1e : 0 < 1 - eta := by linarith
  have hbudget : Ecal (-Real.log a) - Ecal (-Real.log b)
      ≤ (Hcal (-Real.log b) - Hcal (-Real.log a) + Crem) / (1 - eta) := by
    rw [le_div_iff₀ h1e]
    nlinarith [hexp, hrembound]
  exact scaleGram_payment_of_expenditure ha hab hK hD hPsi hE hdom hbudget

end ClayNS
