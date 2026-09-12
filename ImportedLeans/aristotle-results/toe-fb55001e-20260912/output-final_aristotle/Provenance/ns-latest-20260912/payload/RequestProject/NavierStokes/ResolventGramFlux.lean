/-
# The signed integrated Gram debt as endpoint flux plus an absorbed remainder

This file assembles the route that survived the two recorded no-gos (the
symmetry/sign route and the naive quartic-flux-via-nonlinearity route):

  viscous pair damping → resolvent-weighted Gram flux → signed integrated Gram.

Two ingredients are proved here and combined with the resolvent-heat
factorization of `ResolventHeatFactorization.lean`.

* `integral_eq_flux_add_weighted_remainder` — the *analytic* flux compiler.  If
  a scalar obeys the damped-forced law `g' = −λ g + r` with `λ > 0`, then on any
  time window
  `∫ g = (g(t₀) − g(t₁))/λ + (1/λ)∫ r`.
  No positivity of `g`, no absolute value and no majorant is used: the identity
  is signed.

* `weighted_remainder_eq` — summing the pairwise remainders against the
  resolvent weights `1/(λ_α+λ_β)` gives exactly `4·resForm A F`, the *same*
  bilinear resolvent object whose diagonal is the positive resolvent energy.

The assembled statement is `signed_gram_integral_bound`:

  `∫_{t₀}^{t₁} D_Gram ≤ 2·resForm(A(t₀)) + ε·∫ resForm(A) + (4/ε)·∫ resForm(F)`

for every `ε > 0`, where `D_Gram(t) = ∑_{α,β} 2⟪A_α,A_β⟫` is the *signed* Gram
debt of the cells, `resForm(A)` is the positive resolvent (heat) energy of the
cells and `resForm(F)` that of the remainder family.  Both the terminal
endpoint and the coherent part of the initial endpoint are paid by positivity —
no absolute bound on either is required — and the mixed term is absorbed into
an arbitrarily small multiple of the very same positive resolvent energy.

The last section instantiates the abstract form on the literal complex carrier
of the Waleffe/Galerkin lane (`Fin 3 → ℂ` with the real part of the Hermitian
pairing) and on the literal viscous pair rate `ν(|p|²+|q|²)`.

**What this does not close.**  The surviving obligation is exactly the
spacetime size of the remainder resolvent energy `∫_{t₀}^{t₁} resForm(F(t))`,
i.e. `∫∫ ‖F_s(t)‖² ds dt` for the heat-weighted nonlinear remainder cells.
Nothing here bounds that quantity, and no Clay-level or Package-A claim is made.
-/
import RequestProject.NavierStokes.ResolventHeatFactorization
import RequestProject.NavierStokes.WaleffeForcingMajorant
import RequestProject.NavierStokes.WaleffeSerrinReduction

noncomputable section

open MeasureTheory Set intervalIntegral

namespace ClayNS.Resolvent

/-! ## The analytic flux compiler -/

/-- **R290, analytically.**  A damped-forced scalar `g' = −λ g + r` with `λ > 0`
has its *signed* time integral equal to an endpoint flux plus the
resolvent-weighted integral of the forcing. -/
theorem integral_eq_flux_add_weighted_remainder
    (g r : ℝ → ℝ) (lam t₀ t₁ : ℝ) (hlam : 0 < lam)
    (hg : ∀ t ∈ uIcc t₀ t₁, HasDerivAt g (-(lam * g t) + r t) t)
    (hr : IntervalIntegrable r volume t₀ t₁) :
    ∫ t in t₀..t₁, g t = (g t₀ - g t₁) / lam + (1 / lam) * ∫ t in t₀..t₁, r t := by
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have hgc : ContinuousOn g (uIcc t₀ t₁) := fun t ht =>
    ((hg t ht).continuousAt).continuousWithinAt
  have hgi : IntervalIntegrable g volume t₀ t₁ :=
    ContinuousOn.intervalIntegrable hgc
  have hf : ∀ t ∈ uIcc t₀ t₁,
      HasDerivAt (fun t => (1 / lam) * g t) (-(g t) + (1 / lam) * r t) t := by
    intro t ht
    have := (hg t ht).const_mul (1 / lam)
    have heq : (1 / lam) * (-(lam * g t) + r t) = -(g t) + (1 / lam) * r t := by
      field_simp
    rwa [heq] at this
  have hint : IntervalIntegrable (fun t => -(g t) + (1 / lam) * r t) volume t₀ t₁ :=
    (hgi.neg).add (hr.const_mul _)
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt hf hint
  have hsplit : (∫ t in t₀..t₁, (-(g t) + (1 / lam) * r t))
      = -(∫ t in t₀..t₁, g t) + (1 / lam) * ∫ t in t₀..t₁, r t := by
    rw [intervalIntegral.integral_add (f := fun t => -(g t)) (g := fun t => (1 / lam) * r t)
        hgi.neg (hr.const_mul _), intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul]
  rw [hsplit] at hmain
  have hgoal : ∫ t in t₀..t₁, g t
      = (1 / lam) * g t₀ - (1 / lam) * g t₁ + (1 / lam) * ∫ t in t₀..t₁, r t := by
    linarith [hmain]
  rw [hgoal]
  field_simp

/-! ## Pairwise Gram scalars and the weighted remainder -/

namespace PSDForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (P : PSDForm V)
variable {ι : Type*} [Fintype ι]

/-- The real Gram scalar of two cells, `g_{αβ} = 2 Re⟪A_α, A_β⟫`. -/
def gram (A : ι → V) (i j : ι) : ℝ := 2 * P.form (A i) (A j)

/-- The product-rule remainder of the pair tangent (R291): the two nonlinear
slots of `d/dt g_{αβ}`. -/
def gramRemainder (A F : ι → V) (i j : ι) : ℝ :=
  2 * P.form (F i) (A j) + 2 * P.form (A i) (F j)

/-- The signed Gram debt of the family: the full fibre sum, diagonal and
coherent parts together, with no absolute value anywhere. -/
def gramDebt (A : ι → V) : ℝ := ∑ i, ∑ j, P.gram A i j

theorem gramDebt_eq_two_mul (A : ι → V) :
    P.gramDebt A = 2 * P.form (∑ i, A i) (∑ j, A j) := by
  rw [gramDebt, P.sum_left, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [P.sum_right, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => rfl

/-- The resolvent-weighted sum of the pairwise Gram scalars is twice the
resolvent form of the cells. -/
theorem weighted_gram_eq (lam : ι → ℝ) (A : ι → V) :
    ∑ i, ∑ j, P.gram A i j / (lam i + lam j) = 2 * P.resForm lam A A := by
  rw [resForm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [gram, mul_div_assoc]

/-- **The factorized pair remainder (R299).**  Weighted by the Cauchy kernel
`1/(λ_α+λ_β)`, the whole nonlinear remainder of the Gram tangent is exactly
four times the resolvent pairing of the cells with the remainder family — the
same object whose diagonal is the positive resolvent energy. -/
theorem weighted_remainder_eq (lam : ι → ℝ) (A F : ι → V) :
    ∑ i, ∑ j, P.gramRemainder A F i j / (lam i + lam j) = 4 * P.resForm lam A F := by
  have hsplit : ∑ i, ∑ j, P.gramRemainder A F i j / (lam i + lam j)
      = (∑ i, ∑ j, 2 * P.form (F i) (A j) / (lam i + lam j))
        + ∑ i, ∑ j, 2 * P.form (A i) (F j) / (lam i + lam j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [gramRemainder, add_div]
  have hFA : ∑ i, ∑ j, 2 * P.form (F i) (A j) / (lam i + lam j)
      = 2 * P.resForm lam F A := by
    rw [resForm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_div_assoc]
  have hAF : ∑ i, ∑ j, 2 * P.form (A i) (F j) / (lam i + lam j)
      = 2 * P.resForm lam A F := by
    rw [resForm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_div_assoc]
  rw [hsplit, hFA, hAF, P.resForm_comm lam F A]
  ring

/-! ## The assembled spacetime statement -/

variable (lam : ι → ℝ)

/-- The pairwise flux identity, summed over the fibre: the signed integrated
Gram debt equals the endpoint difference of the resolvent energies plus the
integrated resolvent pairing with the remainder family. -/
theorem integral_gramDebt_eq
    (hlam : ∀ i, 0 < lam i) (A F : ℝ → ι → V) (t₀ t₁ : ℝ)
    (hderiv : ∀ i j, ∀ t ∈ uIcc t₀ t₁,
      HasDerivAt (fun t => P.gram (A t) i j)
        (-((lam i + lam j) * P.gram (A t) i j) + P.gramRemainder (A t) (F t) i j) t)
    (hrem : ∀ i j, IntervalIntegrable
      (fun t => P.gramRemainder (A t) (F t) i j) volume t₀ t₁) :
    ∫ t in t₀..t₁, P.gramDebt (A t)
      = 2 * P.resForm lam (A t₀) (A t₀) - 2 * P.resForm lam (A t₁) (A t₁)
        + 4 * ∫ t in t₀..t₁, P.resForm lam (A t) (F t) := by
  classical
  have hpos : ∀ i j : ι, 0 < lam i + lam j := fun i j => by
    have := hlam i; have := hlam j; linarith
  -- each pairwise Gram scalar is continuous, hence integrable
  have hgi : ∀ i j : ι, IntervalIntegrable (fun t => P.gram (A t) i j) volume t₀ t₁ := by
    intro i j
    exact ContinuousOn.intervalIntegrable fun t ht =>
      (((hderiv i j) t ht).continuousAt).continuousWithinAt
  have hrowint : ∀ i : ι, IntervalIntegrable (fun t => ∑ j, P.gram (A t) i j) volume t₀ t₁ := by
    intro i
    have hfun : (fun t => ∑ j, P.gram (A t) i j)
        = ∑ j ∈ (Finset.univ : Finset ι), (fun t => P.gram (A t) i j) := by
      funext t; simp
    rw [hfun]
    exact IntervalIntegrable.sum (Finset.univ : Finset ι) (fun j _ => hgi i j)
  have hrowrem : ∀ i : ι, IntervalIntegrable
      (fun t => ∑ j, P.gramRemainder (A t) (F t) i j / (lam i + lam j)) volume t₀ t₁ := by
    intro i
    have hfun : (fun t => ∑ j, P.gramRemainder (A t) (F t) i j / (lam i + lam j))
        = ∑ j ∈ (Finset.univ : Finset ι),
            (fun t => P.gramRemainder (A t) (F t) i j / (lam i + lam j)) := by
      funext t; simp
    rw [hfun]
    exact IntervalIntegrable.sum (Finset.univ : Finset ι)
      (fun j _ => (hrem i j).div_const (lam i + lam j))
  -- the pairwise flux identity
  have hpair : ∀ i j : ι, ∫ t in t₀..t₁, P.gram (A t) i j
      = (P.gram (A t₀) i j - P.gram (A t₁) i j) / (lam i + lam j)
        + (1 / (lam i + lam j)) * ∫ t in t₀..t₁, P.gramRemainder (A t) (F t) i j := by
    intro i j
    exact integral_eq_flux_add_weighted_remainder _ _ _ _ _ (hpos i j) (hderiv i j) (hrem i j)
  -- exchange the finite fibre sum with the time integral
  have hswap : ∫ t in t₀..t₁, P.gramDebt (A t)
      = ∑ i, ∑ j, ∫ t in t₀..t₁, P.gram (A t) i j := by
    rw [show (fun t => P.gramDebt (A t)) = fun t => ∑ i, ∑ j, P.gram (A t) i j from rfl]
    rw [intervalIntegral.integral_finset_sum (fun i _ =>
      hrowint i)]
    exact Finset.sum_congr rfl fun i _ =>
      intervalIntegral.integral_finset_sum (fun j _ => hgi i j)
  rw [hswap]
  have hterm : ∑ i, ∑ j, ∫ t in t₀..t₁, P.gram (A t) i j
      = (∑ i, ∑ j, (P.gram (A t₀) i j - P.gram (A t₁) i j) / (lam i + lam j))
        + ∑ i, ∑ j, (1 / (lam i + lam j)) *
            ∫ t in t₀..t₁, P.gramRemainder (A t) (F t) i j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hpair i j
  rw [hterm]
  have hendpoint : (∑ i, ∑ j, (P.gram (A t₀) i j - P.gram (A t₁) i j) / (lam i + lam j))
      = 2 * P.resForm lam (A t₀) (A t₀) - 2 * P.resForm lam (A t₁) (A t₁) := by
    rw [← P.weighted_gram_eq lam (A t₀), ← P.weighted_gram_eq lam (A t₁),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [sub_div]
  rw [hendpoint]
  have hremsum : (∑ i, ∑ j, (1 / (lam i + lam j)) *
        ∫ t in t₀..t₁, P.gramRemainder (A t) (F t) i j)
      = 4 * ∫ t in t₀..t₁, P.resForm lam (A t) (F t) := by
    have hpull : ∀ i j : ι, (1 / (lam i + lam j)) *
        (∫ t in t₀..t₁, P.gramRemainder (A t) (F t) i j)
        = ∫ t in t₀..t₁, P.gramRemainder (A t) (F t) i j / (lam i + lam j) := by
      intro i j
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun t _ => by ring
    have hsum : ∑ i, ∑ j, (1 / (lam i + lam j)) *
        (∫ t in t₀..t₁, P.gramRemainder (A t) (F t) i j)
        = ∫ t in t₀..t₁, ∑ i, ∑ j,
            P.gramRemainder (A t) (F t) i j / (lam i + lam j) := by
      rw [intervalIntegral.integral_finset_sum (fun i _ => hrowrem i)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [intervalIntegral.integral_finset_sum (fun j _ => (hrem i j).div_const _)]
      exact Finset.sum_congr rfl fun j _ => hpull i j
    rw [hsum]
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => P.weighted_remainder_eq lam (A t) (F t)
  rw [hremsum]

/-- **The assembled bound (R299 + R300).**  The signed integrated Gram debt is
bounded by the *initial* resolvent energy of the cells, an arbitrarily small
multiple of the integrated resolvent energy of the cells, and the integrated
resolvent energy of the remainder family. -/
theorem signed_gram_integral_bound
    (hlam : ∀ i, 0 < lam i) (A F : ℝ → ι → V) (t₀ t₁ : ℝ) (ht : t₀ ≤ t₁)
    {ε : ℝ} (hε : 0 < ε)
    (hderiv : ∀ i j, ∀ t ∈ uIcc t₀ t₁,
      HasDerivAt (fun t => P.gram (A t) i j)
        (-((lam i + lam j) * P.gram (A t) i j) + P.gramRemainder (A t) (F t) i j) t)
    (hrem : ∀ i j, IntervalIntegrable
      (fun t => P.gramRemainder (A t) (F t) i j) volume t₀ t₁)
    (hMint : IntervalIntegrable (fun t => P.resForm lam (A t) (F t)) volume t₀ t₁)
    (hAint : IntervalIntegrable (fun t => P.resForm lam (A t) (A t)) volume t₀ t₁)
    (hFint : IntervalIntegrable (fun t => P.resForm lam (F t) (F t)) volume t₀ t₁) :
    ∫ t in t₀..t₁, P.gramDebt (A t)
      ≤ 2 * P.resForm lam (A t₀) (A t₀)
        + ε * (∫ t in t₀..t₁, P.resForm lam (A t) (A t))
        + (4 / ε) * ∫ t in t₀..t₁, P.resForm lam (F t) (F t) := by
  have hid := P.integral_gramDebt_eq lam hlam A F t₀ t₁ hderiv hrem
  have hterm : 0 ≤ 2 * P.resForm lam (A t₁) (A t₁) := by
    have := P.resForm_nonneg lam hlam (A t₁); linarith
  have hyoung : ∀ t : ℝ, 4 * P.resForm lam (A t) (F t)
      ≤ ε * P.resForm lam (A t) (A t) + (4 / ε) * P.resForm lam (F t) (F t) := by
    intro t
    have h := P.resForm_young lam hlam hε (A t) (F t)
    have habs : P.resForm lam (A t) (F t) ≤ |P.resForm lam (A t) (F t)| := le_abs_self _
    linarith [h, habs]
  have hmono : (∫ t in t₀..t₁, 4 * P.resForm lam (A t) (F t))
      ≤ ∫ t in t₀..t₁, (ε * P.resForm lam (A t) (A t)
          + (4 / ε) * P.resForm lam (F t) (F t)) := by
    refine intervalIntegral.integral_mono_on ht (hMint.const_mul 4)
      ((hAint.const_mul ε).add (hFint.const_mul (4 / ε))) ?_
    intro t _
    exact hyoung t
  rw [intervalIntegral.integral_add (hAint.const_mul ε) (hFint.const_mul (4 / ε)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hmono
  rw [hid]
  linarith [hmono, hterm]

end PSDForm

/-! ## The literal Waleffe/Galerkin carrier -/

open ClayNS.Waleffe

/-- The real part of the Hermitian pairing on `ℂ³` is a symmetric positive
semidefinite real bilinear form.  This is the concrete carrier of the R227
mixed-helicity cells. -/
def nsPSD : PSDForm (Fin 3 → ℂ) where
  form u v := (herm u v).re
  symm u v := by
    have h := herm_conj u v
    rw [← h, Complex.conj_re]
  add_left u v w := by
    show (herm (fun i => u i + v i) w).re = (herm u w).re + (herm v w).re
    rw [herm_add_left]
    exact Complex.add_re _ _
  smul_left c u v := by
    have h : herm (c • u) v = (c : ℂ) * herm u v := by
      show herm (fun i => (c : ℂ) * u i) v = (c : ℂ) * herm u v
      rw [herm_smul_left]
      simp
    rw [h]
    simp [Complex.mul_re]
  nonneg u := by
    rw [herm_self]
    simpa using nsq_nonneg u

@[simp] theorem nsPSD_form (u v : Fin 3 → ℂ) : nsPSD.form u v = (herm u v).re := rfl

/-- The literal viscous pair rate `λ_{pq} = ν(|p|² + |q|²)` of a two-leg cell. -/
def viscousPairRate (nu : ℝ) (p q : Wave) : ℝ := nu * (wsq p + wsq q)

theorem viscousPairRate_pos {nu : ℝ} (hnu : 0 < nu) {p q : Wave}
    (hp : wsq p ≠ 0) : 0 < viscousPairRate nu p q := by
  have hpp : 0 < wsq p := lt_of_le_of_ne (wsq_nonneg p) (Ne.symm hp)
  have hqq : 0 ≤ wsq q := wsq_nonneg q
  have : 0 < wsq p + wsq q := by linarith
  exact mul_pos hnu this


/-! ## The Gram tangent from the cell tangent (R291/R292 on the literal carrier)

On the complex Galerkin carrier the pairwise Gram tangent is not an assumption:
it follows from the *cell* tangent by the product rule, with no sign or size
information about the nonlinear slot.
-/

theorem herm_re_hasDerivAt (A B : ℝ → Fin 3 → ℂ) (A' B' : Fin 3 → ℂ) (t : ℝ)
    (hA : ∀ c : Fin 3, HasDerivAt (fun t => A t c) (A' c) t)
    (hB : ∀ c : Fin 3, HasDerivAt (fun t => B t c) (B' c) t) :
    HasDerivAt (fun t => (herm (A t) (B t)).re)
      ((herm A' (B t) + herm (A t) B').re) t := by
  have hterm : ∀ c : Fin 3, HasDerivAt
      (fun t => ((starRingEnd ℂ) (A t c) * B t c).re)
      (((starRingEnd ℂ) (A' c) * B t c + (starRingEnd ℂ) (A t c) * B' c).re) t := by
    intro c
    have hc : HasDerivAt (fun t => (starRingEnd ℂ) (A t c)) ((starRingEnd ℂ) (A' c)) t :=
      (hA c).star
    have hm := hc.mul (hB c)
    have := (Complex.reCLM.hasFDerivAt
      (x := (starRingEnd ℂ) (A t c) * B t c)).comp_hasDerivAt t hm
    simpa [Function.comp_def] using this
  have hsum := HasDerivAt.sum (u := Finset.univ) (A := fun c t =>
    ((starRingEnd ℂ) (A t c) * B t c).re) (fun c _ => hterm c)
  have hlhs : (∑ c : Fin 3, fun t => ((starRingEnd ℂ) (A t c) * B t c).re)
      = fun t => (herm (A t) (B t)).re := by
    funext t
    simp only [Finset.sum_apply]
    rw [herm, Complex.re_sum]
  have hrhs : (∑ c : Fin 3,
      ((starRingEnd ℂ) (A' c) * B t c + (starRingEnd ℂ) (A t c) * B' c).re)
      = (herm A' (B t) + herm (A t) B').re := by
    rw [Complex.add_re, herm, herm, Complex.re_sum, Complex.re_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => Complex.add_re _ _
  rw [hlhs] at hsum
  rw [hrhs] at hsum
  exact hsum

/-- **The damped-forced Gram tangent.**  If every cell obeys the literal damped
tangent `dA_α = −λ_α A_α + F_α` componentwise, then the pairwise Gram scalar
obeys `dg_{αβ} = −(λ_α+λ_β) g_{αβ} + r_{αβ}` with `r` the product-rule
remainder — exactly the hypothesis consumed by the flux compiler. -/
theorem nsPSD_gram_hasDerivAt {ι : Type*} (lam : ι → ℝ)
    (A F : ℝ → ι → Fin 3 → ℂ) (i j : ι) (t : ℝ)
    (hA : ∀ (k : ι) (c : Fin 3),
      HasDerivAt (fun t => A t k c) (-(lam k : ℂ) * A t k c + F t k c) t) :
    HasDerivAt (fun t => nsPSD.gram (A t) i j)
      (-((lam i + lam j) * nsPSD.gram (A t) i j)
        + nsPSD.gramRemainder (A t) (F t) i j) t := by
  set Ai' : Fin 3 → ℂ := fun c => -(lam i : ℂ) * A t i c + F t i c with hAi'
  set Aj' : Fin 3 → ℂ := fun c => -(lam j : ℂ) * A t j c + F t j c with hAj'
  have hbase : HasDerivAt (fun t => (herm (A t i) (A t j)).re)
      ((herm Ai' (A t j) + herm (A t i) Aj').re) t :=
    herm_re_hasDerivAt (fun t => A t i) (fun t => A t j) Ai' Aj' t
      (fun c => hA i c) (fun c => hA j c)
  have hleft : herm Ai' (A t j)
      = -(lam i : ℂ) * herm (A t i) (A t j) + herm (F t i) (A t j) := by
    rw [hAi', herm_add_left (fun c => -(lam i : ℂ) * A t i c) (fun c => F t i c) (A t j),
      herm_smul_left]
    simp
  have hright : herm (A t i) Aj'
      = -(lam j : ℂ) * herm (A t i) (A t j) + herm (A t i) (F t j) := by
    rw [hAj', herm_add_right (A t i) (fun c => -(lam j : ℂ) * A t j c) (fun c => F t j c),
      herm_smul_right]
  have hval : (herm Ai' (A t j) + herm (A t i) Aj').re
      = -((lam i + lam j) * (herm (A t i) (A t j)).re)
        + ((herm (F t i) (A t j)).re + (herm (A t i) (F t j)).re) := by
    rw [hleft, hright]
    simp [Complex.add_re, Complex.mul_re, add_mul]
    ring
  have hscaled := hbase.const_mul (2 : ℝ)
  rw [hval] at hscaled
  have hgoal : (2 : ℝ) * (-((lam i + lam j) * (herm (A t i) (A t j)).re)
        + ((herm (F t i) (A t j)).re + (herm (A t i) (F t j)).re))
      = -((lam i + lam j) * nsPSD.gram (A t) i j)
        + nsPSD.gramRemainder (A t) (F t) i j := by
    simp [PSDForm.gram, PSDForm.gramRemainder]
    ring
  rw [hgoal] at hscaled
  exact hscaled

/-- **The route, on the literal carrier.**  For any finite family of
mixed-helicity two-leg cells of the Galerkin carrier obeying the literal damped
tangent `dA_α = −ν(|p|²+|q|²) A_α + F_α`, the signed integrated Gram debt of the
fibre is bounded by the initial resolvent energy, an arbitrarily small multiple
of the integrated resolvent energy of the cells, and the integrated resolvent
energy of the remainder.  The remaining unpaid object is the last integral. -/
theorem ns_signed_gram_integral_bound
    {ι : Type*} [Fintype ι] (leg : ι → Wave × Wave) {nu : ℝ} (hnu : 0 < nu)
    (hleg : ∀ i, wsq (leg i).1 ≠ 0)
    (A F : ℝ → ι → Fin 3 → ℂ) (t₀ t₁ : ℝ) (ht : t₀ ≤ t₁) {ε : ℝ} (hε : 0 < ε)
    (lam : ι → ℝ) (hlamdef : ∀ i, lam i = viscousPairRate nu (leg i).1 (leg i).2)
    (hcell : ∀ t ∈ uIcc t₀ t₁, ∀ (k : ι) (c : Fin 3),
      HasDerivAt (fun t => A t k c) (-(lam k : ℂ) * A t k c + F t k c) t)
    (hrem : ∀ i j, IntervalIntegrable
      (fun t => nsPSD.gramRemainder (A t) (F t) i j) volume t₀ t₁)
    (hMint : IntervalIntegrable (fun t => nsPSD.resForm lam (A t) (F t)) volume t₀ t₁)
    (hAint : IntervalIntegrable (fun t => nsPSD.resForm lam (A t) (A t)) volume t₀ t₁)
    (hFint : IntervalIntegrable (fun t => nsPSD.resForm lam (F t) (F t)) volume t₀ t₁) :
    ∫ t in t₀..t₁, nsPSD.gramDebt (A t)
      ≤ 2 * nsPSD.resForm lam (A t₀) (A t₀)
        + ε * (∫ t in t₀..t₁, nsPSD.resForm lam (A t) (A t))
        + (4 / ε) * ∫ t in t₀..t₁, nsPSD.resForm lam (F t) (F t) := by
  have hlam : ∀ i, 0 < lam i := by
    intro i
    rw [hlamdef i]
    exact viscousPairRate_pos hnu (hleg i)
  have hderiv : ∀ i j, ∀ t ∈ uIcc t₀ t₁,
      HasDerivAt (fun t => nsPSD.gram (A t) i j)
        (-((lam i + lam j) * nsPSD.gram (A t) i j)
          + nsPSD.gramRemainder (A t) (F t) i j) t :=
    fun i j t htmem => nsPSD_gram_hasDerivAt lam A F i j t (hcell t htmem)
  exact nsPSD.signed_gram_integral_bound lam hlam A F t₀ t₁ ht hε hderiv hrem hMint hAint hFint

end ClayNS.Resolvent
