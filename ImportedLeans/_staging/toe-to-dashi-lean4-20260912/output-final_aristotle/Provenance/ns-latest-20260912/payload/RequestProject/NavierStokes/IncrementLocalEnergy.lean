/-
# The localized energy identity for velocity increments

`RequestProject/NavierStokes/Increments.lean` derives the increment equation

  `∂_t δ_h u_a + (u(·+h)·∇) δ_h u_a = −(δ_h u·∇)u_a − ∂_a δ_h p + ν Δ δ_h u_a`,

which quotients out the constants that obstruct every Liouville/oscillation
argument (`δ_h u ≡ 0` for all `h` *is* spatial constancy).  This file carries
that equation through the local `L²` calculation, i.e. it multiplies by
`δ_h u` and organises every term:

* `ClayNS.increment_quadratic_identity` — the transported-quadratic identity
  for `q = ½|δ_h u|²`;
* `ClayNS.divg_incrVec` — the increment is divergence free, hence
* `ClayNS.incr_pressure_divergence` — **the pressure cancellation**: the
  pressure enters the increment energy balance *only* through the divergence
  `div(δ_h p · δ_h u)`, i.e. only as a boundary flux, with no interior term;
* `ClayNS.incr_transport_divergence` — likewise the advective term is the pure
  divergence `div(q · u(·+h))`, since the transporting field is divergence free;
* `ClayNS.increment_local_energy_identity` — the resulting exact local energy
  identity in divergence form

  `∂_t q + div( q·u(·+h) + δ_h p·δ_h u ) = ν(Δq − |∇δ_h u|²) − δ_h u·(δ_h u·∇)u`.

  So after localization every term except the last is either a divergence (a
  flux against the cutoff) or the good dissipation.  **The only interior
  obstruction is the stretching term.**
* `ClayNS.increment_localized_energy_identity` — the same identity localized by
  a time-independent cutoff `Φ`, with all `Φ`-derivatives displayed:

  `∂_t(Φq) + div(Φ·F − νΦ∇q + νq∇Φ) = F·∇Φ + νqΔΦ − νΦ|∇δ_h u|² − Φ·(stretching)`.

* `ClayNS.incrStretch_eq_strain` — the stretching term only sees the *symmetric*
  part of `∇u` (the strain): the antisymmetric/vorticity part cancels exactly;
* `ClayNS.incrStretch_abs_le` and
  `ClayNS.increment_localized_dissipation_le` — the resulting quantitative
  statement: with a strain bound `K` the interior obstruction is at most
  `3K|δ_h u|²`, which is exactly the scale-critical competition against the
  dissipation `ν|∇δ_h u|²` discussed in the route notes.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.Increments
import RequestProject.NavierStokes.EnergyIdentity

open scoped BigOperators

noncomputable section

namespace ClayNS

/-! ## The increment fields -/

/-- The `a`-th component of the increment `δ_h u = u(·+h) − u`. -/
def incrComp (h : E3) (V : STime → E3) (a : Fin 3) : STime → ℝ :=
  fun z => shift h V z a - V z a

/-- The increment `δ_h u = u(·+h) − u` as a vector field. -/
def incrVec (h : E3) (V : STime → E3) : STime → E3 := fun z => shift h V z - V z

/-- The pressure increment `δ_h p`. -/
def incrPres (h : E3) (P : STime → ℝ) : STime → ℝ := fun z => shift h P z - P z

/-- The increment energy density `q = ½|δ_h u|²`. -/
def incrQuad (h : E3) (V : STime → E3) : STime → ℝ := quad (incrComp h V)

/-- The increment dissipation density `|∇δ_h u|²`. -/
def incrDissip (h : E3) (V : STime → E3) : STime → ℝ :=
  fun z => ∑ k, ∑ a, dvec (0, ee k) (incrComp h V a) z * dvec (0, ee k) (incrComp h V a) z

/-- The stretching (interior obstruction) term `δ_h u · (δ_h u·∇)u`. -/
def incrStretch (h : E3) (V : STime → E3) : STime → ℝ :=
  fun z => ∑ a, incrComp h V a z * ∑ j, incrComp h V j z * dvec (0, ee j) (fun w => V w a) z

/-- The increment energy flux `F = q·u(·+h) + δ_h p·δ_h u`. -/
def incrFlux (h : E3) (V : STime → E3) (P : STime → ℝ) : STime → E3 :=
  fun z => incrQuad h V z • shift h V z + incrPres h P z • incrVec h V z

@[simp] lemma incrVec_coord (h : E3) (V : STime → E3) (z : STime) (a : Fin 3) :
    incrVec h V z a = incrComp h V a z := rfl

lemma contDiff_incrVec {V : STime → E3} (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    ContDiff ℝ (⊤ : ℕ∞) (incrVec h V) := (contDiff_shift h hV).sub hV

lemma contDiff_incrComp {V : STime → E3} (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (a : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (incrComp h V a) :=
  contDiff_coord (incrVec h V) (contDiff_incrVec h hV) a

lemma contDiff_incrPres {P : STime → ℝ} (h : E3) (hP : ContDiff ℝ (⊤ : ℕ∞) P) :
    ContDiff ℝ (⊤ : ℕ∞) (incrPres h P) := (contDiff_shift h hP).sub hP

lemma contDiff_incrQuad {V : STime → E3} (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) :=
  contDiff_quad (incrComp h V) (fun a => contDiff_incrComp h hV a)

/-! ## The quadratic identity for the increment -/

/-- Multiplying the increment equation by `δ_h u`: the transported-quadratic
identity for `q = ½|δ_h u|²`, with the increment transported by `u(·+h)`. -/
theorem increment_quadratic_identity (nu : ℝ) (V : STime → E3) (P : STime → ℝ) (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (z : STime) :
    dvec (1, 0) (incrQuad h V) z + ∑ j, shift h V z j * dvec (0, ee j) (incrQuad h V) z
      = (∑ a, incrComp h V a z *
            (-(∑ j, incrComp h V j z * dvec (0, ee j) (fun w => V w a) z)
              - dvec (0, ee a) (incrPres h P) z))
        + nu * (lap (incrQuad h V) z - incrDissip h V z) :=
  transported_quadratic_identity nu (shift h V) (incrComp h V)
    (fun a z => -(∑ j, incrComp h V j z * dvec (0, ee j) (fun w => V w a) z)
      - dvec (0, ee a) (incrPres h P) z)
    (fun a => contDiff_incrComp h hV a)
    (fun a z => increment_transport nu V P h hV hP hmom a z) z

/-! ## Incompressibility of the increment, and the two divergence terms -/

/-- Divergences add. -/
lemma divg_add (V V' : STime → E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hV' : ContDiff ℝ (⊤ : ℕ∞) V')
    (z : STime) : divg (fun w => V w + V' w) z = divg V z + divg V' z := by
  have hadd : ContDiff ℝ (⊤ : ℕ∞) (fun w => V w + V' w) := hV.add hV'
  rw [divg_eq_sum _ hadd z, divg_eq_sum V hV z, divg_eq_sum V' hV' z, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcoord : (fun w : STime => (V w + V' w) i) = fun w => V w i + V' w i := rfl
  rw [hcoord]
  exact dvec_add _ _ z ((differentiable_of_contDiffTop (contDiff_coord V hV i)) z)
    ((differentiable_of_contDiffTop (contDiff_coord V' hV' i)) z) (0, ee i)

/-- **The increment of a divergence-free field is divergence free.** -/
lemma divg_incrVec {V : STime → E3} (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hdiv : ∀ z : STime, divg V z = 0) (z : STime) : divg (incrVec h V) z = 0 := by
  have h1 : divg (incrVec h V) z = divg (shift h V) z - divg V z :=
    divg_sub _ _ (contDiff_shift h hV) hV z
  rw [h1, divg_shift, hdiv, hdiv, sub_zero]

/-- **The advective term is a pure divergence**: `(u(·+h)·∇)q = div(q·u(·+h))`. -/
lemma incr_transport_divergence {V : STime → E3} (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hdiv : ∀ z : STime, divg V z = 0) (z : STime) :
    divg (fun w => incrQuad h V w • shift h V w) z
      = ∑ j, shift h V z j * dvec (0, ee j) (incrQuad h V) z :=
  pressure_work_divergence (shift h V) (incrQuad h V) (contDiff_shift h hV)
    (contDiff_incrQuad h hV) (shift_incompressible h hdiv) z

/-- **The pressure cancellation.**  Because the increment is divergence free,
the pressure enters the increment energy balance only as the divergence
`div(δ_h p · δ_h u)` — a flux, with no interior term. -/
lemma incr_pressure_divergence {V : STime → E3} {P : STime → ℝ} (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hdiv : ∀ z : STime, divg V z = 0) (z : STime) :
    divg (fun w => incrPres h P w • incrVec h V w) z
      = ∑ a, incrComp h V a z * dvec (0, ee a) (incrPres h P) z := by
  have h1 := pressure_work_divergence (incrVec h V) (incrPres h P) (contDiff_incrVec h hV)
    (contDiff_incrPres h hP) (divg_incrVec h hV hdiv) z
  rw [h1]
  exact Finset.sum_congr rfl fun a _ => by rw [incrVec_coord]

/-! ## The local energy identity for the increment -/

/-- **Local energy identity for the increment.**  For a smooth solution `(u,p)`
of the zero-force Navier–Stokes system with `div u = 0`, the increment energy
density `q = ½|δ_h u|²` satisfies exactly

`∂_t q + div( q·u(·+h) + δ_h p·δ_h u ) = ν(Δq − |∇δ_h u|²) − δ_h u·(δ_h u·∇)u`.

Every term other than the last is either a divergence (i.e. a flux, which after
localization is paid for by derivatives of the cutoff) or the good dissipation.
The stretching term is the only interior obstruction. -/
theorem increment_local_energy_identity (nu : ℝ) (V : STime → E3) (P : STime → ℝ) (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (z : STime) :
    dvec (1, 0) (incrQuad h V) z + divg (incrFlux h V P) z
      = nu * (lap (incrQuad h V) z - incrDissip h V z) - incrStretch h V z := by
  have hq := increment_quadratic_identity nu V P h hV hP hmom z
  have hsplit : divg (incrFlux h V P) z
      = divg (fun w => incrQuad h V w • shift h V w) z
        + divg (fun w => incrPres h P w • incrVec h V w) z :=
    divg_add _ _ ((contDiff_incrQuad h hV).smul (contDiff_shift h hV))
      ((contDiff_incrPres h hP).smul (contDiff_incrVec h hV)) z
  have hQ : (∑ a, incrComp h V a z *
        (-(∑ j, incrComp h V j z * dvec (0, ee j) (fun w => V w a) z)
          - dvec (0, ee a) (incrPres h P) z))
      = - incrStretch h V z
        - ∑ a, incrComp h V a z * dvec (0, ee a) (incrPres h P) z := by
    rw [incrStretch, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hsplit, incr_transport_divergence h hV hdiv z, incr_pressure_divergence h hV hP hdiv z]
  rw [hQ] at hq
  linarith [hq]

/-! ## The structure of the interior obstruction -/

/-- A quadratic form in three variables only sees the symmetric part of its
matrix. -/
lemma quadForm_eq_strain (w : Fin 3 → ℝ) (T : Fin 3 → Fin 3 → ℝ) :
    (∑ a, w a * ∑ j, w j * T j a)
      = ∑ i, ∑ a, w i * w a * ((T i a + T a i) / 2) := by
  simp only [Fin.sum_univ_three]
  ring

/-- A quadratic form with entries bounded by `K` is bounded by `3K|w|²`. -/
lemma quadForm_abs_le (w : Fin 3 → ℝ) (T : Fin 3 → Fin 3 → ℝ) (K : ℝ)
    (hK : ∀ i a : Fin 3, |T i a| ≤ K) :
    |∑ a, w a * ∑ j, w j * T j a| ≤ 3 * K * ∑ a, w a * w a := by
  have hb : ∀ i a : Fin 3,
      w i * w a * T i a ≤ K * ((w i) ^ 2 + (w a) ^ 2) / 2 ∧
        -(K * ((w i) ^ 2 + (w a) ^ 2) / 2) ≤ w i * w a * T i a := by
    intro i a
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hK i a)
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hhi) (sq_nonneg (w i + w a)),
        mul_nonneg (by linarith : (0 : ℝ) ≤ K + T i a) (sq_nonneg (w i - w a))]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hhi) (sq_nonneg (w i - w a)),
        mul_nonneg (by linarith : (0 : ℝ) ≤ K + T i a) (sq_nonneg (w i + w a))]
  have h00 := hb 0 0; have h01 := hb 0 1; have h02 := hb 0 2
  have h10 := hb 1 0; have h11 := hb 1 1; have h12 := hb 1 2
  have h20 := hb 2 0; have h21 := hb 2 1; have h22 := hb 2 2
  simp only [Fin.sum_univ_three] at *
  rw [abs_le]
  constructor <;> nlinarith [h00.1, h00.2, h01.1, h01.2, h02.1, h02.2, h10.1, h10.2,
    h11.1, h11.2, h12.1, h12.2, h20.1, h20.2, h21.1, h21.2, h22.1, h22.2]

/-- **Only the strain appears.**  The stretching term contracts `δ_h u ⊗ δ_h u`
against `∇u`, so it only sees the *symmetric* part of `∇u`; the antisymmetric
(vorticity) part cancels identically. -/
theorem incrStretch_eq_strain (h : E3) (V : STime → E3) (z : STime) :
    incrStretch h V z
      = ∑ i, ∑ a, incrComp h V i z * incrComp h V a z *
          ((dvec (0, ee i) (fun w => V w a) z + dvec (0, ee a) (fun w => V w i) z) / 2) :=
  quadForm_eq_strain (fun a => incrComp h V a z)
    (fun i a => dvec (0, ee i) (fun w => V w a) z)

/-- With a bound `K` on every entry of `∇u`, the interior obstruction is at
most `3K|δ_h u|²`. -/
theorem incrStretch_abs_le (h : E3) (V : STime → E3) (z : STime) (K : ℝ)
    (hK : ∀ i a : Fin 3, |dvec (0, ee i) (fun w => V w a) z| ≤ K) :
    |incrStretch h V z| ≤ 3 * K * ∑ a, incrComp h V a z * incrComp h V a z :=
  quadForm_abs_le (fun a => incrComp h V a z)
    (fun i a => dvec (0, ee i) (fun w => V w a) z) K hK

lemma sum_sq_incrComp (h : E3) (V : STime → E3) (z : STime) :
    (∑ a, incrComp h V a z * incrComp h V a z) = 2 * incrQuad h V z := by
  rw [incrQuad, quad]
  ring

/-! ## Localization by a cutoff -/

/-- The gradient is smooth. -/
lemma contDiff_grad {f : STime → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w => grad f w) :=
  ContDiff.sum fun i _ => (contDiff_dvec f hf (0, ee i)).smul contDiff_const

@[simp] lemma grad_coord (f : STime → ℝ) (z : STime) (i : Fin 3) :
    grad f z i = dvec (0, ee i) f z := by
  simp [grad, dspace_eq_dvec, ee, Pi.single_apply]

/-- Leibniz rule for the divergence of a scalar multiple of a vector field. -/
lemma divg_smul (f : STime → ℝ) (G : STime → E3) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (z : STime) :
    divg (fun w => f w • G w) z
      = (∑ i, dvec (0, ee i) f z * G z i) + f z * divg G z := by
  have hprod : ContDiff ℝ (⊤ : ℕ∞) (fun w => f w • G w) := hf.smul hG
  have hstep : ∀ i : Fin 3, dvec (0, ee i) (fun w => (f w • G w) i) z
      = dvec (0, ee i) f z * G z i + f z * dvec (0, ee i) (fun w => G w i) z := by
    intro i
    have hcoord : (fun w : STime => (f w • G w) i) = fun w => f w * G w i := by
      funext w; simp
    rw [hcoord]
    exact dvec_mul f (fun w => G w i) z ((differentiable_of_contDiffTop hf) z)
      ((differentiable_of_contDiffTop (contDiff_coord G hG i)) z) (0, ee i)
  rw [divg_eq_sum _ hprod z, Finset.sum_congr rfl (fun i _ => hstep i), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← divg_eq_sum G hG z]

/-- Divergences commute with scalar multiples. -/
lemma divg_cmul (c : ℝ) (G : STime → E3) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (z : STime) :
    divg (fun w => c • G w) z = c * divg G z := by
  have h := divg_smul (fun _ => c) G contDiff_const hG z
  have hzero : ∀ i : Fin 3, dvec (0, ee i) (fun _ : STime => c) z = 0 := by
    intro i; simp [dvec]
  simpa [hzero] using h

/-- The localized increment energy flux
`Φ·F − ν(Φ∇q − q∇Φ)`, `F` the increment energy flux and `q = ½|δ_h u|²`. -/
def incrLocFlux (nu : ℝ) (h : E3) (V : STime → E3) (P Phi : STime → ℝ) : STime → E3 :=
  fun z => Phi z • incrFlux h V P z
    - nu • (Phi z • grad (incrQuad h V) z - incrQuad h V z • grad Phi z)

/-- **The localized increment energy identity.**  For a time-independent smooth
cutoff `Φ`,

`∂_t(Φq) + div(Φ·F − ν(Φ∇q − q∇Φ)) = ∇Φ·F + νqΔΦ − νΦ|∇δ_h u|² − Φ·δ_h u·(δ_h u·∇)u`,

where `q = ½|δ_h u|²` and `F = q·u(·+h) + δ_h p·δ_h u`.  After integration the
left-hand divergence disappears, and every remaining term except the last is
either the good dissipation or is paid for by derivatives of the cutoff; in
particular **the pressure appears only inside `F`, i.e. only against `∇Φ`**. -/
theorem increment_localized_energy_identity (nu : ℝ) (V : STime → E3) (P Phi : STime → ℝ)
    (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) (hPhiT : ∀ z : STime, dvec (1, 0) Phi z = 0)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (z : STime) :
    dvec (1, 0) (fun w => Phi w * incrQuad h V w) z + divg (incrLocFlux nu h V P Phi) z
      = (∑ i, dvec (0, ee i) Phi z * incrFlux h V P z i)
        + nu * incrQuad h V z * lap Phi z
        - nu * Phi z * incrDissip h V z
        - Phi z * incrStretch h V z := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  have hF : ContDiff ℝ (⊤ : ℕ∞) (incrFlux h V P) :=
    (hq.smul (contDiff_shift h hV)).add ((contDiff_incrPres h hP).smul (contDiff_incrVec h hV))
  have hgq : ContDiff ℝ (⊤ : ℕ∞) (fun w => grad (incrQuad h V) w) := contDiff_grad hq
  have hgPhi : ContDiff ℝ (⊤ : ℕ∞) (fun w => grad Phi w) := contDiff_grad hPhi
  -- the base identity
  have hbase := increment_local_energy_identity nu V P h hV hP hdiv hmom z
  -- the time derivative of the localized density
  have htime : dvec (1, 0) (fun w => Phi w * incrQuad h V w) z
      = Phi z * dvec (1, 0) (incrQuad h V) z := by
    rw [dvec_mul Phi (incrQuad h V) z ((differentiable_of_contDiffTop hPhi) z)
      ((differentiable_of_contDiffTop hq) z) (1, 0), hPhiT z]
    ring
  -- the three divergences
  have hd1 : divg (fun w => Phi w • incrFlux h V P w) z
      = (∑ i, dvec (0, ee i) Phi z * incrFlux h V P z i) + Phi z * divg (incrFlux h V P) z :=
    divg_smul Phi (incrFlux h V P) hPhi hF z
  have hd2 : divg (fun w => Phi w • grad (incrQuad h V) w) z
      = (∑ i, dvec (0, ee i) Phi z * dvec (0, ee i) (incrQuad h V) z)
        + Phi z * lap (incrQuad h V) z := by
    rw [divg_smul Phi (fun w => grad (incrQuad h V) w) hPhi hgq z,
      divg_grad (incrQuad h V) hq z]
    simp
  have hd3 : divg (fun w => incrQuad h V w • grad Phi w) z
      = (∑ i, dvec (0, ee i) Phi z * dvec (0, ee i) (incrQuad h V) z)
        + incrQuad h V z * lap Phi z := by
    rw [divg_smul (incrQuad h V) (fun w => grad Phi w) hq hgPhi z, divg_grad Phi hPhi z]
    simp only [grad_coord]
    congr 1
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hd4 : divg (incrLocFlux nu h V P Phi) z
      = divg (fun w => Phi w • incrFlux h V P w) z
        - nu * (divg (fun w => Phi w • grad (incrQuad h V) w) z
            - divg (fun w => incrQuad h V w • grad Phi w) z) := by
    have hinner : ContDiff ℝ (⊤ : ℕ∞)
        (fun w => Phi w • grad (incrQuad h V) w - incrQuad h V w • grad Phi w) :=
      (hPhi.smul hgq).sub (hq.smul hgPhi)
    have hfun : incrLocFlux nu h V P Phi = fun w => Phi w • incrFlux h V P w
        - nu • (Phi w • grad (incrQuad h V) w - incrQuad h V w • grad Phi w) := rfl
    rw [hfun,
      divg_sub (fun w => Phi w • incrFlux h V P w)
        (fun w => nu • (Phi w • grad (incrQuad h V) w - incrQuad h V w • grad Phi w))
        (hPhi.smul hF) (hinner.const_smul nu) z,
      divg_cmul nu
        (fun w => Phi w • grad (incrQuad h V) w - incrQuad h V w • grad Phi w) hinner z,
      divg_sub (fun w => Phi w • grad (incrQuad h V) w) (fun w => incrQuad h V w • grad Phi w)
        (hPhi.smul hgq) (hq.smul hgPhi) z]
  rw [htime, hd4, hd1, hd2, hd3]
  linear_combination Phi z * hbase

/-- **The interior obstruction, quantified.**  With a bound `K` on every entry
of `∇u` and a nonnegative cutoff, the localized identity becomes an inequality
in which the stretching term costs at most `6K·Φq`, to be compared with the
dissipation `νΦ|∇δ_h u|²`.  This is exactly the scale-critical competition the
route has to win. -/
theorem increment_localized_dissipation_le (nu : ℝ) (V : STime → E3) (P Phi : STime → ℝ)
    (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) (hPhiT : ∀ z : STime, dvec (1, 0) Phi z = 0)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (z : STime) (hPhi0 : 0 ≤ Phi z) (K : ℝ)
    (hK : ∀ i a : Fin 3, |dvec (0, ee i) (fun w => V w a) z| ≤ K) :
    nu * Phi z * incrDissip h V z
      ≤ - dvec (1, 0) (fun w => Phi w * incrQuad h V w) z
        - divg (incrLocFlux nu h V P Phi) z
        + (∑ i, dvec (0, ee i) Phi z * incrFlux h V P z i)
        + nu * incrQuad h V z * lap Phi z
        + 6 * K * Phi z * incrQuad h V z := by
  have hid := increment_localized_energy_identity nu V P Phi h hV hP hPhi hPhiT hdiv hmom z
  have hstr : |incrStretch h V z| ≤ 3 * K * (2 * incrQuad h V z) := by
    have := incrStretch_abs_le h V z K hK
    rwa [sum_sq_incrComp] at this
  have hle : - incrStretch h V z ≤ 6 * K * incrQuad h V z := by
    have h1 := (abs_le.mp hstr).1
    linarith
  have hmul : Phi z * (- incrStretch h V z) ≤ Phi z * (6 * K * incrQuad h V z) :=
    mul_le_mul_of_nonneg_left hle hPhi0
  linarith [hid, hmul]

/-! ## Transferring the derivative off `u`: the amplitude form of the obstruction

The bound `|stretching| ≤ 3K|δ_h u|²` of `incrStretch_abs_le` costs a bound `K`
on `∇u`, which is exactly the quantity a regularity argument may not have.  It
can be avoided: because the increment is divergence free,

  `δ_h u·(δ_h u·∇)u = div( (u·δ_h u)·δ_h u ) − ∑ u_a δ_h u_j ∂_j δ_h u_a`,

so up to one more flux the derivative sits on the *increment*, and only the
amplitude of `u` is needed.  The price is half of the dissipation and a
zeroth-order term with coefficient `|u|²/ν` — i.e. exactly the local Reynolds
number `|u|R/ν` when compared at scale `R` with the damping rate `ν/R²`.
-/

/-- The scalar `u·δ_h u`. -/
def incrPair (h : E3) (V : STime → E3) : STime → ℝ :=
  fun z => ∑ a, V z a * incrComp h V a z

/-- The transferred obstruction `∑_{a,j} u_a δ_h u_j ∂_j δ_h u_a`: the derivative
now falls on the increment, not on `u`. -/
def incrTransfer (h : E3) (V : STime → E3) : STime → ℝ :=
  fun z => ∑ a, ∑ j, V z a * incrComp h V j z * dvec (0, ee j) (incrComp h V a) z

lemma contDiff_incrPair {V : STime → E3} (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    ContDiff ℝ (⊤ : ℕ∞) (incrPair h V) :=
  ContDiff.sum fun a _ => (contDiff_coord V hV a).mul (contDiff_incrComp h hV a)

/-- **Derivative transfer for the stretching term.**  For a divergence-free `u`,

`δ_h u·(δ_h u·∇)u = div((u·δ_h u)δ_h u) − ∑_{a,j} u_a δ_h u_j ∂_j δ_h u_a`.

The interior obstruction therefore needs no bound on `∇u` at all: only the
amplitude of `u`, at the cost of one further flux. -/
theorem incrStretch_divergence_transfer {V : STime → E3} (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hdiv : ∀ z : STime, divg V z = 0) (z : STime) :
    incrStretch h V z
      = divg (fun w => incrPair h V w • incrVec h V w) z - incrTransfer h V z := by
  have hdvecPair : ∀ j : Fin 3, dvec (0, ee j) (incrPair h V) z
      = ∑ a, (dvec (0, ee j) (fun w => V w a) z * incrComp h V a z
          + V z a * dvec (0, ee j) (incrComp h V a) z) := by
    intro j
    have hterm : ∀ a : Fin 3, dvec (0, ee j) (fun w => V w a * incrComp h V a w) z
        = dvec (0, ee j) (fun w => V w a) z * incrComp h V a z
          + V z a * dvec (0, ee j) (incrComp h V a) z := by
      intro a
      exact dvec_mul (fun w => V w a) (incrComp h V a) z
        ((differentiable_of_contDiffTop (contDiff_coord V hV a)) z)
        ((differentiable_of_contDiffTop (contDiff_incrComp h hV a)) z) (0, ee j)
    have hfun : incrPair h V = fun w => ∑ a, V w a * incrComp h V a w := rfl
    rw [hfun, dvec_sum Finset.univ (fun (a : Fin 3) (w : STime) => V w a * incrComp h V a w) z
      (fun a _ => (differentiable_of_contDiffTop
        ((contDiff_coord V hV a).mul (contDiff_incrComp h hV a))) z) (0, ee j)]
    exact Finset.sum_congr rfl fun a _ => hterm a
  rw [divg_smul (incrPair h V) (incrVec h V) (contDiff_incrPair h hV) (contDiff_incrVec h hV) z,
    divg_incrVec h hV hdiv z]
  simp only [incrVec_coord, mul_zero, add_zero,
    Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => congrArg (fun t => t * incrComp h V j z)
      (hdvecPair j))]
  simp only [incrStretch, incrTransfer, Fin.sum_univ_three]
  ring

/-- Young's inequality in the form needed for the transferred obstruction. -/
lemma abs_mul_mul_le_young (x y c : ℝ) {eps : ℝ} (heps : 0 < eps) :
    |x * y * c| ≤ eps / 2 * c ^ 2 + 1 / (2 * eps) * (x ^ 2 * y ^ 2) := by
  have hkey : |x * y| * |c| ≤ eps / 2 * c ^ 2 + 1 / (2 * eps) * (x * y) ^ 2 := by
    have hsq : eps / 2 * |c| ^ 2 + 1 / (2 * eps) * |x * y| ^ 2 - |x * y| * |c|
        = 1 / (2 * eps) * (|x * y| - eps * |c|) ^ 2 := by
      field_simp
      ring
    have hpos : (0 : ℝ) ≤ 1 / (2 * eps) * (|x * y| - eps * |c|) ^ 2 :=
      mul_nonneg (by positivity) (sq_nonneg _)
    have := hsq ▸ hpos
    rw [sq_abs, sq_abs] at this
    linarith
  calc |x * y * c| = |x * y| * |c| := by rw [abs_mul]
    _ ≤ eps / 2 * c ^ 2 + 1 / (2 * eps) * (x * y) ^ 2 := hkey
    _ = eps / 2 * c ^ 2 + 1 / (2 * eps) * (x ^ 2 * y ^ 2) := by ring

/-- **The transferred obstruction is controlled by the amplitude alone.**  For
every `ε > 0`,

`|∑_{a,j} u_a δ_h u_j ∂_j δ_h u_a| ≤ (ε/2)|∇δ_h u|² + (1/2ε)|u|²|δ_h u|²`. -/
theorem incrTransfer_abs_le (h : E3) (V : STime → E3) (z : STime) {eps : ℝ} (heps : 0 < eps) :
    |incrTransfer h V z|
      ≤ eps / 2 * incrDissip h V z
        + 1 / (2 * eps) * ((∑ a, V z a * V z a) * ∑ j, incrComp h V j z * incrComp h V j z) := by
  have hb : ∀ a j : Fin 3,
      |V z a * incrComp h V j z * dvec (0, ee j) (incrComp h V a) z|
        ≤ eps / 2 * (dvec (0, ee j) (incrComp h V a) z) ^ 2
          + 1 / (2 * eps) * ((V z a) ^ 2 * (incrComp h V j z) ^ 2) := fun a j =>
    abs_mul_mul_le_young _ _ _ heps
  have h00 := hb 0 0; have h01 := hb 0 1; have h02 := hb 0 2
  have h10 := hb 1 0; have h11 := hb 1 1; have h12 := hb 1 2
  have h20 := hb 2 0; have h21 := hb 2 1; have h22 := hb 2 2
  have htri : |incrTransfer h V z|
      ≤ ∑ a, ∑ j, |V z a * incrComp h V j z * dvec (0, ee j) (incrComp h V a) z| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _
  have hexp : (∑ a, ∑ j, |V z a * incrComp h V j z * dvec (0, ee j) (incrComp h V a) z|)
      ≤ eps / 2 * incrDissip h V z
        + 1 / (2 * eps) * ((∑ a, V z a * V z a) * ∑ j, incrComp h V j z * incrComp h V j z) := by
    simp only [incrDissip, Fin.sum_univ_three]
    nlinarith [h00, h01, h02, h10, h11, h12, h20, h21, h22]
  exact htri.trans hexp

/-- **The amplitude form of the increment energy inequality.**  With `ν > 0`,

`∂_t q + div( F + (u·δ_h u)δ_h u ) ≤ νΔq − (ν/2)|∇δ_h u|² + (|u|²/ν)·q`,

`q = ½|δ_h u|²`, `F = q·u(·+h) + δ_h p·δ_h u`.  No bound on `∇u` is used: the
interior obstruction has been reduced to the amplitude `|u|`, half the
dissipation being spent.  Comparing the surviving zeroth-order coefficient
`|u|²/ν` with the damping rate `ν/R²` supplied by the localized Poincaré
inequality at scale `R` gives the ratio `(|u|R/ν)²`: the increment route
produces a one-step gain exactly when the local Reynolds number is small. -/
theorem increment_local_energy_amplitude_le (nu : ℝ) (hnu : 0 < nu) (V : STime → E3)
    (P : STime → ℝ) (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (z : STime) :
    dvec (1, 0) (incrQuad h V) z
        + divg (incrFlux h V P) z + divg (fun w => incrPair h V w • incrVec h V w) z
      ≤ nu * lap (incrQuad h V) z - nu / 2 * incrDissip h V z
        + (∑ a, V z a * V z a) / nu * incrQuad h V z := by
  have hbase := increment_local_energy_identity nu V P h hV hP hdiv hmom z
  have htransfer := incrStretch_divergence_transfer h hV hdiv z
  have hbound := incrTransfer_abs_le h V z hnu
  have hle : incrTransfer h V z
      ≤ nu / 2 * incrDissip h V z
        + 1 / (2 * nu) * ((∑ a, V z a * V z a) * ∑ j, incrComp h V j z * incrComp h V j z) :=
    (le_abs_self _).trans hbound
  rw [sum_sq_incrComp] at hle
  have hnu' : nu ≠ 0 := ne_of_gt hnu
  have hcoef : 1 / (2 * nu) * ((∑ a, V z a * V z a) * (2 * incrQuad h V z))
      = (∑ a, V z a * V z a) / nu * incrQuad h V z := by
    field_simp
  rw [hcoef] at hle
  linarith [hbase, htransfer, hle]

end ClayNS
