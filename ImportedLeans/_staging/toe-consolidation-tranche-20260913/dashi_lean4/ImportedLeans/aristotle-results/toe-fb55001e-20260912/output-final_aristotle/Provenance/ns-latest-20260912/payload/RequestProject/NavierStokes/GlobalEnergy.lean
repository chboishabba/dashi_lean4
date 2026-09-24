/-
# Global balances on the torus: the energy identity, the energy inequality and
# the enstrophy balance, all derived.

`RequestProject/NavierStokes/EnergyIdentity.lean` derives the *pointwise*
identities; `RequestProject/NavierStokes/PeriodicIntegral.lean` supplies the two
analytic tools (divergence theorem on the torus, differentiation under the cell
integral).  This file combines them into the global balances that every step of
the Clay ladder — Leray–Hopf theory, Galerkin truncation, BKM/Serrin
continuation, absorption arguments — actually uses:

* `ClayNS.global_quadratic_balance` — for a quadratic density `q = ½|W|²`
  transported by a divergence-free periodic velocity with source `S`,
  `d/dt ∫_cell q = ∫_cell W·S - ν ∫_cell |∇W|²`;
* `ClayNS.energy_balance` — `d/dt ∫_cell ½|u|² = - ν ∫_cell |∇u|²`
  (the pressure term integrates to zero, being a pure divergence);
* `ClayNS.energy_antitone`, `ClayNS.energy_le_initial` — the a priori energy
  inequality `E(t) ≤ E(0)`;
* `ClayNS.enstrophy_balance` — `d/dt ∫_cell ½|ω|² = ∫_cell ω·(ω·∇)u
  - ν ∫_cell |∇ω|²`, the global form of the vortex-stretching budget.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.PeriodicIntegral

open scoped BigOperators
open MeasureTheory Set

noncomputable section

namespace ClayNS

/-! ## Gradient-square density and the global functionals -/

/-- The squared spatial gradient `∑_{k,a} (∂_k W_a)²` of a triple of scalar
fields. -/
def gradSq (W : Fin 3 → STime → ℝ) (z : STime) : ℝ :=
  ∑ k, ∑ a, dvec (0, ee k) (W a) z * dvec (0, ee k) (W a) z

lemma gradSq_nonneg (W : Fin 3 → STime → ℝ) (z : STime) : 0 ≤ gradSq W z :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- Total kinetic energy in the periodicity cell. -/
def energy (V : STime → E3) (t : ℝ) : ℝ := cellInt (fun x => kin V (t, x))

/-- Total enstrophy in the periodicity cell. -/
def enstrophy (V : STime → E3) (t : ℝ) : ℝ := cellInt (fun x => ens V (t, x))

/-! ## Continuity and periodicity bookkeeping -/

lemma continuous_dvec {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (V : STime → G) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (a : STime) : Continuous (dvec a V) :=
  (hV.continuous_fderiv (by simp)).clm_apply continuous_const

lemma spacePeriodic_quad {W : Fin 3 → STime → ℝ} (hW : ∀ a, SpacePeriodic (W a)) :
    SpacePeriodic (quad W) := by
  intro z j
  simp only [quad]
  exact congrArg _ (Finset.sum_congr rfl fun a _ => by rw [hW a z j])

lemma spacePeriodic_coord {V : STime → E3} (hV : SpacePeriodic V) (a : Fin 3) :
    SpacePeriodic (fun w => V w a) := fun z j => congrFun (congrArg _ (hV z j)) a

lemma continuous_time_slice {f : STime → ℝ} (hf : Continuous f) (t : ℝ) :
    Continuous (fun x : E3 => f (t, x)) :=
  hf.comp (continuous_const.prodMk continuous_id)

/-! ## The flux form of advection and diffusion -/

/-- The spatial flux of the quadratic density `q = ½|W|²` carried by `u`:
`Fᵢ = q uᵢ - ν ∂ᵢ q`. -/
def quadFlux (nu : ℝ) (V : STime → E3) (W : Fin 3 → STime → ℝ) (i : Fin 3) : STime → ℝ :=
  fun w => quad W w * V w i - nu * dvec (0, ee i) (quad W) w

/-- Advection plus diffusion of `q` is the divergence of the flux `quadFlux`:
`(u·∇)q - ν Δq = ∑ᵢ ∂ᵢ (q uᵢ - ν ∂ᵢ q)`, using `div u = 0`. -/
lemma quadFlux_divergence_at (nu : ℝ) (V : STime → E3) (W : Fin 3 → STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hW : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (W a)) (z : STime)
    (hdiv : divg V z = 0) :
    ∑ i, dvec (0, ee i) (quadFlux nu V W i) z
      = (∑ j, V z j * dvec (0, ee j) (quad W) z) - nu * lap (quad W) z := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (quad W) := contDiff_quad W hW
  have hqd : Differentiable ℝ (quad W) := differentiable_of_contDiffTop hq
  have hVc : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V w i) := fun i => contDiff_coord V hV i
  have hdq : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (dvec (0, ee i) (quad W)) :=
    fun i => contDiff_dvec (quad W) hq (0, ee i)
  have hterm : ∀ i : Fin 3, dvec (0, ee i) (quadFlux nu V W i) z
      = (dvec (0, ee i) (quad W) z * V z i
          + quad W z * dvec (0, ee i) (fun w => V w i) z)
        - nu * dvec (0, ee i) (dvec (0, ee i) (quad W)) z := by
    intro i
    have hA : DifferentiableAt ℝ (fun w => quad W w * V w i) z :=
      (hqd z).mul ((differentiable_of_contDiffTop (hVc i)) z)
    have hB : DifferentiableAt ℝ (fun w => nu * dvec (0, ee i) (quad W) w) z :=
      ((differentiable_of_contDiffTop (hdq i)) z).const_mul nu
    have h1 : dvec (0, ee i) (quadFlux nu V W i) z
        = dvec (0, ee i) (fun w => quad W w * V w i) z
          - dvec (0, ee i) (fun w => nu * dvec (0, ee i) (quad W) w) z :=
      dvec_sub _ _ z hA hB (0, ee i)
    have h2 : dvec (0, ee i) (fun w => nu * dvec (0, ee i) (quad W) w) z
        = nu * dvec (0, ee i) (dvec (0, ee i) (quad W)) z := by
      simpa [smul_eq_mul] using
        dvec_cmul nu (dvec (0, ee i) (quad W)) z
          ((differentiable_of_contDiffTop (hdq i)) z) (0, ee i)
    rw [h1, h2, dvec_mul (quad W) (fun w => V w i) z (hqd z)
      ((differentiable_of_contDiffTop (hVc i)) z) (0, ee i)]
  have hdivV : ∑ i, dvec (0, ee i) (fun w => V w i) z = 0 := by
    have h := hdiv
    rwa [divg_eq_sum V hV z] at h
  have hlapq : lap (quad W) z = ∑ i, dvec (0, ee i) (dvec (0, ee i) (quad W)) z := rfl
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, hdivV, mul_zero, add_zero,
    hlapq, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The flux divergence identity with incompressibility assumed everywhere. -/
lemma quadFlux_divergence (nu : ℝ) (V : STime → E3) (W : Fin 3 → STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hW : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (W a))
    (hdiv : ∀ w : STime, divg V w = 0) (z : STime) :
    ∑ i, dvec (0, ee i) (quadFlux nu V W i) z
      = (∑ j, V z j * dvec (0, ee j) (quad W) z) - nu * lap (quad W) z :=
  quadFlux_divergence_at nu V W hV hW z (hdiv z)

/-! ## The general global balance -/

/-- **Global balance for a transported quadratic density.**  If each component
of `W` is transported by the divergence-free periodic velocity `u` with source
`S` and viscosity `ν`, then the cell integral of `q = ½|W|²` obeys

`d/dt ∫ q = ∫ W·S - ν ∫ |∇W|²`.

The advection term and the Laplacian both integrate away, being spatial
divergences of periodic fields. -/
theorem global_quadratic_balance_at (nu : ℝ) (V : STime → E3) (W S : Fin 3 → STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVper : SpacePeriodic V)
    (hW : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (W a)) (hWper : ∀ a, SpacePeriodic (W a))
    (t : ℝ)
    (hdiv : ∀ x : E3, divg V (t, x) = 0)
    (heq : ∀ (a : Fin 3) (x : E3),
      dvec (1, 0) (W a) (t, x) + ∑ j, V (t, x) j * dvec (0, ee j) (W a) (t, x)
        = S a (t, x) + nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (W a)) (t, x)) :
    HasDerivAt (fun s => cellInt (fun x => quad W (s, x)))
      (cellInt (fun x => ∑ a, W a (t, x) * S a (t, x))
        - nu * cellInt (fun x => gradSq W (t, x))) t := by
  classical
  have hq : ContDiff ℝ (⊤ : ℕ∞) (quad W) := contDiff_quad W hW
  have hqd : Differentiable ℝ (quad W) := differentiable_of_contDiffTop hq
  have hqper : SpacePeriodic (quad W) := spacePeriodic_quad hWper
  -- the flux is smooth and periodic, so its divergence integrates to zero
  have hfluxSmooth : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (quadFlux nu V W i) := fun i =>
    (hq.mul (contDiff_coord V hV i)).sub
      (contDiff_const.mul (contDiff_dvec (quad W) hq (0, ee i)))
  have hfluxPer : ∀ i, SpacePeriodic (quadFlux nu V W i) := by
    intro i z j
    have h1 : quad W (z.1, z.2 + ee j) = quad W z := hqper z j
    have h2 : V (z.1, z.2 + ee j) i = V z i := spacePeriodic_coord hVper i z j
    have h3 : dvec (0, ee i) (quad W) (z.1, z.2 + ee j) = dvec (0, ee i) (quad W) z :=
      spacePeriodic_dvec hqd hqper (0, ee i) z j
    show quad W (z.1, z.2 + ee j) * V (z.1, z.2 + ee j) i
        - nu * dvec (0, ee i) (quad W) (z.1, z.2 + ee j)
      = quad W z * V z i - nu * dvec (0, ee i) (quad W) z
    rw [h1, h2, h3]
  have hdivzero : cellInt (fun x => ∑ i, dvec (0, ee i) (quadFlux nu V W i) (t, x)) = 0 :=
    cellInt_dvec_divergence_eq_zero (quadFlux nu V W) hfluxSmooth hfluxPer t
  -- the source is determined by the transport equation, hence continuous
  set Sx : Fin 3 → STime → ℝ := fun a w =>
    dvec (1, 0) (W a) w + (∑ j, V w j * dvec (0, ee j) (W a) w)
      - nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (W a)) w with hSx
  have hSeq : ∀ (a : Fin 3) (x : E3), S a (t, x) = Sx a (t, x) := by
    intro a x
    have h := heq a x
    simp only [hSx]
    linarith
  have hVcont : ∀ j : Fin 3, Continuous (fun w : STime => V w j) := fun j =>
    (contDiff_coord V hV j).continuous
  have hSxCont : ∀ a, Continuous (Sx a) := by
    intro a
    have h1 : Continuous (dvec (1, 0) (W a)) := continuous_dvec (W a) (hW a) (1, 0)
    have h2 : Continuous (fun w : STime => ∑ j, V w j * dvec (0, ee j) (W a) w) :=
      continuous_finset_sum _ fun j _ =>
        (hVcont j).mul (continuous_dvec (W a) (hW a) (0, ee j))
    have h3 : Continuous (fun w : STime => nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (W a)) w) :=
      continuous_const.mul (continuous_finset_sum _ fun k _ =>
        continuous_dvec _ (contDiff_dvec (W a) (hW a) (0, ee k)) (0, ee k))
    exact (h1.add h2).sub h3
  -- the three continuous integrands
  have hAcont : Continuous (fun x : E3 => ∑ a, W a (t, x) * Sx a (t, x)) :=
    continuous_finset_sum _ fun a _ =>
      (continuous_time_slice (hW a).continuous t).mul (continuous_time_slice (hSxCont a) t)
  have hgradSqCont : Continuous (fun x : E3 => gradSq W (t, x)) := by
    refine continuous_time_slice (f := fun w => gradSq W w) ?_ t
    exact continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun a _ =>
      (continuous_dvec (W a) (hW a) (0, ee k)).mul (continuous_dvec (W a) (hW a) (0, ee k))
  have hBcont : Continuous (fun x : E3 => nu * gradSq W (t, x)) := continuous_const.mul hgradSqCont
  have hCcont : Continuous (fun x : E3 => ∑ i, dvec (0, ee i) (quadFlux nu V W i) (t, x)) := by
    refine continuous_time_slice (f := fun w => ∑ i, dvec (0, ee i) (quadFlux nu V W i) w) ?_ t
    exact continuous_finset_sum _ fun i _ =>
      continuous_dvec _ (hfluxSmooth i) (0, ee i)
  -- the pointwise identity
  have hpt : ∀ x : E3, dvec (1, 0) (quad W) (t, x)
      = ((∑ a, W a (t, x) * Sx a (t, x)) - nu * gradSq W (t, x))
        - ∑ i, dvec (0, ee i) (quadFlux nu V W i) (t, x) := by
    intro x
    have hid := transported_quadratic_identity_at nu V W S hW (t, x) (fun a => heq a x)
    have hflux := quadFlux_divergence_at nu V W hV hW (t, x) (hdiv x)
    have hS : ∀ a : Fin 3, S a (t, x) = Sx a (t, x) := fun a => hSeq a x
    simp only [hS] at hid
    rw [hflux]
    simp only [gradSq] at *
    linear_combination hid
  -- integrate
  have hcell : cellInt (fun x => dvec (1, 0) (quad W) (t, x))
      = cellInt (fun x => ∑ a, W a (t, x) * S a (t, x))
        - nu * cellInt (fun x => gradSq W (t, x)) := by
    have h0 : cellInt (fun x => dvec (1, 0) (quad W) (t, x))
        = cellInt (fun x => ((∑ a, W a (t, x) * Sx a (t, x)) - nu * gradSq W (t, x))
            - ∑ i, dvec (0, ee i) (quadFlux nu V W i) (t, x)) := cellInt_congr hpt
    rw [h0, cellInt_sub (hAcont.sub hBcont) hCcont, hdivzero, sub_zero,
      cellInt_sub hAcont hBcont, cellInt_const_mul]
    congr 1
    exact cellInt_congr fun x => Finset.sum_congr rfl fun a _ => by rw [hSeq a x]
  have hderiv := hasDerivAt_cellInt (quad W) hq t
  rwa [hcell] at hderiv

/-- **Global balance for a transported quadratic density**, with the transport
equation and incompressibility assumed at every spacetime point. -/
theorem global_quadratic_balance (nu : ℝ) (V : STime → E3) (W S : Fin 3 → STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVper : SpacePeriodic V)
    (hdiv : ∀ w : STime, divg V w = 0)
    (hW : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (W a)) (hWper : ∀ a, SpacePeriodic (W a))
    (heq : ∀ (a : Fin 3) (z : STime),
      dvec (1, 0) (W a) z + ∑ j, V z j * dvec (0, ee j) (W a) z
        = S a z + nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (W a)) z)
    (t : ℝ) :
    HasDerivAt (fun s => cellInt (fun x => quad W (s, x)))
      (cellInt (fun x => ∑ a, W a (t, x) * S a (t, x))
        - nu * cellInt (fun x => gradSq W (t, x))) t :=
  global_quadratic_balance_at nu V W S hV hVper hW hWper t (fun x => hdiv (t, x))
    (fun a x => heq a (t, x))

/-! ## The energy balance -/

/-- **The pressure work integrates to zero on the torus.**  For a smooth
periodic divergence-free field `u` and a smooth periodic scalar `p`,
`∫_cell ∑_a u_a ∂_a p = 0`, because `u·∇p = div (p u)`. -/
theorem cellInt_pressure_work_eq_zero_at (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P) (t : ℝ)
    (hdiv : ∀ x : E3, divg V (t, x) = 0) :
    cellInt (fun x => ∑ a, V (t, x) a * dvec (0, ee a) P (t, x)) = 0 := by
  have hG : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => P w * V w i) :=
    fun i => hP.mul (contDiff_coord V hV i)
  have hGper : ∀ i : Fin 3, SpacePeriodic (fun w => P w * V w i) := by
    intro i z j
    have h1 : P (z.1, z.2 + ee j) = P z := hPper z j
    have h2 : V (z.1, z.2 + ee j) i = V z i := spacePeriodic_coord hVper i z j
    show P (z.1, z.2 + ee j) * V (z.1, z.2 + ee j) i = P z * V z i
    rw [h1, h2]
  have hzero := cellInt_dvec_divergence_eq_zero (fun i w => P w * V w i) hG hGper t
  have hpt : ∀ x : E3, (∑ a, V (t, x) a * dvec (0, ee a) P (t, x))
      = ∑ i, dvec (0, ee i) (fun w => P w * V w i) (t, x) := by
    intro x
    have h1 := pressure_work_divergence_at V P hV hP (t, x) (hdiv x)
    have h2 := divg_eq_sum (fun w => P w • V w) (hP.smul hV) (t, x)
    have h3 : ∀ i : Fin 3, (fun w : STime => (P w • V w) i) = fun w => P w * V w i := by
      intro i; funext w; simp
    simp only [h3] at h2
    rw [← h2, h1]
  rw [cellInt_congr hpt]
  exact hzero

/-- The vanishing of the cell pressure work, with incompressibility assumed at
every point. -/
theorem cellInt_pressure_work_eq_zero (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P)
    (hdiv : ∀ w : STime, divg V w = 0) (t : ℝ) :
    cellInt (fun x => ∑ a, V (t, x) a * dvec (0, ee a) P (t, x)) = 0 :=
  cellInt_pressure_work_eq_zero_at V P hV hP hVper hPper t (fun x => hdiv (t, x))

/-- **Global energy identity on the torus.**  For every smooth periodic
divergence-free solution of the momentum equation,
`d/dt ∫_cell ½|u|² = - ν ∫_cell |∇u|²`. -/
theorem energy_balance (nu : ℝ) (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P)
    (hdiv : ∀ w : STime, divg V w = 0)
    (hmom : ∀ w : STime, dtime V w + adv V w = - grad P w + nu • lap V w)
    (t : ℝ) :
    HasDerivAt (energy V)
      (- (nu * cellInt (fun x => gradSq (fun a w => V w a) (t, x)))) t := by
  have hW : ∀ a : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V w a) := fun a => contDiff_coord V hV a
  have hWper : ∀ a : Fin 3, SpacePeriodic (fun w => V w a) :=
    fun a => spacePeriodic_coord hVper a
  have heq : ∀ (a : Fin 3) (z : STime),
      dvec (1, 0) (fun w => V w a) z + ∑ j, V z j * dvec (0, ee j) (fun w => V w a) z
        = (fun (a : Fin 3) (z : STime) => - dvec (0, ee a) P z) a z
          + nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) z :=
    fun a z => congrFun (momentum_component nu V P hV hmom a) z
  have hbal := global_quadratic_balance nu V (fun a w => V w a)
    (fun a w => - dvec (0, ee a) P w) hV hVper hdiv hW hWper heq t
  -- the pressure work is a spatial divergence, so it integrates to zero
  have hzero := cellInt_pressure_work_eq_zero V P hV hP hVper hPper hdiv t
  have hpt : ∀ x : E3, (∑ a, V (t, x) a * (- dvec (0, ee a) P (t, x)))
      = - ∑ a, V (t, x) a * dvec (0, ee a) P (t, x) := by
    intro x
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hsrc : cellInt (fun x => ∑ a, V (t, x) a * (- dvec (0, ee a) P (t, x))) = 0 := by
    rw [cellInt_congr hpt, cellInt_neg, hzero, neg_zero]
  rw [hsrc, zero_sub] at hbal
  exact hbal

/-- **The a priori energy inequality.**  For nonnegative viscosity the cell
energy of a smooth periodic solution is nonincreasing. -/
theorem energy_antitone (nu : ℝ) (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P)
    (hnu : 0 ≤ nu)
    (hdiv : ∀ w : STime, divg V w = 0)
    (hmom : ∀ w : STime, dtime V w + adv V w = - grad P w + nu • lap V w) :
    Antitone (energy V) := by
  have hderiv : ∀ t : ℝ, HasDerivAt (energy V)
      (- (nu * cellInt (fun x => gradSq (fun a w => V w a) (t, x)))) t :=
    fun t => energy_balance nu V P hV hP hVper hPper hdiv hmom t
  refine antitone_of_deriv_nonpos (fun t => (hderiv t).differentiableAt) fun t => ?_
  rw [(hderiv t).deriv]
  have hnonneg : 0 ≤ cellInt (fun x => gradSq (fun a w => V w a) (t, x)) :=
    cellInt_nonneg fun x => gradSq_nonneg _ _
  have : 0 ≤ nu * cellInt (fun x => gradSq (fun a w => V w a) (t, x)) :=
    mul_nonneg hnu hnonneg
  linarith

/-- The energy at any later time is bounded by the initial energy. -/
theorem energy_le_initial (nu : ℝ) (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P)
    (hnu : 0 ≤ nu)
    (hdiv : ∀ w : STime, divg V w = 0)
    (hmom : ∀ w : STime, dtime V w + adv V w = - grad P w + nu • lap V w)
    {t : ℝ} (ht : 0 ≤ t) :
    energy V t ≤ energy V 0 :=
  energy_antitone nu V P hV hP hVper hPper hnu hdiv hmom ht

/-! ## The integrated (Leray) energy equality -/

lemma continuous_gradSq (W : Fin 3 → STime → ℝ) (hW : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (W a)) :
    Continuous (fun w => gradSq W w) :=
  continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun a _ =>
    (continuous_dvec (W a) (hW a) (0, ee k)).mul (continuous_dvec (W a) (hW a) (0, ee k))

lemma continuous_cellInt_gradSq (W : Fin 3 → STime → ℝ)
    (hW : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (W a)) :
    Continuous (fun t => cellInt (fun x => gradSq W (t, x))) :=
  continuous_cellInt (fun w => gradSq W w) (continuous_gradSq W hW)

/-- **Integrated energy equality on the torus.**  For every smooth periodic
divergence-free solution and every time `T`,
`∫_cell ½|u(T)|² + ν ∫₀ᵀ ∫_cell |∇u|² = ∫_cell ½|u(0)|²`.
This is the a priori bound on the total dissipation. -/
theorem energy_dissipation_integral (nu : ℝ) (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P)
    (hdiv : ∀ w : STime, divg V w = 0)
    (hmom : ∀ w : STime, dtime V w + adv V w = - grad P w + nu • lap V w)
    (T : ℝ) :
    energy V T
        + nu * ∫ t in (0 : ℝ)..T, cellInt (fun x => gradSq (fun a w => V w a) (t, x))
      = energy V 0 := by
  have hW : ∀ a : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V w a) := fun a => contDiff_coord V hV a
  have hDcont : Continuous (fun t => cellInt (fun x => gradSq (fun a w => V w a) (t, x))) :=
    continuous_cellInt_gradSq _ hW
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T, HasDerivAt (energy V)
      (- (nu * cellInt (fun x => gradSq (fun a w => V w a) (t, x)))) t :=
    fun t _ => energy_balance nu V P hV hP hVper hPper hdiv hmom t
  have hint : IntervalIntegrable
      (fun t => - (nu * cellInt (fun x => gradSq (fun a w => V w a) (t, x))))
      volume 0 T := ((continuous_const.mul hDcont).neg).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at h
  linarith

/-! ## Conservation of the mean velocity -/

/-- The cell mean of the `a`-th velocity component. -/
def meanVel (V : STime → E3) (a : Fin 3) (t : ℝ) : ℝ := cellInt (fun x => V (t, x) a)

/-- **The mean velocity is conserved.**  Every term of the momentum equation is
a spatial divergence of a periodic field, so the cell mean of each velocity
component has vanishing time derivative. -/
theorem hasDerivAt_meanVel (nu : ℝ) (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P)
    (hdiv : ∀ w : STime, divg V w = 0)
    (hmom : ∀ w : STime, dtime V w + adv V w = - grad P w + nu • lap V w)
    (a : Fin 3) (t : ℝ) :
    HasDerivAt (meanVel V a) 0 t := by
  have hVc : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V w i) := fun i => contDiff_coord V hV i
  have hVd : ∀ i : Fin 3, Differentiable ℝ (fun w => V w i) := fun i =>
    differentiable_of_contDiffTop (hVc i)
  -- the advective flux `u_j u_a` and the viscous flux `∂_k u_a` are periodic and smooth
  have hAper : ∀ j : Fin 3, SpacePeriodic (fun w => V w j * V w a) := by
    intro j z i
    have h1 : V (z.1, z.2 + ee i) j = V z j := spacePeriodic_coord hVper j z i
    have h2 : V (z.1, z.2 + ee i) a = V z a := spacePeriodic_coord hVper a z i
    show V (z.1, z.2 + ee i) j * V (z.1, z.2 + ee i) a = V z j * V z a
    rw [h1, h2]
  have hA0 := cellInt_dvec_divergence_eq_zero (fun j w => V w j * V w a)
    (fun j => (hVc j).mul (hVc a)) hAper t
  have hC0 := cellInt_dvec_divergence_eq_zero (fun k => dvec (0, ee k) (fun w => V w a))
    (fun k => contDiff_dvec _ (hVc a) (0, ee k))
    (fun k => spacePeriodic_dvec (hVd a) (spacePeriodic_coord hVper a) (0, ee k)) t
  have hB0 := cellInt_dvec_eq_zero P hP hPper a t
  -- the pointwise identity: ∂_t u_a is a spatial divergence
  have hpt : ∀ x : E3, dvec (1, 0) (fun w => V w a) (t, x)
      = (-(∑ j, dvec (0, ee j) (fun w => V w j * V w a) (t, x))
            - dvec (0, ee a) P (t, x))
        + nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) (t, x) := by
    intro x
    have hmomc := congrFun (momentum_component nu V P hV hmom a) (t, x)
    have hterm : ∀ j : Fin 3, dvec (0, ee j) (fun w => V w j * V w a) (t, x)
        = dvec (0, ee j) (fun w => V w j) (t, x) * V (t, x) a
          + V (t, x) j * dvec (0, ee j) (fun w => V w a) (t, x) :=
      fun j => dvec_mul _ _ _ ((hVd j) _) ((hVd a) _) (0, ee j)
    have hd0 : ∑ j, dvec (0, ee j) (fun w => V w j) (t, x) * V (t, x) a = 0 := by
      rw [← Finset.sum_mul]
      have h := hdiv (t, x)
      rw [divg_eq_sum V hV (t, x)] at h
      rw [h, zero_mul]
    have hadv : ∑ j, dvec (0, ee j) (fun w => V w j * V w a) (t, x)
        = ∑ j, V (t, x) j * dvec (0, ee j) (fun w => V w a) (t, x) := by
      rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, hd0, zero_add]
    rw [hadv]
    linarith [hmomc]
  -- continuity of the three integrands
  have hcA : Continuous (fun x : E3 => ∑ j, dvec (0, ee j) (fun w => V w j * V w a) (t, x)) := by
    refine continuous_time_slice
      (f := fun w => ∑ j, dvec (0, ee j) (fun y => V y j * V y a) w) ?_ t
    exact continuous_finset_sum _ fun j _ => continuous_dvec _ ((hVc j).mul (hVc a)) (0, ee j)
  have hcB : Continuous (fun x : E3 => dvec (0, ee a) P (t, x)) :=
    continuous_time_slice (continuous_dvec P hP (0, ee a)) t
  have hcC : Continuous
      (fun x : E3 => ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) (t, x)) := by
    refine continuous_time_slice
      (f := fun w => ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun y => V y a)) w) ?_ t
    exact continuous_finset_sum _ fun k _ =>
      continuous_dvec _ (contDiff_dvec _ (hVc a) (0, ee k)) (0, ee k)
  have e1 : cellInt (fun x =>
        (-(∑ j, dvec (0, ee j) (fun w => V w j * V w a) (t, x)) - dvec (0, ee a) P (t, x))
          + nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) (t, x))
      = cellInt (fun x =>
          -(∑ j, dvec (0, ee j) (fun w => V w j * V w a) (t, x)) - dvec (0, ee a) P (t, x))
        + cellInt (fun x =>
            nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) (t, x)) :=
    cellInt_add (hcA.neg.sub hcB) (continuous_const.mul hcC)
  have e2 : cellInt (fun x =>
        -(∑ j, dvec (0, ee j) (fun w => V w j * V w a) (t, x)) - dvec (0, ee a) P (t, x))
      = cellInt (fun x => -(∑ j, dvec (0, ee j) (fun w => V w j * V w a) (t, x)))
        - cellInt (fun x => dvec (0, ee a) P (t, x)) :=
    cellInt_sub hcA.neg hcB
  have e3 : cellInt (fun x => -(∑ j, dvec (0, ee j) (fun w => V w j * V w a) (t, x)))
      = - cellInt (fun x => ∑ j, dvec (0, ee j) (fun w => V w j * V w a) (t, x)) :=
    cellInt_neg _
  have e4 : cellInt (fun x => nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) (t, x))
      = nu * cellInt (fun x => ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) (t, x)) :=
    cellInt_const_mul _ _
  have hcell : cellInt (fun x => dvec (1, 0) (fun w => V w a) (t, x)) = 0 := by
    rw [cellInt_congr hpt, e1, e2, e3, e4, hA0, hB0, hC0]
    ring
  have hderiv := hasDerivAt_cellInt (fun w => V w a) (hVc a) t
  rw [hcell] at hderiv
  exact hderiv

/-- The cell mean of the velocity is constant in time. -/
theorem meanVel_const (nu : ℝ) (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P)
    (hdiv : ∀ w : STime, divg V w = 0)
    (hmom : ∀ w : STime, dtime V w + adv V w = - grad P w + nu • lap V w)
    (a : Fin 3) (s t : ℝ) :
    meanVel V a s = meanVel V a t := by
  have hderiv : ∀ r : ℝ, HasDerivAt (meanVel V a) 0 r :=
    fun r => hasDerivAt_meanVel nu V P hV hP hVper hPper hdiv hmom a r
  exact is_const_of_deriv_eq_zero (fun r => (hderiv r).differentiableAt)
    (fun r => (hderiv r).deriv) s t

/-! ## The enstrophy balance -/

/-- **Global enstrophy balance on the torus.**  For every smooth periodic
divergence-free solution, with `ω = curl u`,
`d/dt ∫_cell ½|ω|² = ∫_cell ω·(ω·∇)u - ν ∫_cell |∇ω|²`.

The first term is the global vortex-stretching production; controlling it is
exactly the obstruction to global regularity. -/
theorem enstrophy_balance (nu : ℝ) (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V)
    (hdiv : ∀ w : STime, divg V w = 0)
    (hmom : ∀ w : STime, dtime V w + adv V w = - grad P w + nu • lap V w)
    (t : ℝ) :
    HasDerivAt (enstrophy V)
      (cellInt (fun x => ∑ a, vortComp V a (t, x)
            * ∑ j, vortComp V j (t, x) * dvec (0, ee j) (fun w => V w a) (t, x))
        - nu * cellInt (fun x => gradSq (vortComp V) (t, x))) t := by
  have hW : ∀ a : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (vortComp V a) :=
    fun a => contDiff_vortComp V hV a
  have hWper : ∀ a : Fin 3, SpacePeriodic (vortComp V a) := by
    intro a z j
    have h1 : dvec (0, ee (a + 1)) (fun w => V w (a + 2)) (z.1, z.2 + ee j)
        = dvec (0, ee (a + 1)) (fun w => V w (a + 2)) z :=
      spacePeriodic_dvec (differentiable_of_contDiffTop (contDiff_coord V hV (a + 2)))
        (spacePeriodic_coord hVper (a + 2)) (0, ee (a + 1)) z j
    have h2 : dvec (0, ee (a + 2)) (fun w => V w (a + 1)) (z.1, z.2 + ee j)
        = dvec (0, ee (a + 2)) (fun w => V w (a + 1)) z :=
      spacePeriodic_dvec (differentiable_of_contDiffTop (contDiff_coord V hV (a + 1)))
        (spacePeriodic_coord hVper (a + 1)) (0, ee (a + 2)) z j
    show dvec (0, ee (a + 1)) (fun w => V w (a + 2)) (z.1, z.2 + ee j)
        - dvec (0, ee (a + 2)) (fun w => V w (a + 1)) (z.1, z.2 + ee j)
      = dvec (0, ee (a + 1)) (fun w => V w (a + 2)) z
        - dvec (0, ee (a + 2)) (fun w => V w (a + 1)) z
    rw [h1, h2]
  exact global_quadratic_balance nu V (vortComp V)
    (fun a w => ∑ j, vortComp V j w * dvec (0, ee j) (fun y => V y a) w)
    hV hVper hdiv hW hWper
    (fun a z => vorticity_component nu V P hV hP hdiv hmom a z) t

end ClayNS
