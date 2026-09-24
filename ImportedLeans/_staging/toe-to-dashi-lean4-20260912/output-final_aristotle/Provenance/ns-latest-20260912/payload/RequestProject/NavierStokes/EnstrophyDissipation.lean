/-
# Enstrophy is the energy dissipation: `∫_cell |∇u|² = ∫_cell |ω|²`.

On the torus, for a divergence-free field, the Dirichlet energy of the velocity
and the `L²` norm of the vorticity coincide.  This is the identity that turns
the energy balance of `RequestProject/NavierStokes/GlobalEnergy.lean` into a
statement about the enstrophy, and it is what makes the enstrophy the natural
critical quantity of the Clay ladder.

* `ClayNS.vorticity_sq_identity` — the pointwise algebraic identity
  `|ω|² = ∑_{p,q} (∂_p u_q)² − ∑_{p,q} (∂_p u_q)(∂_q u_p)`;
* `ClayNS.cellInt_cross_gradient_eq_zero` — the cross term
  `∑_{p,q} (∂_p u_q)(∂_q u_p)` integrates to zero on the torus when
  `div u = 0`, being the divergence of the advection field;
* `ClayNS.cellInt_gradSq_eq_two_enstrophy` — hence
  `∫_cell |∇u|² = 2 ∫_cell ½|ω|²`;
* `ClayNS.energy_balance_enstrophy` — `d/dt E = −2ν · enstrophy`;
* `ClayNS.energy_enstrophy_integral` — `E(t) + 2ν ∫₀ᵗ enstrophy = E(0)`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.GlobalEnergy

open scoped BigOperators
open MeasureTheory Set

noncomputable section

namespace ClayNS

/-! ## The pointwise algebraic identity -/

/-- With `D p q` standing for `∂_p u_q`, the squared vorticity is the difference
of the Dirichlet density and the "cross" density. -/
lemma vorticity_sq_identity (D : Fin 3 → Fin 3 → ℝ) :
    (∑ i, (D (i + 1) (i + 2) - D (i + 2) (i + 1)) * (D (i + 1) (i + 2) - D (i + 2) (i + 1)))
      = (∑ p, ∑ q, D p q * D p q) - ∑ p, ∑ q, D p q * D q p := by
  simp only [Fin.sum_univ_three, Fin.isValue, Fin.reduceAdd]
  ring

/-- The velocity gradient, written through `dvec`. -/
lemma dspace_eq_dvec_coord (V : STime → E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (p q : Fin 3)
    (z : STime) : dspace V p z q = dvec (0, ee p) (fun w => V w q) z :=
  dvec_coord V z ((differentiable_of_contDiffTop hV) z) (0, ee p) q

lemma vortComp_eq_dvec (V : STime → E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (i : Fin 3) (z : STime) :
    vortComp V i z = dvec (0, ee (i + 1)) (fun w => V w (i + 2)) z
      - dvec (0, ee (i + 2)) (fun w => V w (i + 1)) z := by
  rw [vortComp_eq_dspace V hV i z, dspace_eq_dvec_coord V hV, dspace_eq_dvec_coord V hV]

/-! ## The cross term integrates away -/

/-- **The cross gradient term is a pure divergence.**  For a smooth periodic
divergence-free field, `∫_cell ∑_{p,q} (∂_p u_q)(∂_q u_p) = 0`: the integrand is
the divergence of the advection field `(u·∇)u`. -/
theorem cellInt_cross_gradient_eq_zero (V : STime → E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hVper : SpacePeriodic V) (hdiv : ∀ w : STime, divg V w = 0) (t : ℝ) :
    cellInt (fun x => ∑ p, ∑ q, dvec (0, ee p) (fun w => V w q) (t, x)
      * dvec (0, ee q) (fun w => V w p) (t, x)) = 0 := by
  classical
  have hVc : ∀ q : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V w q) := fun q => contDiff_coord V hV q
  have hVd : ∀ q : Fin 3, Differentiable ℝ (fun w => V w q) := fun q =>
    differentiable_of_contDiffTop (hVc q)
  have hVdvec : ∀ p q : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (dvec (0, ee p) (fun w => V w q)) :=
    fun p q => contDiff_dvec _ (hVc q) (0, ee p)
  -- the advection field, componentwise
  set F : Fin 3 → STime → ℝ :=
    fun i w => ∑ j, V w j * dvec (0, ee j) (fun y => V y i) w with hF
  have hFsmooth : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i) := fun i =>
    ContDiff.sum fun j _ => (hVc j).mul (hVdvec j i)
  have hFper : ∀ i, SpacePeriodic (F i) := by
    intro i z j
    show ∑ k, V (z.1, z.2 + ee j) k * dvec (0, ee k) (fun y => V y i) (z.1, z.2 + ee j)
      = ∑ k, V z k * dvec (0, ee k) (fun y => V y i) z
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : V (z.1, z.2 + ee j) k = V z k := spacePeriodic_coord hVper k z j
    have h2 : dvec (0, ee k) (fun y => V y i) (z.1, z.2 + ee j)
        = dvec (0, ee k) (fun y => V y i) z :=
      spacePeriodic_dvec (hVd i) (spacePeriodic_coord hVper i) (0, ee k) z j
    rw [h1, h2]
  -- the divergence of the velocity vanishes identically, hence so do its derivatives
  have hdivfun : (fun w : STime => ∑ i, dvec (0, ee i) (fun y => V y i) w)
      = fun _ : STime => (0 : ℝ) := by
    funext w
    rw [← divg_eq_sum V hV w, hdiv w]
  have hsecond : ∀ (j : Fin 3) (z : STime),
      (∑ i, dvec (0, ee i) (dvec (0, ee j) (fun y => V y i)) z) = 0 := by
    intro j z
    have hswap : ∀ i : Fin 3, dvec (0, ee i) (dvec (0, ee j) (fun y => V y i)) z
        = dvec (0, ee j) (dvec (0, ee i) (fun y => V y i)) z :=
      fun i => dvec_comm _ (hVc i) (0, ee j) (0, ee i) z
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hswap i),
      ← dvec_sum Finset.univ (fun i => dvec (0, ee i) (fun y => V y i)) z
        (fun i _ => (differentiable_of_contDiffTop (hVdvec i i)) z) (0, ee j), hdivfun]
    simp [dvec]
  -- the pointwise identity
  have hpt : ∀ x : E3, (∑ p, ∑ q, dvec (0, ee p) (fun w => V w q) (t, x)
        * dvec (0, ee q) (fun w => V w p) (t, x))
      = ∑ i, dvec (0, ee i) (F i) (t, x) := by
    intro x
    have hterm : ∀ i : Fin 3, dvec (0, ee i) (F i) (t, x)
        = (∑ j, dvec (0, ee i) (fun w => V w j) (t, x)
              * dvec (0, ee j) (fun w => V w i) (t, x))
          + ∑ j, V (t, x) j * dvec (0, ee i) (dvec (0, ee j) (fun y => V y i)) (t, x) := by
      intro i
      rw [hF, dvec_sum Finset.univ
        (fun j w => V w j * dvec (0, ee j) (fun y => V y i) w) (t, x)
        (fun j _ => ((hVd j) (t, x)).mul ((differentiable_of_contDiffTop (hVdvec j i)) (t, x)))
        (0, ee i), ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact dvec_mul _ _ (t, x) ((hVd j) (t, x))
        ((differentiable_of_contDiffTop (hVdvec j i)) (t, x)) (0, ee i)
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i), Finset.sum_add_distrib]
    have hzero : (∑ i, ∑ j, V (t, x) j
        * dvec (0, ee i) (dvec (0, ee j) (fun y => V y i)) (t, x)) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← Finset.mul_sum, hsecond j (t, x), mul_zero]
    rw [hzero, add_zero]
  rw [cellInt_congr hpt]
  exact cellInt_dvec_divergence_eq_zero F hFsmooth hFper t

/-! ## The identity -/

/-- **Enstrophy is the Dirichlet energy.**  For a smooth periodic
divergence-free field, `∫_cell |∇u|² = 2 ∫_cell ½|ω|²`. -/
theorem cellInt_gradSq_eq_two_enstrophy (V : STime → E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hVper : SpacePeriodic V) (hdiv : ∀ w : STime, divg V w = 0) (t : ℝ) :
    cellInt (fun x => gradSq (fun a w => V w a) (t, x)) = 2 * enstrophy V t := by
  classical
  have hVc : ∀ q : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V w q) := fun q => contDiff_coord V hV q
  have hVdvec : ∀ p q : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (dvec (0, ee p) (fun w => V w q)) :=
    fun p q => contDiff_dvec _ (hVc q) (0, ee p)
  -- continuity of the two pieces
  have hcVort : Continuous (fun x : E3 =>
      ∑ i, vortComp V i (t, x) * vortComp V i (t, x)) :=
    continuous_time_slice (f := fun z : STime => ∑ i, vortComp V i z * vortComp V i z)
      (continuous_finset_sum _ fun i _ =>
        (contDiff_vortComp V hV i).continuous.mul (contDiff_vortComp V hV i).continuous) t
  have hcCross : Continuous (fun x : E3 => ∑ p, ∑ q,
      dvec (0, ee p) (fun w => V w q) (t, x) * dvec (0, ee q) (fun w => V w p) (t, x)) :=
    continuous_time_slice (f := fun z : STime => ∑ p, ∑ q,
      dvec (0, ee p) (fun w => V w q) z * dvec (0, ee q) (fun w => V w p) z)
      (continuous_finset_sum _ fun p _ => continuous_finset_sum _ fun q _ =>
        (hVdvec p q).continuous.mul (hVdvec q p).continuous) t
  -- the pointwise identity
  have hpt : ∀ x : E3, gradSq (fun a w => V w a) (t, x)
      = (∑ i, vortComp V i (t, x) * vortComp V i (t, x))
        + ∑ p, ∑ q, dvec (0, ee p) (fun w => V w q) (t, x)
            * dvec (0, ee q) (fun w => V w p) (t, x) := by
    intro x
    have halg := vorticity_sq_identity
      (fun p q => dvec (0, ee p) (fun w => V w q) (t, x))
    have hvort : ∀ i : Fin 3, vortComp V i (t, x)
        = dvec (0, ee (i + 1)) (fun w => V w (i + 2)) (t, x)
          - dvec (0, ee (i + 2)) (fun w => V w (i + 1)) (t, x) :=
      fun i => vortComp_eq_dvec V hV i (t, x)
    have hgs : gradSq (fun a w => V w a) (t, x)
        = ∑ p, ∑ q, dvec (0, ee p) (fun w => V w q) (t, x)
            * dvec (0, ee p) (fun w => V w q) (t, x) := rfl
    have hvsum : (∑ i, vortComp V i (t, x) * vortComp V i (t, x))
        = ∑ i, (dvec (0, ee (i + 1)) (fun w => V w (i + 2)) (t, x)
              - dvec (0, ee (i + 2)) (fun w => V w (i + 1)) (t, x))
            * (dvec (0, ee (i + 1)) (fun w => V w (i + 2)) (t, x)
              - dvec (0, ee (i + 2)) (fun w => V w (i + 1)) (t, x)) :=
      Finset.sum_congr rfl fun i _ => by rw [hvort i]
    rw [hgs, hvsum]
    linarith [halg]
  -- integrate
  have hsplit : cellInt (fun x => gradSq (fun a w => V w a) (t, x))
      = cellInt (fun x : E3 => ∑ i, vortComp V i (t, x) * vortComp V i (t, x))
        + cellInt (fun x : E3 => ∑ p, ∑ q,
            dvec (0, ee p) (fun w => V w q) (t, x) * dvec (0, ee q) (fun w => V w p) (t, x)) := by
    rw [cellInt_congr hpt]
    exact cellInt_add hcVort hcCross
  have htwo : cellInt (fun x : E3 => ∑ i, vortComp V i (t, x) * vortComp V i (t, x))
      = 2 * enstrophy V t := by
    rw [enstrophy, ← cellInt_const_mul (2 : ℝ) (fun x : E3 => ens V (t, x))]
    exact cellInt_congr fun x => by
      show (∑ i, vortComp V i (t, x) * vortComp V i (t, x))
        = 2 * ((1 / 2 : ℝ) * ∑ i, vortComp V i (t, x) * vortComp V i (t, x))
      ring
  rw [hsplit, htwo, cellInt_cross_gradient_eq_zero V hV hVper hdiv t, add_zero]

/-! ## Consequences for the energy -/

/-- **The energy balance in enstrophy form.**  `d/dt ∫_cell ½|u|² = −2ν ·
enstrophy`. -/
theorem energy_balance_enstrophy (nu : ℝ) (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P)
    (hdiv : ∀ w : STime, divg V w = 0)
    (hmom : ∀ w : STime, dtime V w + adv V w = - grad P w + nu • lap V w)
    (t : ℝ) :
    HasDerivAt (energy V) (-(2 * nu * enstrophy V t)) t := by
  have h := energy_balance nu V P hV hP hVper hPper hdiv hmom t
  rwa [cellInt_gradSq_eq_two_enstrophy V hV hVper hdiv t, ← mul_assoc,
    mul_comm nu (2 : ℝ)] at h

/-- **The integrated energy–enstrophy equality.**  `E(t) + 2ν ∫₀ᵗ enstrophy =
E(0)`. -/
theorem energy_enstrophy_integral (nu : ℝ) (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P)
    (hdiv : ∀ w : STime, divg V w = 0)
    (hmom : ∀ w : STime, dtime V w + adv V w = - grad P w + nu • lap V w)
    (t : ℝ) :
    energy V t + 2 * nu * ∫ s in (0 : ℝ)..t, enstrophy V s = energy V 0 := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) t, HasDerivAt (energy V) (-(2 * nu * enstrophy V s)) s :=
    fun s _ => energy_balance_enstrophy nu V P hV hP hVper hPper hdiv hmom s
  have hcont : Continuous (enstrophy V) := by
    have hq : ContDiff ℝ (⊤ : ℕ∞) (ens V) :=
      contDiff_quad (vortComp V) fun a => contDiff_vortComp V hV a
    exact continuous_cellInt (ens V) hq.continuous
  have hint : IntervalIntegrable (fun s => -(2 * nu * enstrophy V s)) volume 0 t :=
    ((continuous_const.mul hcont).neg).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hpull : (∫ s in (0 : ℝ)..t, -(2 * nu * enstrophy V s))
      = -(2 * nu * ∫ s in (0 : ℝ)..t, enstrophy V s) := by
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
  rw [hpull] at hFTC
  linarith

end ClayNS
