/-
# Local energy and enstrophy identities, derived

The whole Clay Navier–Stokes ladder rests on the energy identity: the a priori
bound that makes Leray–Hopf theory, the Galerkin scheme and every absorption
argument possible.  Its vorticity analogue, the enstrophy identity, carries the
vortex-stretching *production* term that the nine-owner absorption arguments of
the Agda development are about.  In that development the energy and enstrophy
budgets appear only as record data and `ℚ`-valued bookkeeping; they are never
derived from the equations.

Here both are derived, pointwise, from one general lemma: if a triple of scalar
fields `W = (W₀,W₁,W₂)` is transported by `u` with source `S` and viscosity `ν`,

  ∂_t W_a + (u·∇)W_a = S_a + ν ΔW_a   for every `a`,

then the quadratic density `q = ½|W|²` satisfies

  ∂_t q + (u·∇)q = W·S + ν ( Δq - ∑_{a,k} (∂_k W_a)² ).

Applying it to `W = u` with `S = -∇p` gives the local energy identity, and to
`W = ω` with `S = (ω·∇)u` — the vorticity transport equation of
`RequestProject/NavierStokes/Vorticity.lean` — gives the local enstrophy
identity, whose source term is exactly the vortex-stretching production.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.Vorticity

open scoped BigOperators

noncomputable section

namespace ClayNS

/-! ## A quadratic density and its derivatives -/

/-- The quadratic density `½|W|²` of a triple of scalar fields. -/
def quad (W : Fin 3 → STime → ℝ) : STime → ℝ := fun z => (1 / 2 : ℝ) * ∑ a, W a z * W a z

/-- Kinetic energy density `e = ½|u|²`. -/
def kin (V : STime → E3) : STime → ℝ := quad (fun a w => V w a)

/-- Enstrophy density `½|ω|²`. -/
def ens (V : STime → E3) : STime → ℝ := quad (vortComp V)

lemma contDiff_quad (W : Fin 3 → STime → ℝ) (hW : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (W a)) :
    ContDiff ℝ (⊤ : ℕ∞) (quad W) :=
  contDiff_const.mul (ContDiff.sum fun a _ => (hW a).mul (hW a))

/-- `∂_c (½|W|²) = ∑_a W_a ∂_c W_a`. -/
lemma dvec_quad (W : Fin 3 → STime → ℝ) (hW : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (W a))
    (c : STime) (z : STime) :
    dvec c (quad W) z = ∑ a, W a z * dvec c (W a) z := by
  have hsq : ∀ a : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => W a w * W a w) :=
    fun a => (hW a).mul (hW a)
  have hsum : Differentiable ℝ (fun w => ∑ a, W a w * W a w) :=
    differentiable_of_contDiffTop (ContDiff.sum fun a _ => hsq a)
  have h1 : dvec c (quad W) z = (1 / 2 : ℝ) * dvec c (fun w => ∑ a, W a w * W a w) z := by
    have h := dvec_cmul (1 / 2 : ℝ) (fun w => ∑ a, W a w * W a w) z (hsum z) c
    simp only [smul_eq_mul] at h
    exact h
  have h2 : dvec c (fun w => ∑ a, W a w * W a w) z
      = ∑ a, dvec c (fun w => W a w * W a w) z :=
    dvec_sum Finset.univ (fun a w => W a w * W a w) z
      (fun a _ => (differentiable_of_contDiffTop (hsq a)) z) c
  have h3 : ∀ a : Fin 3, dvec c (fun w => W a w * W a w) z
      = 2 * (W a z * dvec c (W a) z) := by
    intro a
    rw [dvec_mul (W a) (W a) z
      ((differentiable_of_contDiffTop (hW a)) z) ((differentiable_of_contDiffTop (hW a)) z) c]
    ring
  rw [h1, h2, Finset.sum_congr rfl (fun a _ => h3 a), ← Finset.mul_sum]
  ring

/-- `Δ(½|W|²) = ∑_{k,a} ((∂_k W_a)² + W_a ∂_k∂_k W_a)`. -/
lemma lap_quad (W : Fin 3 → STime → ℝ) (hW : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (W a)) (z : STime) :
    lap (quad W) z
      = ∑ k, ∑ a, (dvec (0, ee k) (W a) z * dvec (0, ee k) (W a) z
          + W a z * dvec (0, ee k) (dvec (0, ee k) (W a)) z) := by
  have hstep : ∀ k : Fin 3, dvec (0, ee k) (dvec (0, ee k) (quad W)) z
      = ∑ a, (dvec (0, ee k) (W a) z * dvec (0, ee k) (W a) z
          + W a z * dvec (0, ee k) (dvec (0, ee k) (W a)) z) := by
    intro k
    have hfun : dvec (0, ee k) (quad W)
        = fun w => ∑ a, W a w * dvec (0, ee k) (W a) w :=
      funext fun w => dvec_quad W hW (0, ee k) w
    rw [hfun]
    have hprod : ∀ a : Fin 3,
        ContDiff ℝ (⊤ : ℕ∞) (fun w => W a w * dvec (0, ee k) (W a) w) :=
      fun a => (hW a).mul (contDiff_dvec _ (hW a) _)
    rw [dvec_sum Finset.univ (fun a w => W a w * dvec (0, ee k) (W a) w) z
      (fun a _ => (differentiable_of_contDiffTop (hprod a)) z) (0, ee k)]
    exact Finset.sum_congr rfl fun a _ =>
      dvec_mul (W a) (dvec (0, ee k) (W a)) z
        ((differentiable_of_contDiffTop (hW a)) z)
        ((differentiable_of_contDiffTop (contDiff_dvec _ (hW a) _)) z) (0, ee k)
  exact Finset.sum_congr rfl fun k _ => hstep k

/-! ## The general transported-quadratic identity -/

/-- **Transported quadratic identity.**  If each component of `W` is transported
by `u` with source `S` and viscosity `ν`, then `q = ½|W|²` satisfies

`∂_t q + (u·∇)q = W·S + ν (Δq - ∑_{a,k}(∂_k W_a)²)`. -/
theorem transported_quadratic_identity_at (nu : ℝ) (V : STime → E3)
    (W S : Fin 3 → STime → ℝ) (hW : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (W a)) (z : STime)
    (heq : ∀ a : Fin 3,
      dvec (1, 0) (W a) z + ∑ j, V z j * dvec (0, ee j) (W a) z
        = S a z + nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (W a)) z) :
    dvec (1, 0) (quad W) z + ∑ j, V z j * dvec (0, ee j) (quad W) z
      = (∑ a, W a z * S a z)
        + nu * (lap (quad W) z
            - ∑ k, ∑ a, dvec (0, ee k) (W a) z * dvec (0, ee k) (W a) z) := by
  have hcontract : ∑ a, W a z * (dvec (1, 0) (W a) z
        + ∑ j, V z j * dvec (0, ee j) (W a) z)
      = ∑ a, W a z * (S a z
        + nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (W a)) z) :=
    Finset.sum_congr rfl fun a _ => congrArg (fun t => W a z * t) (heq a)
  -- left-hand side
  have hL : ∑ a, W a z * (dvec (1, 0) (W a) z
        + ∑ j, V z j * dvec (0, ee j) (W a) z)
      = dvec (1, 0) (quad W) z + ∑ j, V z j * dvec (0, ee j) (quad W) z := by
    have hsplit : ∀ a ∈ (Finset.univ : Finset (Fin 3)),
        W a z * (dvec (1, 0) (W a) z + ∑ j, V z j * dvec (0, ee j) (W a) z)
          = W a z * dvec (1, 0) (W a) z
            + ∑ j, V z j * (W a z * dvec (0, ee j) (W a) z) := by
      intro a _
      rw [mul_add, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← dvec_quad W hW (1, 0) z]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, ← dvec_quad W hW (0, ee j) z]
  -- right-hand side
  have hR : ∑ a, W a z * (S a z
        + nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (W a)) z)
      = (∑ a, W a z * S a z)
        + nu * (lap (quad W) z
            - ∑ k, ∑ a, dvec (0, ee k) (W a) z * dvec (0, ee k) (W a) z) := by
    have hsplit : ∀ a ∈ (Finset.univ : Finset (Fin 3)),
        W a z * (S a z + nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (W a)) z)
          = W a z * S a z
            + nu * ∑ k, W a z * dvec (0, ee k) (dvec (0, ee k) (W a)) z := by
      intro a _
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    rw [lap_quad W hW z, ← Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [← hL, ← hR]
  exact hcontract

/-- **Transported quadratic identity**, global form: the transport equation is
assumed at every spacetime point. -/
theorem transported_quadratic_identity (nu : ℝ) (V : STime → E3)
    (W S : Fin 3 → STime → ℝ) (hW : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (W a))
    (heq : ∀ (a : Fin 3) (z : STime),
      dvec (1, 0) (W a) z + ∑ j, V z j * dvec (0, ee j) (W a) z
        = S a z + nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (W a)) z)
    (z : STime) :
    dvec (1, 0) (quad W) z + ∑ j, V z j * dvec (0, ee j) (quad W) z
      = (∑ a, W a z * S a z)
        + nu * (lap (quad W) z
            - ∑ k, ∑ a, dvec (0, ee k) (W a) z * dvec (0, ee k) (W a) z) :=
  transported_quadratic_identity_at nu V W S hW z (fun a => heq a z)

/-! ## The local energy identity -/

/-- **Local energy identity.**  For any smooth solution of the momentum
equation, with `e = ½|u|²`,

`∂_t e + (u·∇)e = - u·∇p + ν (Δe - ∑_{a,j}(∂_j u_a)²)`.

No incompressibility hypothesis is required. -/
theorem local_energy_identity (nu : ℝ) (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hmom : ∀ w : STime, dtime V w + adv V w = - grad P w + nu • lap V w)
    (z : STime) :
    dvec (1, 0) (kin V) z + ∑ j, V z j * dvec (0, ee j) (kin V) z
      = - (∑ a, V z a * dvec (0, ee a) P z)
        + nu * (lap (kin V) z
            - ∑ k, ∑ a, dvec (0, ee k) (fun w => V w a) z
                * dvec (0, ee k) (fun w => V w a) z) := by
  have hgen := transported_quadratic_identity nu V (fun a w => V w a)
    (fun a z => - dvec (0, ee a) P z) (fun a => contDiff_coord V hV a)
    (fun a z => congrFun (momentum_component nu V P hV hmom a) z) z
  rw [kin]
  rw [hgen]
  congr 1
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- With incompressibility the pressure work is a pure divergence,
`u·∇p = div (p u)`.  This is what makes it vanish after integration over the
torus, leaving the dissipation `-ν ∫ |∇u|²`. -/
theorem pressure_work_divergence_at (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P) (z : STime)
    (hdiv : divg V z = 0) :
    divg (fun w => P w • V w) z = ∑ a, V z a * dvec (0, ee a) P z := by
  have hu : ∀ a : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V w a) := fun a => contDiff_coord V hV a
  have hPV : ContDiff ℝ (⊤ : ℕ∞) (fun w => P w • V w) := hP.smul hV
  have hcoord : ∀ a : Fin 3, (fun w => (P w • V w) a) = fun w => P w * V w a := by
    intro a; funext w; simp
  have hstep : ∀ a : Fin 3, dvec (0, ee a) (fun w => (P w • V w) a) z
      = dvec (0, ee a) P z * V z a + P z * dvec (0, ee a) (fun w => V w a) z := by
    intro a
    rw [hcoord a]
    exact dvec_mul P (fun w => V w a) z
      ((differentiable_of_contDiffTop hP) z) ((differentiable_of_contDiffTop (hu a)) z) (0, ee a)
  have hdivsum : divg (fun w => P w • V w) z
      = ∑ a, dvec (0, ee a) (fun w => (P w • V w) a) z := by
    rw [divg_eq_sum (fun w => P w • V w) hPV z]
  have hdivV : ∑ a, dvec (0, ee a) (fun w => V w a) z = 0 := by
    have h := hdiv
    rw [divg_eq_sum V hV z] at h
    exact h
  rw [hdivsum, Finset.sum_congr rfl (fun a _ => hstep a), Finset.sum_add_distrib,
    ← Finset.mul_sum, hdivV, mul_zero, add_zero]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- The pressure-work divergence identity with incompressibility assumed at
every point. -/
theorem pressure_work_divergence (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hdiv : ∀ w : STime, divg V w = 0) (z : STime) :
    divg (fun w => P w • V w) z = ∑ a, V z a * dvec (0, ee a) P z :=
  pressure_work_divergence_at V P hV hP z (hdiv z)

/-! ## The local enstrophy identity -/

/-- **Local enstrophy identity.**  For every smooth divergence-free solution,
with `ω = curl u` and enstrophy density `E = ½|ω|²`,

`∂_t E + (u·∇)E = ω·(ω·∇)u + ν (ΔE - ∑_{a,k}(∂_k ω_a)²)`.

The first term on the right is the vortex-stretching *production*; the last is
the enstrophy dissipation.  This is the pointwise form of the balance that the
Agda development's absorption arguments quantify over rational cell data. -/
theorem local_enstrophy_identity (nu : ℝ) (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hdiv : ∀ w : STime, divg V w = 0)
    (hmom : ∀ w : STime, dtime V w + adv V w = - grad P w + nu • lap V w)
    (z : STime) :
    dvec (1, 0) (ens V) z + ∑ j, V z j * dvec (0, ee j) (ens V) z
      = (∑ a, vortComp V a z
            * ∑ j, vortComp V j z * dvec (0, ee j) (fun w => V w a) z)
        + nu * (lap (ens V) z
            - ∑ k, ∑ a, dvec (0, ee k) (vortComp V a) z
                * dvec (0, ee k) (vortComp V a) z) :=
  transported_quadratic_identity nu V (vortComp V)
    (fun a z => ∑ j, vortComp V j z * dvec (0, ee j) (fun w => V w a) z)
    (fun a => contDiff_vortComp V hV a)
    (fun a z => vorticity_component nu V P hV hP hdiv hmom a z) z

end ClayNS
