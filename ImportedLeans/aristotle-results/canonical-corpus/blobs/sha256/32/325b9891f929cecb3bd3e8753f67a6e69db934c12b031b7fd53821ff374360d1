/-
# The vorticity transport equation, derived

The Beale–Kato–Majda continuation criterion — one of the target-critical items
of the Clay Navier–Stokes ladder — is a statement about the vorticity
`ω = curl u`.  In the Agda development the vorticity transport equation is
never derived; the continuation step is carried as opaque record data.

This file derives it, honestly, from the momentum equation of
`RequestProject/NavierStokes/ClayPeriodic.lean`:

  ∂_t ω + (u·∇)ω = (ω·∇)u + ν Δω,

for every smooth divergence-free solution.  The vortex-stretching term
`(ω·∇)u` is obtained from the genuine algebraic identity

  ∑_j (∂_a u_j)(∂_j u_b) - (∂_b u_j)(∂_j u_a) = - ∑_j ω_j ∂_j u_i   (a = i+1, b = i+2)

which holds *modulo the incompressibility constraint* `∑_p ∂_p u_p = 0`;
the constraint is used with the explicit multiplier `ω_i`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.PressurePoisson

open scoped BigOperators

noncomputable section

namespace ClayNS

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## Additional calculus for `dvec` -/

lemma dvec_sub (A B : STime → F) (z : STime) (hA : DifferentiableAt ℝ A z)
    (hB : DifferentiableAt ℝ B z) (a : STime) :
    dvec a (fun w => A w - B w) z = dvec a A z - dvec a B z :=
  congrArg (fun L : STime →L[ℝ] F => L a) (hA.hasFDerivAt.sub hB.hasFDerivAt).fderiv

lemma dvec_sub_fun (A B : STime → F) (hA : Differentiable ℝ A) (hB : Differentiable ℝ B)
    (a : STime) : dvec a (fun w => A w - B w) = fun z => dvec a A z - dvec a B z :=
  funext fun z => dvec_sub A B z (hA z) (hB z) a

/-- Product rule. -/
lemma dvec_mul (f g : STime → ℝ) (z : STime) (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) (a : STime) :
    dvec a (fun w => f w * g w) z = dvec a f z * g z + f z * dvec a g z := by
  have h : HasFDerivAt (fun w => f w * g w) (f z • fderiv ℝ g z + g z • fderiv ℝ f z) z :=
    hf.hasFDerivAt.mul hg.hasFDerivAt
  have h2 : dvec a (fun w => f w * g w) z = (f z • fderiv ℝ g z + g z • fderiv ℝ f z) a :=
    congrArg (fun L : STime →L[ℝ] ℝ => L a) h.fderiv
  rw [h2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, dvec]
  ring

lemma dvec_comm_fun (V : STime → F) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (a b : STime) :
    dvec b (dvec a V) = dvec a (dvec b V) :=
  funext fun z => dvec_comm V hV a b z

/-- Coordinate projections pass through a derivative, at the level of functions. -/
lemma dvec_coord_fun (W : STime → E3) (hW : ContDiff ℝ (⊤ : ℕ∞) W) (b : STime) (k : Fin 3) :
    (fun w => (dvec b W w) k) = dvec b (fun w => W w k) :=
  funext fun z => dvec_coord W z (differentiable_of_contDiffTop hW z) b k

/-! ## Vorticity -/

/-- The `i`-th component of the vorticity `ω = curl u`, with cyclic indices
`a = i+1`, `b = i+2` in `Fin 3`. -/
def vortComp (V : STime → E3) (i : Fin 3) : STime → ℝ :=
  fun z => dvec (0, ee (i + 1)) (fun w => V w (i + 2)) z
         - dvec (0, ee (i + 2)) (fun w => V w (i + 1)) z

/-- The vorticity field `ω = curl u`. -/
def curl (V : STime → E3) (z : STime) : E3 := ∑ i, (vortComp V i z) • ee i

lemma curl_apply (V : STime → E3) (z : STime) (i : Fin 3) :
    curl V z i = vortComp V i z := by
  simp [curl, ee, Pi.single_apply]

lemma curl_coord (V : STime → E3) (i : Fin 3) : (fun w => curl V w i) = vortComp V i :=
  funext fun z => curl_apply V z i

lemma vortComp_eq_dspace (V : STime → E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (i : Fin 3) (z : STime) :
    vortComp V i z = dspace V (i + 1) z (i + 2) - dspace V (i + 2) z (i + 1) := by
  have hd := differentiable_of_contDiffTop hV
  rw [vortComp]
  rw [← dvec_coord V z (hd z) (0, ee (i + 1)) (i + 2),
      ← dvec_coord V z (hd z) (0, ee (i + 2)) (i + 1)]
  rfl

lemma contDiff_vortComp (V : STime → E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (vortComp V i) :=
  (contDiff_dvec _ (contDiff_coord V hV _) _).sub (contDiff_dvec _ (contDiff_coord V hV _) _)

lemma contDiff_curl (V : STime → E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w => curl V w) :=
  ContDiff.sum fun i _ => (contDiff_vortComp V hV i).smul contDiff_const

/-! ## The vortex-stretching algebraic identity -/

/-- The purely algebraic identity behind vortex stretching.  `D p q` stands for
`∂_p u_q`; the hypothesis is incompressibility.  The incompressibility
constraint enters with multiplier `ω_i = D (i+1) (i+2) - D (i+2) (i+1)`. -/
lemma stretching_identity (D : Fin 3 → Fin 3 → ℝ) (h : D 0 0 + D 1 1 + D 2 2 = 0) (i : Fin 3) :
    ∑ j, (D (i + 1) j * D j (i + 2) - D (i + 2) j * D j (i + 1))
      = - ∑ j, (D (j + 1) (j + 2) - D (j + 2) (j + 1)) * D j i := by
  fin_cases i
  · simp only [Fin.sum_univ_three, Fin.zero_eta, Fin.isValue, Fin.reduceAdd]
    linear_combination (D 1 2 - D 2 1) * h
  · simp only [Fin.sum_univ_three, Fin.mk_one, Fin.isValue, Fin.reduceAdd]
    linear_combination (D 2 0 - D 0 2) * h
  · simp only [Fin.sum_univ_three, Fin.reduceFinMk, Fin.isValue, Fin.reduceAdd]
    linear_combination (D 0 1 - D 1 0) * h

/-! ## The momentum equation in components -/

/-- The momentum equation, read off in the `a`-th coordinate **at a single
spacetime point**.  Only the equation at that point is needed; this is what
makes the finite-window Cauchy theory usable. -/
lemma momentum_component_at (nu : ℝ) (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (a : Fin 3) (z : STime)
    (hmom : dtime V z + adv V z = - grad P z + nu • lap V z) :
    dvec (1, 0) (fun w => V w a) z
        + ∑ j, V z j * dvec (0, ee j) (fun w => V w a) z
      = - dvec (0, ee a) P z
        + nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) z := by
  have hd := differentiable_of_contDiffTop hV
  have h := congrArg (fun x : E3 => x a) hmom
  simp only [dtime, adv, grad, lap, dspace] at h
  have hlhs1 : (fderiv ℝ V z (1, 0) : E3) a = dvec (1, 0) (fun w => V w a) z :=
    dvec_coord V z (hd z) (1, 0) a
  have hlhs2 : ∀ j : Fin 3, (fderiv ℝ V z (0, ee j) : E3) a
      = dvec (0, ee j) (fun w => V w a) z := fun j => dvec_coord V z (hd z) (0, ee j) a
  have hgrad : (∑ i, (fderiv ℝ P z (0, ee i)) • ee i : E3) a = dvec (0, ee a) P z := by
    simp [ee, Pi.single_apply, dvec]
  have hlapk : ∀ k : Fin 3,
      (fderiv ℝ (fun w => fderiv ℝ V w (0, ee k)) z (0, ee k) : E3) a
        = dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) z := by
    intro k
    have h1 : (fderiv ℝ (fun w => fderiv ℝ V w (0, ee k)) z (0, ee k) : E3) a
        = dvec (0, ee k) (fun w => (dvec (0, ee k) V w) a) z :=
      dvec_coord (dvec (0, ee k) V) z
        (differentiable_of_contDiffTop (contDiff_dvec V hV (0, ee k)) z) (0, ee k) a
    rw [h1, dvec_coord_fun V hV (0, ee k) a]
  simp only [PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul,
    WithLp.ofLp_sum, Finset.sum_apply] at h
  rw [hlhs1] at h
  calc dvec (1, 0) (fun w => V w a) z + ∑ j, V z j * dvec (0, ee j) (fun w => V w a) z
      = dvec (1, 0) (fun w => V w a) z
          + ∑ j, V z j * (fderiv ℝ V z (0, ee j) : E3) a := by
        exact congrArg _ (Finset.sum_congr rfl fun j _ => by rw [hlhs2 j])
    _ = - (∑ i, (fderiv ℝ P z (0, ee i)) • ee i : E3) a
          + nu * ∑ k, (fderiv ℝ (fun w => fderiv ℝ V w (0, ee k)) z (0, ee k) : E3) a := by
        convert h using 2
    _ = - dvec (0, ee a) P z
          + nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) z := by
        rw [hgrad]
        exact congrArg _ (congrArg _ (Finset.sum_congr rfl fun k _ => hlapk k))

/-- The momentum equation, read off in the `a`-th coordinate, as an equality of
functions of spacetime. -/
lemma momentum_component (nu : ℝ) (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hmom : ∀ w : STime, dtime V w + adv V w = - grad P w + nu • lap V w) (a : Fin 3) :
    (fun z => dvec (1, 0) (fun w => V w a) z
        + ∑ j, V z j * dvec (0, ee j) (fun w => V w a) z)
      = fun z => - dvec (0, ee a) P z
        + nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) z :=
  funext fun z => momentum_component_at nu V P hV a z (hmom z)

/-! ## Differentiating the momentum equation -/

/-- The `c`-th spatial derivative of the `a`-th component of the momentum
equation, expanded by the product rule. -/
lemma dvec_momentum (nu : ℝ) (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hmom : ∀ w : STime, dtime V w + adv V w = - grad P w + nu • lap V w)
    (c a : Fin 3) (z : STime) :
    dvec (0, ee c) (dvec (1, 0) (fun w => V w a)) z
      + ∑ j, (dvec (0, ee c) (fun w => V w j) z * dvec (0, ee j) (fun w => V w a) z
              + V z j * dvec (0, ee c) (dvec (0, ee j) (fun w => V w a)) z)
    = - dvec (0, ee c) (dvec (0, ee a) P) z
      + nu * ∑ k, dvec (0, ee c) (dvec (0, ee k) (dvec (0, ee k) (fun w => V w a))) z := by
  have hu : ∀ q : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V w q) := fun q => contDiff_coord V hV q
  have hkey := congrArg (fun G : STime → ℝ => dvec (0, ee c) G z)
    (momentum_component nu V P hV hmom a)
  simp only at hkey
  -- expand the left-hand side
  have hAdiff : Differentiable ℝ (dvec (1, 0) (fun w => V w a)) :=
    differentiable_of_contDiffTop (contDiff_dvec _ (hu a) _)
  have hprod : ∀ j : Fin 3,
      ContDiff ℝ (⊤ : ℕ∞) (fun w => V w j * dvec (0, ee j) (fun w => V w a) w) :=
    fun j => (hu j).mul (contDiff_dvec _ (hu a) _)
  have hBdiff : Differentiable ℝ
      (fun z => ∑ j, V z j * dvec (0, ee j) (fun w => V w a) z) :=
    differentiable_of_contDiffTop (ContDiff.sum fun j _ => hprod j)
  have hL : dvec (0, ee c)
      (fun z => dvec (1, 0) (fun w => V w a) z
        + ∑ j, V z j * dvec (0, ee j) (fun w => V w a) z) z
      = dvec (0, ee c) (dvec (1, 0) (fun w => V w a)) z
        + ∑ j, (dvec (0, ee c) (fun w => V w j) z * dvec (0, ee j) (fun w => V w a) z
              + V z j * dvec (0, ee c) (dvec (0, ee j) (fun w => V w a)) z) := by
    rw [dvec_add _ _ z (hAdiff z) (hBdiff z) (0, ee c)]
    congr 1
    rw [dvec_sum Finset.univ (fun j w => V w j * dvec (0, ee j) (fun w => V w a) w) z
      (fun j _ => (differentiable_of_contDiffTop (hprod j)) z) (0, ee c)]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact dvec_mul (fun w => V w j) (dvec (0, ee j) (fun w => V w a)) z
      ((differentiable_of_contDiffTop (hu j)) z)
      ((differentiable_of_contDiffTop (contDiff_dvec _ (hu a) _)) z) (0, ee c)
  -- expand the right-hand side
  have hgradDiff : Differentiable ℝ (fun z => - dvec (0, ee a) P z) :=
    (differentiable_of_contDiffTop (contDiff_dvec P hP _)).neg
  have hlapk : ∀ k : Fin 3,
      ContDiff ℝ (⊤ : ℕ∞) (dvec (0, ee k) (dvec (0, ee k) (fun w => V w a))) :=
    fun k => contDiff_dvec _ (contDiff_dvec _ (hu a) _) _
  have hlapDiff : Differentiable ℝ
      (fun z => nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) z) :=
    (differentiable_of_contDiffTop
      (ContDiff.sum fun k _ => hlapk k)).const_mul nu
  have hR : dvec (0, ee c)
      (fun z => - dvec (0, ee a) P z
        + nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) z) z
      = - dvec (0, ee c) (dvec (0, ee a) P) z
        + nu * ∑ k, dvec (0, ee c) (dvec (0, ee k) (dvec (0, ee k) (fun w => V w a))) z := by
    rw [dvec_add _ _ z (hgradDiff z) (hlapDiff z) (0, ee c)]
    congr 1
    · exact dvec_neg (dvec (0, ee a) P) z
        ((differentiable_of_contDiffTop (contDiff_dvec P hP _)) z) (0, ee c)
    · have hc : dvec (0, ee c)
          (fun z => nu • ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) z) z
          = nu • dvec (0, ee c)
            (fun z => ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) z) z :=
        dvec_cmul nu _ z
          ((differentiable_of_contDiffTop (ContDiff.sum fun k _ => hlapk k)) z) (0, ee c)
      simp only [smul_eq_mul] at hc
      rw [hc, dvec_sum Finset.univ
        (fun k w => dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) w) z
        (fun k _ => (differentiable_of_contDiffTop (hlapk k)) z) (0, ee c)]
  rw [hL, hR] at hkey
  exact hkey

/-! ## The vorticity transport equation -/

/-- **Vorticity transport equation, in components.** -/
theorem vorticity_component (nu : ℝ) (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hdiv : ∀ w : STime, divg V w = 0)
    (hmom : ∀ w : STime, dtime V w + adv V w = - grad P w + nu • lap V w)
    (i : Fin 3) (z : STime) :
    dvec (1, 0) (vortComp V i) z + ∑ j, V z j * dvec (0, ee j) (vortComp V i) z
      = ∑ j, vortComp V j z * dvec (0, ee j) (fun w => V w i) z
        + nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (vortComp V i)) z := by
  have hu : ∀ q : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V w q) := fun q => contDiff_coord V hV q
  set a := i + 1 with ha
  set b := i + 2 with hb
  have hA := dvec_momentum nu V P hV hP hmom a b z
  have hB := dvec_momentum nu V P hV hP hmom b a z
  -- the vorticity component, as a difference of derivatives
  have hvort : vortComp V i = fun w => dvec (0, ee a) (fun y => V y b) w
      - dvec (0, ee b) (fun y => V y a) w := rfl
  -- time derivative
  have htime : dvec (0, ee a) (dvec (1, 0) (fun w => V w b)) z
      - dvec (0, ee b) (dvec (1, 0) (fun w => V w a)) z = dvec (1, 0) (vortComp V i) z := by
    rw [hvort, dvec_sub _ _ z
      ((differentiable_of_contDiffTop (contDiff_dvec _ (hu b) _)) z)
      ((differentiable_of_contDiffTop (contDiff_dvec _ (hu a) _)) z) (1, 0)]
    rw [dvec_comm (fun w => V w b) (hu b) (0, ee a) (1, 0) z,
      dvec_comm (fun w => V w a) (hu a) (0, ee b) (1, 0) z]
  -- transport term
  have htr : ∀ j : Fin 3, dvec (0, ee a) (dvec (0, ee j) (fun w => V w b)) z
      - dvec (0, ee b) (dvec (0, ee j) (fun w => V w a)) z
        = dvec (0, ee j) (vortComp V i) z := by
    intro j
    rw [hvort, dvec_sub _ _ z
      ((differentiable_of_contDiffTop (contDiff_dvec _ (hu b) _)) z)
      ((differentiable_of_contDiffTop (contDiff_dvec _ (hu a) _)) z) (0, ee j)]
    rw [dvec_comm (fun w => V w b) (hu b) (0, ee a) (0, ee j) z,
      dvec_comm (fun w => V w a) (hu a) (0, ee b) (0, ee j) z]
  -- viscous term
  have hvisc : ∀ k : Fin 3,
      dvec (0, ee a) (dvec (0, ee k) (dvec (0, ee k) (fun w => V w b))) z
        - dvec (0, ee b) (dvec (0, ee k) (dvec (0, ee k) (fun w => V w a))) z
      = dvec (0, ee k) (dvec (0, ee k) (vortComp V i)) z := by
    intro k
    have step : ∀ q : Fin 3, ∀ c : Fin 3,
        dvec (0, ee c) (dvec (0, ee k) (dvec (0, ee k) (fun w => V w q)))
          = dvec (0, ee k) (dvec (0, ee k) (dvec (0, ee c) (fun w => V w q))) := by
      intro q c
      rw [dvec_comm_fun (dvec (0, ee k) (fun w => V w q))
        (contDiff_dvec _ (hu q) _) (0, ee k) (0, ee c)]
      exact congrArg (dvec (0, ee k)) (dvec_comm_fun (fun w => V w q) (hu q) (0, ee k) (0, ee c))
    rw [congrFun (step b a) z, congrFun (step a b) z]
    rw [hvort]
    rw [dvec_sub_fun (dvec (0, ee a) (fun y => V y b)) (dvec (0, ee b) (fun y => V y a))
      (differentiable_of_contDiffTop (contDiff_dvec _ (hu b) _))
      (differentiable_of_contDiffTop (contDiff_dvec _ (hu a) _)) (0, ee k)]
    rw [dvec_sub_fun _ _
      (differentiable_of_contDiffTop (contDiff_dvec _ (contDiff_dvec _ (hu b) _) _))
      (differentiable_of_contDiffTop (contDiff_dvec _ (contDiff_dvec _ (hu a) _) _)) (0, ee k)]
  -- pressure cancels by symmetry of second derivatives
  have hpress : dvec (0, ee a) (dvec (0, ee b) P) z = dvec (0, ee b) (dvec (0, ee a) P) z :=
    dvec_comm P hP (0, ee b) (0, ee a) z
  -- the stretching identity
  have hDdiv : dvec (0, ee 0) (fun w => V w 0) z + dvec (0, ee 1) (fun w => V w 1) z
      + dvec (0, ee 2) (fun w => V w 2) z = 0 := by
    have h := hdiv z
    rw [divg_eq_sum V hV z] at h
    rw [Fin.sum_univ_three] at h
    exact h
  have hstretch : ∑ j, (dvec (0, ee a) (fun w => V w j) z * dvec (0, ee j) (fun w => V w b) z
        - dvec (0, ee b) (fun w => V w j) z * dvec (0, ee j) (fun w => V w a) z)
      = - ∑ j, vortComp V j z * dvec (0, ee j) (fun w => V w i) z := by
    have := stretching_identity (fun p q => dvec (0, ee p) (fun w => V w q) z) hDdiv i
    simpa [ha, hb, vortComp] using this
  -- combine
  have hcomb : (dvec (0, ee a) (dvec (1, 0) (fun w => V w b)) z
      - dvec (0, ee b) (dvec (1, 0) (fun w => V w a)) z)
      + (∑ j, ((dvec (0, ee a) (fun w => V w j) z * dvec (0, ee j) (fun w => V w b) z
                + V z j * dvec (0, ee a) (dvec (0, ee j) (fun w => V w b)) z)
             - (dvec (0, ee b) (fun w => V w j) z * dvec (0, ee j) (fun w => V w a) z
                + V z j * dvec (0, ee b) (dvec (0, ee j) (fun w => V w a)) z)))
      = (- dvec (0, ee a) (dvec (0, ee b) P) z + dvec (0, ee b) (dvec (0, ee a) P) z)
        + nu * ∑ k, (dvec (0, ee a) (dvec (0, ee k) (dvec (0, ee k) (fun w => V w b))) z
                   - dvec (0, ee b) (dvec (0, ee k) (dvec (0, ee k) (fun w => V w a))) z) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, mul_sub]
    linarith [hA, hB]
  rw [htime, hpress] at hcomb
  have hsum1 : (∑ j, ((dvec (0, ee a) (fun w => V w j) z * dvec (0, ee j) (fun w => V w b) z
                + V z j * dvec (0, ee a) (dvec (0, ee j) (fun w => V w b)) z)
             - (dvec (0, ee b) (fun w => V w j) z * dvec (0, ee j) (fun w => V w a) z
                + V z j * dvec (0, ee b) (dvec (0, ee j) (fun w => V w a)) z)))
      = (- ∑ j, vortComp V j z * dvec (0, ee j) (fun w => V w i) z)
        + ∑ j, V z j * dvec (0, ee j) (vortComp V i) z := by
    have hterm : ∀ j ∈ Finset.univ,
        ((dvec (0, ee a) (fun w => V w j) z * dvec (0, ee j) (fun w => V w b) z
                + V z j * dvec (0, ee a) (dvec (0, ee j) (fun w => V w b)) z)
             - (dvec (0, ee b) (fun w => V w j) z * dvec (0, ee j) (fun w => V w a) z
                + V z j * dvec (0, ee b) (dvec (0, ee j) (fun w => V w a)) z))
        = (dvec (0, ee a) (fun w => V w j) z * dvec (0, ee j) (fun w => V w b) z
            - dvec (0, ee b) (fun w => V w j) z * dvec (0, ee j) (fun w => V w a) z)
          + V z j * dvec (0, ee j) (vortComp V i) z := by
      intro j _
      rw [← htr j]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, hstretch]
  have hsum2 : (∑ k, (dvec (0, ee a) (dvec (0, ee k) (dvec (0, ee k) (fun w => V w b))) z
                   - dvec (0, ee b) (dvec (0, ee k) (dvec (0, ee k) (fun w => V w a))) z))
      = ∑ k, dvec (0, ee k) (dvec (0, ee k) (vortComp V i)) z :=
    Finset.sum_congr rfl fun k _ => hvisc k
  rw [hsum1, hsum2] at hcomb
  linarith [hcomb]

/-- **Vorticity transport equation.**  For every smooth divergence-free solution
of the momentum equation, the vorticity `ω = curl u` satisfies

`∂_t ω + (u·∇)ω = (ω·∇)u + ν Δω`.

This is the analytic input of the Beale–Kato–Majda continuation criterion,
which the Agda development carries as opaque data. -/
theorem vorticity_equation (nu : ℝ) (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hdiv : ∀ w : STime, divg V w = 0)
    (hmom : ∀ w : STime, dtime V w + adv V w = - grad P w + nu • lap V w)
    (z : STime) :
    dtime (fun w => curl V w) z + (∑ j, (V z j) • dspace (fun w => curl V w) j z)
      = (∑ j, (curl V z j) • dspace V j z) + nu • lap (fun w => curl V w) z := by
  have hcurl := contDiff_curl V hV
  have hu : ∀ q : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V w q) := fun q => contDiff_coord V hV q
  ext i
  have e1 : (dtime (fun w => curl V w) z : E3) i = dvec (1, 0) (vortComp V i) z := by
    have := dvec_coord (fun w => curl V w) z (differentiable_of_contDiffTop hcurl z) (1, 0) i
    rw [show (dtime (fun w => curl V w) z : E3) i
      = (dvec (1, 0) (fun w => curl V w) z : E3) i from rfl, this, curl_coord]
  have e2 : ∀ j : Fin 3, (dspace (fun w => curl V w) j z : E3) i
      = dvec (0, ee j) (vortComp V i) z := by
    intro j
    have := dvec_coord (fun w => curl V w) z (differentiable_of_contDiffTop hcurl z) (0, ee j) i
    rw [show (dspace (fun w => curl V w) j z : E3) i
      = (dvec (0, ee j) (fun w => curl V w) z : E3) i from rfl, this, curl_coord]
  have e3 : ∀ j : Fin 3, (dspace V j z : E3) i = dvec (0, ee j) (fun w => V w i) z :=
    fun j => dvec_coord V z (differentiable_of_contDiffTop hV z) (0, ee j) i
  have e4 : (lap (fun w => curl V w) z : E3) i
      = ∑ k, dvec (0, ee k) (dvec (0, ee k) (vortComp V i)) z := by
    have hstep : ∀ k : Fin 3,
        (dspace (fun w => dspace (fun w => curl V w) k w) k z : E3) i
          = dvec (0, ee k) (dvec (0, ee k) (vortComp V i)) z := by
      intro k
      have h1 : (dvec (0, ee k) (dvec (0, ee k) (fun w => curl V w)) z : E3) i
          = dvec (0, ee k) (fun w => (dvec (0, ee k) (fun w => curl V w) w : E3) i) z :=
        dvec_coord (dvec (0, ee k) (fun w => curl V w)) z
          (differentiable_of_contDiffTop (contDiff_dvec _ hcurl (0, ee k)) z) (0, ee k) i
      rw [show (dspace (fun w => dspace (fun w => curl V w) k w) k z : E3) i
        = (dvec (0, ee k) (dvec (0, ee k) (fun w => curl V w)) z : E3) i from rfl, h1]
      congr 1
      rw [dvec_coord_fun (fun w => curl V w) hcurl (0, ee k) i, curl_coord]
    simp only [lap, WithLp.ofLp_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun k _ => hstep k
  simp only [PiLp.add_apply, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul]
  rw [e1, e4]
  have el : ∑ j, V z j * (dspace (fun w => curl V w) j z : E3) i
      = ∑ j, V z j * dvec (0, ee j) (vortComp V i) z :=
    Finset.sum_congr rfl fun j _ => by rw [e2 j]
  have er : ∑ j, (curl V z j) * (dspace V j z : E3) i
      = ∑ j, vortComp V j z * dvec (0, ee j) (fun w => V w i) z :=
    Finset.sum_congr rfl fun j _ => by rw [e3 j, curl_apply]
  rw [el, er]
  exact vorticity_component nu V P hV hP hdiv hmom i z

end ClayNS
