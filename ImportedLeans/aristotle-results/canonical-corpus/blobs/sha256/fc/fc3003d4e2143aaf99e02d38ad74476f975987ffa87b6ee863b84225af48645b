/-
# The pressure Poisson equation, derived

In the Agda development the recovery of the pressure from the projected
equation is an *assumed* field: `GlobalPhysicalSolutionPrimitiveInputs` carries
`pressureFromProjectedVelocity`, `PressurePoissonEquation` and
`PressureMeanZeroNormalization` as opaque data
(`DASHI/Physics/Closure/NSTriadKNLuoGlobalPhysicalSolutionReductionExact.agda`).

This file derives the pressure Poisson equation for real, from the
Navier–Stokes system of `RequestProject/NavierStokes/ClayPeriodic.lean`:
taking the divergence of the momentum equation on a divergence-free smooth
field gives

  Δp = - ∑_{i,j} (∂_i u_j)(∂_j u_i).

Everything is proved: interchange of derivatives with finite sums and with
coordinate projections, symmetry of second derivatives, the product rule for
the advective term, and `div Δu = Δ div u`, `div ∂_t u = ∂_t div u`,
`div ∇p = Δp`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.ClayPeriodic

open scoped BigOperators

noncomputable section

namespace ClayNS

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## A uniform directional-derivative operator -/

/-- Directional derivative of a spacetime field in the direction `a`. -/
def dvec (a : STime) (V : STime → F) (z : STime) : F := fderiv ℝ V z a

lemma dtime_eq_dvec (V : STime → F) (z : STime) : dtime V z = dvec (1, 0) V z := rfl

lemma dspace_eq_dvec (V : STime → F) (i : Fin 3) (z : STime) :
    dspace V i z = dvec (0, ee i) V z := rfl

/-! ### Calculus toolbox for `dvec` -/

lemma contDiff_dvec (V : STime → F) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (a : STime) :
    ContDiff ℝ (⊤ : ℕ∞) (dvec a V) := by
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fun w : STime => fderiv ℝ V w) := hV.fderiv_right (by simp)
  exact (ContinuousLinearMap.apply ℝ F a).contDiff.comp hfd

lemma contDiff_coord (W : STime → E3) (hW : ContDiff ℝ (⊤ : ℕ∞) W) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w => W w i) :=
  (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).contDiff.comp hW

lemma differentiable_of_contDiffTop {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {W : STime → G} (hW : ContDiff ℝ (⊤ : ℕ∞) W) : Differentiable ℝ W :=
  hW.differentiable (by simp)

/-- Derivatives commute with finite sums. -/
lemma dvec_sum {ι : Type*} (s : Finset ι) (f : ι → STime → F) (z : STime)
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) (a : STime) :
    dvec a (fun w => ∑ i ∈ s, f i w) z = ∑ i ∈ s, dvec a (f i) z := by
  simp only [dvec]
  rw [fderiv_fun_sum hf]
  simp

/-- Derivatives commute with coordinate projections. -/
lemma dvec_coord (W : STime → E3) (z : STime) (hW : DifferentiableAt ℝ W z)
    (a : STime) (i : Fin 3) :
    (dvec a W z) i = dvec a (fun w => W w i) z := by
  have happ : HasFDerivAt (fun w : STime => W w i)
      ((EuclideanSpace.proj i : E3 →L[ℝ] ℝ).comp (fderiv ℝ W z)) z :=
    ((EuclideanSpace.proj i : E3 →L[ℝ] ℝ).hasFDerivAt).comp z hW.hasFDerivAt
  show _ = (fderiv ℝ (fun w : STime => W w i) z) a
  rw [happ.fderiv]
  simp [dvec]

lemma dvec_const_smul (f : STime → ℝ) (c : E3) (z : STime)
    (hf : DifferentiableAt ℝ f z) (a : STime) :
    dvec a (fun w => f w • c) z = (dvec a f z) • c := by
  have h : HasFDerivAt (fun w => f w • c) ((fderiv ℝ f z).smulRight c) z :=
    hf.hasFDerivAt.smul_const c
  show (fderiv ℝ (fun w => f w • c) z) a = _
  rw [h.fderiv]
  simp [dvec]

lemma dvec_smul (f : STime → ℝ) (g : STime → E3) (z : STime)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (a : STime) :
    dvec a (fun w => f w • g w) z = (dvec a f z) • g z + f z • (dvec a g z) := by
  have h : HasFDerivAt (fun w => f w • g w)
      (f z • fderiv ℝ g z + (fderiv ℝ f z).smulRight (g z)) z :=
    hf.hasFDerivAt.smul hg.hasFDerivAt
  show (fderiv ℝ (fun w => f w • g w) z) a = _
  rw [h.fderiv]
  simp [dvec]
  module

/-- Derivatives are additive. -/
lemma dvec_add (A B : STime → F) (z : STime) (hA : DifferentiableAt ℝ A z)
    (hB : DifferentiableAt ℝ B z) (a : STime) :
    dvec a (fun w => A w + B w) z = dvec a A z + dvec a B z :=
  congrArg (fun L : STime →L[ℝ] F => L a) (hA.hasFDerivAt.add hB.hasFDerivAt).fderiv

/-- Derivatives commute with negation. -/
lemma dvec_neg (A : STime → F) (z : STime) (hA : DifferentiableAt ℝ A z) (a : STime) :
    dvec a (fun w => - A w) z = - dvec a A z :=
  congrArg (fun L : STime →L[ℝ] F => L a) hA.hasFDerivAt.neg.fderiv

/-- Derivatives commute with scalar multiples. -/
lemma dvec_cmul (c : ℝ) (A : STime → F) (z : STime) (hA : DifferentiableAt ℝ A z) (a : STime) :
    dvec a (fun w => c • A w) z = c • dvec a A z :=
  congrArg (fun L : STime →L[ℝ] F => L a) (hA.hasFDerivAt.const_smul c).fderiv

lemma dvec_dvec (V : STime → F) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (a b : STime) (z : STime) :
    dvec b (dvec a V) z = fderiv ℝ (fderiv ℝ V) z b a := by
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fun w : STime => fderiv ℝ V w) := hV.fderiv_right (by simp)
  have hdiff : DifferentiableAt ℝ (fun w : STime => fderiv ℝ V w) z :=
    (hfd.differentiable (by simp)) z
  have happ : HasFDerivAt (fun w : STime => (fderiv ℝ V w) a)
      ((ContinuousLinearMap.apply ℝ F a).comp (fderiv ℝ (fun w : STime => fderiv ℝ V w) z)) z :=
    ((ContinuousLinearMap.apply ℝ F a).hasFDerivAt).comp z hdiff.hasFDerivAt
  show (fderiv ℝ (fun w : STime => (fderiv ℝ V w) a) z) b = _
  rw [happ.fderiv]
  simp

/-- Symmetry of second derivatives, in directional form. -/
lemma dvec_comm (V : STime → F) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (a b : STime) (z : STime) :
    dvec b (dvec a V) z = dvec a (dvec b V) z := by
  have hle : minSmoothness ℝ 2 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    simp
    exact ENat.LEInfty.out
  rw [dvec_dvec V hV a b z, dvec_dvec V hV b a z]
  exact (hV.contDiffAt.isSymmSndFDerivAt hle) b a

/-! ## Divergence of the individual terms -/

/-- The divergence, written through `dvec` and scalar components. -/
lemma divg_eq_sum (V : STime → E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (z : STime) :
    divg V z = ∑ i, dvec (0, ee i) (fun w => V w i) z := by
  refine Finset.sum_congr rfl ?_
  intro i _
  exact dvec_coord V z ((differentiable_of_contDiffTop hV) z) (0, ee i) i

/-- `div (∂_a u) = ∂_a (div u)` for any constant direction `a`. -/
lemma divg_dvec (V : STime → E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (a : STime) (z : STime) :
    divg (dvec a V) z = dvec a (fun w => divg V w) z := by
  have hstep : ∀ i : Fin 3,
      (dvec (0, ee i) (dvec a V) z) i = dvec a (fun w => (dvec (0, ee i) V w) i) z := by
    intro i
    rw [dvec_comm V hV a (0, ee i) z]
    exact dvec_coord (dvec (0, ee i) V) z
      ((differentiable_of_contDiffTop (contDiff_dvec V hV (0, ee i))) z) a i
  have hsum : dvec a (fun w => ∑ i, (dvec (0, ee i) V w) i) z
      = ∑ i, dvec a (fun w => (dvec (0, ee i) V w) i) z := by
    refine dvec_sum Finset.univ _ z ?_ a
    intro i _
    exact (differentiable_of_contDiffTop
      (contDiff_coord (dvec (0, ee i) V) (contDiff_dvec V hV (0, ee i)) i)) z
  calc divg (dvec a V) z = ∑ i, (dvec (0, ee i) (dvec a V) z) i := rfl
    _ = ∑ i, dvec a (fun w => (dvec (0, ee i) V w) i) z := Finset.sum_congr rfl (fun i _ => hstep i)
    _ = dvec a (fun w => ∑ i, (dvec (0, ee i) V w) i) z := hsum.symm
    _ = dvec a (fun w => divg V w) z := rfl

/-- `div ∂_t u = ∂_t div u`. -/
lemma divg_dtime (V : STime → E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (z : STime) :
    divg (fun w => dtime V w) z = dtime (fun w => divg V w) z :=
  divg_dvec V hV (1, 0) z

/-- `div Δu = Δ div u`. -/
lemma divg_lap (V : STime → E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (z : STime) :
    divg (fun w => lap V w) z = lap (fun w => divg V w) z := by
  -- write the Laplacian as a sum of second directional derivatives
  have hlapV : (fun w => lap V w) = fun w => ∑ k, dvec (0, ee k) (dvec (0, ee k) V) w := rfl
  have hdiffk : ∀ k : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (dvec (0, ee k) (dvec (0, ee k) V)) :=
    fun k => contDiff_dvec _ (contDiff_dvec V hV (0, ee k)) (0, ee k)
  -- divergence of a finite sum of fields
  have hsum : divg (fun w => ∑ k, dvec (0, ee k) (dvec (0, ee k) V) w) z
      = ∑ k, divg (dvec (0, ee k) (dvec (0, ee k) V)) z := by
    have hco : ∀ i : Fin 3,
        (dvec (0, ee i) (fun w => ∑ k, dvec (0, ee k) (dvec (0, ee k) V) w) z) i
          = ∑ k, (dvec (0, ee i) (dvec (0, ee k) (dvec (0, ee k) V)) z) i := by
      intro i
      rw [dvec_sum Finset.univ _ z
        (fun k _ => (differentiable_of_contDiffTop (hdiffk k)) z) (0, ee i)]
      simp
    calc divg (fun w => ∑ k, dvec (0, ee k) (dvec (0, ee k) V) w) z
        = ∑ i, (dvec (0, ee i)
            (fun w => ∑ k, dvec (0, ee k) (dvec (0, ee k) V) w) z) i := rfl
      _ = ∑ i, ∑ k, (dvec (0, ee i) (dvec (0, ee k) (dvec (0, ee k) V)) z) i :=
          Finset.sum_congr rfl (fun i _ => hco i)
      _ = ∑ k, ∑ i, (dvec (0, ee i) (dvec (0, ee k) (dvec (0, ee k) V)) z) i :=
          Finset.sum_comm
      _ = ∑ k, divg (dvec (0, ee k) (dvec (0, ee k) V)) z := rfl
  rw [hlapV, hsum]
  have hstep : ∀ k : Fin 3,
      divg (dvec (0, ee k) (dvec (0, ee k) V)) z
        = dvec (0, ee k) (dvec (0, ee k) (fun w => divg V w)) z := by
    intro k
    rw [divg_dvec _ (contDiff_dvec V hV (0, ee k)) (0, ee k) z]
    have : (fun w => divg (dvec (0, ee k) V) w) = fun w => dvec (0, ee k) (fun y => divg V y) w := by
      funext w; exact divg_dvec V hV (0, ee k) w
    rw [this]
  exact Finset.sum_congr rfl (fun k _ => hstep k)

/-- `div ∇p = Δp`. -/
lemma divg_grad (P : STime → ℝ) (hP : ContDiff ℝ (⊤ : ℕ∞) P) (z : STime) :
    divg (fun w => grad P w) z = lap P z := by
  have hdi : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (dvec (0, ee i) P) := fun i => contDiff_dvec P hP _
  have hcomp : ∀ j : Fin 3,
      (dvec (0, ee j) (fun w => grad P w) z) j = dvec (0, ee j) (dvec (0, ee j) P) z := by
    intro j
    have hgradP : (fun w => grad P w) = fun w => ∑ i, (dvec (0, ee i) P w) • ee i := rfl
    rw [hgradP, dvec_sum Finset.univ (fun (i : Fin 3) (w : STime) => (dvec (0, ee i) P w) • ee i) z
      (fun i _ => (differentiable_of_contDiffTop
        ((hdi i).smul (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) fun _ : STime => ee i))) z) (0, ee j)]
    have hterm : ∀ i : Fin 3,
        dvec (0, ee j) (fun w => (dvec (0, ee i) P w) • ee i) z
          = (dvec (0, ee j) (dvec (0, ee i) P) z) • ee i :=
      fun i => dvec_const_smul _ _ z ((differentiable_of_contDiffTop (hdi i)) z) _
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    simp [ee, Pi.single_apply]
  calc divg (fun w => grad P w) z
      = ∑ j, (dvec (0, ee j) (fun w => grad P w) z) j := rfl
    _ = ∑ j, dvec (0, ee j) (dvec (0, ee j) P) z := Finset.sum_congr rfl (fun j _ => hcomp j)
    _ = lap P z := rfl

/-- `div ((u·∇)u) = ∑_{i,j} (∂_i u_j)(∂_j u_i) + ∑_j u_j ∂_j (div u)`. -/
lemma divg_adv (V : STime → E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (z : STime) :
    divg (fun w => adv V w) z
      = (∑ i, ∑ j, (dspace V i z j) * (dspace V j z i))
        + ∑ j, (V z j) * dvec (0, ee j) (fun w => divg V w) z := by
  have hVd : Differentiable ℝ V := differentiable_of_contDiffTop hV
  have hcoordDiff : ∀ j : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V w j) :=
    fun j => contDiff_coord V hV j
  have hdj : ∀ j : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (dvec (0, ee j) V) :=
    fun j => contDiff_dvec V hV _
  -- differentiate one advective summand
  have hterm : ∀ (i j : Fin 3),
      dvec (0, ee i) (fun w => (V w j) • dvec (0, ee j) V w) z
        = (dvec (0, ee i) (fun w => V w j) z) • (dvec (0, ee j) V z)
          + (V z j) • (dvec (0, ee i) (dvec (0, ee j) V) z) := by
    intro i j
    exact dvec_smul _ _ z ((differentiable_of_contDiffTop (hcoordDiff j)) z)
      ((differentiable_of_contDiffTop (hdj j)) z) _
  -- the i-th component of ∂_i (adv V)
  have hrow : ∀ i : Fin 3,
      (dvec (0, ee i) (fun w => adv V w) z) i
        = ∑ j, ((dspace V i z j) * (dspace V j z i)
                + (V z j) * ((dvec (0, ee i) (dvec (0, ee j) V) z) i)) := by
    intro i
    have hadv : (fun w => adv V w) = fun w => ∑ j, (V w j) • dvec (0, ee j) V w := rfl
    rw [hadv, dvec_sum Finset.univ
      (fun (j : Fin 3) (w : STime) => (V w j) • dvec (0, ee j) V w) z
      (fun j _ => (differentiable_of_contDiffTop
        ((hcoordDiff j).smul (hdj j))) z) (0, ee i)]
    rw [Finset.sum_congr rfl (fun j _ => hterm i j)]
    rw [show ((∑ j, ((dvec (0, ee i) (fun w => V w j) z) • (dvec (0, ee j) V z)
            + (V z j) • (dvec (0, ee i) (dvec (0, ee j) V) z))) i)
        = ∑ j, ((dvec (0, ee i) (fun w => V w j) z) * ((dvec (0, ee j) V z) i)
            + (V z j) * ((dvec (0, ee i) (dvec (0, ee j) V) z) i)) from by
      simp]
    refine Finset.sum_congr rfl ?_
    intro j _
    congr 1
    congr 1
    exact (dvec_coord V z (hVd z) (0, ee i) j).symm
  calc divg (fun w => adv V w) z
      = ∑ i, (dvec (0, ee i) (fun w => adv V w) z) i := rfl
    _ = ∑ i, ∑ j, ((dspace V i z j) * (dspace V j z i)
          + (V z j) * ((dvec (0, ee i) (dvec (0, ee j) V) z) i)) :=
        Finset.sum_congr rfl (fun i _ => hrow i)
    _ = (∑ i, ∑ j, (dspace V i z j) * (dspace V j z i))
          + ∑ i, ∑ j, (V z j) * ((dvec (0, ee i) (dvec (0, ee j) V) z) i) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib)
    _ = (∑ i, ∑ j, (dspace V i z j) * (dspace V j z i))
          + ∑ j, (V z j) * dvec (0, ee j) (fun w => divg V w) z := by
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [← Finset.mul_sum]
        congr 1
        exact divg_dvec V hV (0, ee j) z

/-! ## The pressure Poisson equation -/

/-- **Pressure Poisson equation.**  For a smooth divergence-free velocity field
solving the momentum equation everywhere, the pressure satisfies

`Δp = - ∑_{i,j} (∂_i u_j)(∂_j u_i)`.

This is the analytic content that the Agda development assumes through the
fields `pressureFromProjectedVelocity` and `PressurePoissonEquation`. -/
theorem pressure_poisson (nu : ℝ) (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hdiv : ∀ w : STime, divg V w = 0)
    (hmom : ∀ w : STime, dtime V w + adv V w = - grad P w + nu • lap V w) :
    ∀ z : STime, lap P z = - ∑ i, ∑ j, (dspace V i z j) * (dspace V j z i) := by
  have hdivfun : (fun w => divg V w) = fun _ : STime => (0 : ℝ) := funext hdiv
  intro z
  -- the divergence of each side of the momentum equation
  have hL : divg (fun w => dtime V w + adv V w) z
      = divg (fun w => - grad P w + nu • lap V w) z := by
    rw [funext hmom]
  -- left-hand side
  have hdtime : divg (fun w => dtime V w) z = 0 := by
    rw [divg_dtime V hV z, hdivfun]
    simp [dtime]
  have hadv : divg (fun w => adv V w) z
      = ∑ i, ∑ j, (dspace V i z j) * (dspace V j z i) := by
    rw [divg_adv V hV z, hdivfun]
    have : ∀ j : Fin 3, dvec (0, ee j) (fun _ : STime => (0 : ℝ)) z = 0 := by
      intro j; simp [dvec]
    simp [this]
  have hlap : divg (fun w => lap V w) z = 0 := by
    rw [divg_lap V hV z, hdivfun]
    simp [lap, dspace]
  -- divergence is additive
  have hadd : ∀ (A B : STime → E3), Differentiable ℝ A → Differentiable ℝ B →
      divg (fun w => A w + B w) z = divg A z + divg B z := by
    intro A B hA hB
    have hcomp : ∀ i : Fin 3, (dvec (0, ee i) (fun w => A w + B w) z) i
        = (dvec (0, ee i) A z) i + (dvec (0, ee i) B z) i := by
      intro i
      have : dvec (0, ee i) (fun w => A w + B w) z
          = dvec (0, ee i) A z + dvec (0, ee i) B z :=
        dvec_add A B z (hA z) (hB z) (0, ee i)
      rw [this]; rfl
    calc divg (fun w => A w + B w) z
        = ∑ i, (dvec (0, ee i) (fun w => A w + B w) z) i := rfl
      _ = ∑ i, ((dvec (0, ee i) A z) i + (dvec (0, ee i) B z) i) :=
          Finset.sum_congr rfl (fun i _ => hcomp i)
      _ = divg A z + divg B z := by
          rw [Finset.sum_add_distrib]; rfl
  have hnegsmul : divg (fun w => - grad P w + nu • lap V w) z
      = - divg (fun w => grad P w) z + nu * divg (fun w => lap V w) z := by
    have hgradDiff : Differentiable ℝ (fun w => grad P w) := by
      have : ContDiff ℝ (⊤ : ℕ∞) (fun w => grad P w) := by
        have : ContDiff ℝ (⊤ : ℕ∞) (fun w => ∑ i, (dvec (0, ee i) P w) • ee i) :=
          ContDiff.sum (fun i _ => (contDiff_dvec P hP _).smul contDiff_const)
        exact this
      exact differentiable_of_contDiffTop this
    have hlapDiff : Differentiable ℝ (fun w => lap V w) := by
      have : ContDiff ℝ (⊤ : ℕ∞) (fun w => ∑ k, dvec (0, ee k) (dvec (0, ee k) V) w) :=
        ContDiff.sum (fun k _ => contDiff_dvec _ (contDiff_dvec V hV _) _)
      exact differentiable_of_contDiffTop this
    rw [hadd (fun w => - grad P w) (fun w => nu • lap V w) (hgradDiff.neg) (hlapDiff.const_smul nu)]
    congr 1
    · have hcomp : ∀ i : Fin 3, (dvec (0, ee i) (fun w => - grad P w) z) i
          = - (dvec (0, ee i) (fun w => grad P w) z) i := by
        intro i
        have : dvec (0, ee i) (fun w => - grad P w) z = - dvec (0, ee i) (fun w => grad P w) z :=
          dvec_neg (fun w => grad P w) z (hgradDiff z) (0, ee i)
        rw [this]; rfl
      calc divg (fun w => - grad P w) z
          = ∑ i, (dvec (0, ee i) (fun w => - grad P w) z) i := rfl
        _ = ∑ i, - (dvec (0, ee i) (fun w => grad P w) z) i :=
            Finset.sum_congr rfl (fun i _ => hcomp i)
        _ = - divg (fun w => grad P w) z := by rw [Finset.sum_neg_distrib]; rfl
    · have hcomp : ∀ i : Fin 3, (dvec (0, ee i) (fun w => nu • lap V w) z) i
          = nu * (dvec (0, ee i) (fun w => lap V w) z) i := by
        intro i
        have : dvec (0, ee i) (fun w => nu • lap V w) z
            = nu • dvec (0, ee i) (fun w => lap V w) z :=
          dvec_cmul nu (fun w => lap V w) z (hlapDiff z) (0, ee i)
        rw [this]; rfl
      calc divg (fun w => nu • lap V w) z
          = ∑ i, (dvec (0, ee i) (fun w => nu • lap V w) z) i := rfl
        _ = ∑ i, nu * (dvec (0, ee i) (fun w => lap V w) z) i :=
            Finset.sum_congr rfl (fun i _ => hcomp i)
        _ = nu * divg (fun w => lap V w) z := by rw [← Finset.mul_sum]; rfl
  have hdtimeDiff : Differentiable ℝ (fun w => dtime V w) :=
    differentiable_of_contDiffTop (contDiff_dvec V hV (1, 0))
  have hadvDiff : Differentiable ℝ (fun w => adv V w) := by
    have : ContDiff ℝ (⊤ : ℕ∞) (fun w => ∑ j, (V w j) • dvec (0, ee j) V w) :=
      ContDiff.sum (fun j _ => (contDiff_coord V hV j).smul (contDiff_dvec V hV _))
    exact differentiable_of_contDiffTop this
  rw [hadd (fun w => dtime V w) (fun w => adv V w) hdtimeDiff hadvDiff, hdtime, hadv, hnegsmul, hlap,
    divg_grad P hP z] at hL
  linarith [hL]

end ClayNS
