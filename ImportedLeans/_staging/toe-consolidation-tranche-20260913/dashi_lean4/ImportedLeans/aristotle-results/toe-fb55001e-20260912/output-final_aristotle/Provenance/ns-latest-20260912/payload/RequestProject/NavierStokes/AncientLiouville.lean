/-
# A Liouville theorem for bounded ancient periodic Navier–Stokes solutions

Koch–Nadirashvili–Seregin–Šverák reduce the regularity problem to a Liouville
theorem for *bounded ancient mild solutions*: a solution defined for all
negative times which is bounded must be constant.  On the whole space `ℝ³` this
is open; here we prove the **periodic** analogue, in full, from the constructive
material of this development:

`ancient_periodic_liouville` — if `(V,P)` is a smooth `ℤ³`-periodic solution of
the Navier–Stokes system with viscosity `ν > 0` defined for *all* times, and the
cell energy of `V` is bounded, then `V` is a constant vector field.

The argument is the backward energy argument made available by the two new
ingredients of this pass:

* the mean of `V` over the cell is independent of time (`meanComp_eq`), so the
  Galilean-corrected energy `D(t) = E(t) - ½|m|²` is a genuine Lyapunov
  functional with `D' = -2ν · enstrophy`;
* the Poincaré inequality on the cell (`cellInt_poincare`) makes the dissipation
  coercive, `D ≤ 3 · enstrophy`, whence `D' ≤ -(2ν/3) D`;
* running this *backwards* in time forces `e^{kt} D(t)` to be nonincreasing, so
  `e^{kt} D(t) ≤ e^{ks} · sup D → 0` as `s → -∞`; hence `D ≡ 0` and `V ≡ m`.

The caveat, stated plainly: this is the Liouville theorem *on the torus*.  The
blow-up limits produced by the Koch–Nadirashvili–Seregin–Šverák extraction live
on the whole space `ℝ³` (parabolic rescaling destroys periodicity), so this
theorem does **not** close the R2 gap of the Clay programme.  What it does is
settle the periodic case of the same rigidity question and isolate exactly which
ingredient fails on `ℝ³`: the Poincaré inequality, i.e. the spectral gap of the
Laplacian, which the torus has and `ℝ³` does not.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.Poincare
import RequestProject.NavierStokes.EnstrophyDissipation

open scoped BigOperators
open MeasureTheory Set

noncomputable section

namespace ClayNS

/-! ## Ancient solutions -/

/-- `(V,P)` is a smooth spatially `ℤ³`-periodic solution of the incompressible
Navier–Stokes system with viscosity `ν` and zero force, defined for **all**
times (in particular for all negative times: an *ancient* solution). -/
structure IsAncientNSSolution (nu : ℝ) (V : STime → E3) (P : STime → ℝ) : Prop where
  smoothVelocity : ContDiff ℝ (⊤ : ℕ∞) V
  smoothPressure : ContDiff ℝ (⊤ : ℕ∞) P
  periodicVelocity : SpacePeriodic V
  periodicPressure : SpacePeriodic P
  momentum : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z
  incompressible : ∀ z : STime, divg V z = 0

/-- The mean of the `a`-th velocity component over the periodicity cell. -/
def meanComp (V : STime → E3) (t : ℝ) (a : Fin 3) : ℝ := cellInt (fun x => V (t, x) a)

/-! ## Missing linearity of the cell integral -/

@[simp] lemma cellInt_const (c : ℝ) : cellInt (fun _ : E3 => c) = c := cubeInt_const c

lemma cellInt_finset_sum {ι : Type*} (s : Finset ι) (f : ι → E3 → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    cellInt (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, cellInt (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      have hcont : ∀ j ∈ s, Continuous (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
      have hsum : Continuous (fun x => ∑ j ∈ s, f j x) :=
        continuous_finset_sum _ fun j hj => hcont j hj
      have hstep : cellInt (fun x => f i x + ∑ j ∈ s, f j x)
          = cellInt (f i) + cellInt (fun x => ∑ j ∈ s, f j x) :=
        cellInt_add (hf i (Finset.mem_insert_self i s)) hsum
      have hins : cellInt (fun x => ∑ j ∈ insert i s, f j x)
          = cellInt (fun x => f i x + ∑ j ∈ s, f j x) :=
        cellInt_congr fun x => by rw [Finset.sum_insert hi]
      rw [Finset.sum_insert hi, hins, hstep, ih hcont]

/-! ## The mean is a constant of the motion -/

section Mean

variable {nu : ℝ} {V : STime → E3} {P : STime → ℝ}

/-- The advective term of the `a`-th component integrates to zero over the cell:
by incompressibility it is a spatial divergence. -/
theorem cellInt_adv_comp_eq_zero (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVper : SpacePeriodic V)
    (hdiv : ∀ w : STime, divg V w = 0) (a : Fin 3) (t : ℝ) :
    cellInt (fun x => ∑ j, V (t, x) j * dvec (0, ee j) (fun w => V w a) (t, x)) = 0 := by
  classical
  have hVc : ∀ q : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V w q) := fun q => contDiff_coord V hV q
  set G : Fin 3 → STime → ℝ := fun j w => V w j * V w a with hG
  have hGsmooth : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (G j) := fun j => (hVc j).mul (hVc a)
  have hGper : ∀ j, SpacePeriodic (G j) := by
    intro j z k
    simp only [hG]
    rw [hVper z k]
  have hpt : ∀ x : E3, (∑ j, dvec (0, ee j) (G j) (t, x))
      = ∑ j, V (t, x) j * dvec (0, ee j) (fun w => V w a) (t, x) := by
    intro x
    have hprod : ∀ j : Fin 3, dvec (0, ee j) (G j) (t, x)
        = dvec (0, ee j) (fun w => V w j) (t, x) * V (t, x) a
          + V (t, x) j * dvec (0, ee j) (fun w => V w a) (t, x) :=
      fun j => dvec_mul (fun w => V w j) (fun w => V w a) (t, x)
        ((differentiable_of_contDiffTop (hVc j)) _)
        ((differentiable_of_contDiffTop (hVc a)) _) (0, ee j)
    rw [Finset.sum_congr rfl fun j _ => hprod j, Finset.sum_add_distrib]
    have hd : ∑ j, dvec (0, ee j) (fun w => V w j) (t, x) * V (t, x) a = 0 := by
      rw [← Finset.sum_mul, ← divg_eq_sum V hV (t, x), hdiv (t, x), zero_mul]
    rw [hd, zero_add]
  rw [← cellInt_congr hpt]
  exact cellInt_dvec_divergence_eq_zero G hGsmooth hGper t

/-- The Laplacian term integrates to zero over the cell. -/
theorem cellInt_lap_comp_eq_zero (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVper : SpacePeriodic V)
    (a : Fin 3) (t : ℝ) :
    cellInt (fun x => ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) (t, x)) = 0 := by
  have hVa : ContDiff ℝ (⊤ : ℕ∞) (fun w => V w a) := contDiff_coord V hV a
  have hVaper : SpacePeriodic (fun w => V w a) :=
    fun z j => congrArg (fun v : E3 => v a) (hVper z j)
  have hcont : ∀ k : Fin 3,
      Continuous (fun x : E3 => dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) (t, x)) :=
    fun k => continuous_time_slice
      (continuous_dvec _ (contDiff_dvec _ hVa (0, ee k)) (0, ee k)) t
  rw [cellInt_finset_sum Finset.univ _ (fun k _ => hcont k)]
  refine Finset.sum_eq_zero fun k _ => ?_
  exact cellInt_dvec_eq_zero (dvec (0, ee k) (fun w => V w a)) (contDiff_dvec _ hVa (0, ee k))
    (spacePeriodic_dvec (differentiable_of_contDiffTop hVa) hVaper (0, ee k)) k t

/-- Hence the time derivative of each velocity component integrates to zero. -/
theorem cellInt_dtime_comp_eq_zero (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P)
    (hdiv : ∀ w : STime, divg V w = 0)
    (hmom : ∀ w : STime, dtime V w + adv V w = - grad P w + nu • lap V w)
    (a : Fin 3) (t : ℝ) :
    cellInt (fun x => dvec (1, 0) (fun w => V w a) (t, x)) = 0 := by
  have hVa : ContDiff ℝ (⊤ : ℕ∞) (fun w => V w a) := contDiff_coord V hV a
  have hVc : ∀ q : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V w q) := fun q => contDiff_coord V hV q
  have hVaper : SpacePeriodic (fun w => V w a) :=
    fun z j => congrArg (fun v : E3 => v a) (hVper z j)
  -- continuity of the three pieces
  have hcP : Continuous (fun x : E3 => dvec (0, ee a) P (t, x)) :=
    continuous_time_slice (continuous_dvec _ hP (0, ee a)) t
  have hcL : Continuous
      (fun x : E3 => ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) (t, x)) := by
    refine continuous_time_slice
      (f := fun w => ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) w) ?_ t
    exact continuous_finset_sum _ fun k _ =>
      continuous_dvec _ (contDiff_dvec _ hVa (0, ee k)) (0, ee k)
  have hcA : Continuous
      (fun x : E3 => ∑ j, V (t, x) j * dvec (0, ee j) (fun w => V w a) (t, x)) := by
    refine continuous_time_slice
      (f := fun w => ∑ j, V w j * dvec (0, ee j) (fun w => V w a) w) ?_ t
    exact continuous_finset_sum _ fun j _ =>
      (hVc j).continuous.mul (continuous_dvec _ hVa (0, ee j))
  -- the pointwise momentum identity, solved for the time derivative
  have hpt : ∀ x : E3, dvec (1, 0) (fun w => V w a) (t, x)
      = ((- dvec (0, ee a) P (t, x))
          + nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) (t, x))
        - ∑ j, V (t, x) j * dvec (0, ee j) (fun w => V w a) (t, x) := by
    intro x
    have h := congrFun (momentum_component nu V P hV hmom a) (t, x)
    simp only at h
    linarith
  have hcNP : Continuous (fun x : E3 => -dvec (0, ee a) P (t, x)) := hcP.neg
  have hcNu : Continuous
      (fun x : E3 => nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) (t, x)) :=
    continuous_const.mul hcL
  have hcSum : Continuous (fun x : E3 => -dvec (0, ee a) P (t, x)
      + nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) (t, x)) := hcNP.add hcNu
  rw [cellInt_congr hpt,
    cellInt_sub hcSum hcA,
    cellInt_add hcNP hcNu, cellInt_neg, cellInt_const_mul,
    cellInt_lap_comp_eq_zero hV hVper a t, cellInt_adv_comp_eq_zero hV hVper hdiv a t,
    cellInt_dvec_eq_zero P hP hPper a t]
  ring

/-- **The cell mean of the velocity is independent of time.** -/
theorem meanComp_eq (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P)
    (hdiv : ∀ w : STime, divg V w = 0)
    (hmom : ∀ w : STime, dtime V w + adv V w = - grad P w + nu • lap V w)
    (a : Fin 3) (t s : ℝ) : meanComp V t a = meanComp V s a := by
  have hVa : ContDiff ℝ (⊤ : ℕ∞) (fun w => V w a) := contDiff_coord V hV a
  have hderiv : ∀ r : ℝ, HasDerivAt (fun r : ℝ => meanComp V r a) 0 r := by
    intro r
    have h := hasDerivAt_cellInt (fun w => V w a) hVa r
    rwa [cellInt_dtime_comp_eq_zero (nu := nu) hV hP hVper hPper hdiv hmom a r] at h
  have hdiff : Differentiable ℝ (fun r : ℝ => meanComp V r a) :=
    fun r => (hderiv r).differentiableAt
  have hzero : ∀ r : ℝ, deriv (fun r : ℝ => meanComp V r a) r = 0 := fun r => (hderiv r).deriv
  exact is_const_of_deriv_eq_zero hdiff hzero t s

end Mean

/-! ## The coercive (Poincaré) energy estimate -/

/-- The Galilean-corrected energy: the squared `L²` distance of the velocity
from its (constant) mean. -/
def devEnergy (V : STime → E3) (m : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  cellInt (fun x => ∑ a, (V (t, x) a - m a)^2)

theorem devEnergy_nonneg (V : STime → E3) (m : Fin 3 → ℝ) (t : ℝ) : 0 ≤ devEnergy V m t :=
  cellInt_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `∫|u - m|² = 2E - |m|²` when `m` is the mean of `u`. -/
theorem devEnergy_eq (V : STime → E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (m : Fin 3 → ℝ) (t : ℝ)
    (hm : ∀ a, meanComp V t a = m a) :
    devEnergy V m t = 2 * energy V t - ∑ a, (m a)^2 := by
  have hVc : ∀ a : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V w a) := fun a => contDiff_coord V hV a
  have hcont : ∀ a : Fin 3, Continuous (fun x : E3 => V (t, x) a) :=
    fun a => continuous_time_slice (hVc a).continuous t
  have hcontsq : Continuous (fun x : E3 => ∑ a, V (t, x) a * V (t, x) a) :=
    continuous_finset_sum _ fun a _ => (hcont a).mul (hcont a)
  have hcontmix : Continuous (fun x : E3 => 2 * ∑ a, m a * V (t, x) a) :=
    continuous_const.mul (continuous_finset_sum _ fun a _ => continuous_const.mul (hcont a))
  have hpt : ∀ x : E3, (∑ a, (V (t, x) a - m a)^2)
      = ((∑ a, V (t, x) a * V (t, x) a) - 2 * ∑ a, m a * V (t, x) a) + ∑ a, (m a)^2 := by
    intro x
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hsq : cellInt (fun x => ∑ a, V (t, x) a * V (t, x) a) = 2 * energy V t := by
    have hpt2 : ∀ x : E3, (∑ a, V (t, x) a * V (t, x) a) = 2 * kin V (t, x) := by
      intro x
      simp only [kin, quad]
      ring
    rw [cellInt_congr hpt2, cellInt_const_mul]
    rfl
  have hmix : cellInt (fun x => 2 * ∑ a, m a * V (t, x) a) = 2 * ∑ a, (m a)^2 := by
    rw [cellInt_const_mul,
      cellInt_finset_sum Finset.univ (fun a x => m a * V (t, x) a)
        (fun a _ => continuous_const.mul (hcont a))]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [cellInt_const_mul, show cellInt (fun x => V (t, x) a) = meanComp V t a from rfl, hm a]
    ring
  rw [devEnergy, cellInt_congr hpt, cellInt_add (hcontsq.sub hcontmix) continuous_const,
    cellInt_sub hcontsq hcontmix, hsq, hmix, cellInt_const]
  ring

/-- **Coercivity of the dissipation on the torus.**  The mean-corrected energy is
controlled by the enstrophy. -/
theorem devEnergy_le_enstrophy (V : STime → E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hVper : SpacePeriodic V) (hdiv : ∀ w : STime, divg V w = 0) (m : Fin 3 → ℝ) (t : ℝ)
    (hm : ∀ a, meanComp V t a = m a) :
    devEnergy V m t ≤ 6 * enstrophy V t := by
  have hVc : ∀ a : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V w a) := fun a => contDiff_coord V hV a
  have hcont : ∀ a : Fin 3, Continuous (fun x : E3 => V (t, x) a) :=
    fun a => continuous_time_slice (hVc a).continuous t
  have hcontD : ∀ i a : Fin 3,
      Continuous (fun x : E3 => dvec (0, ee i) (fun w => V w a) (t, x)) :=
    fun i a => continuous_time_slice (continuous_dvec _ (hVc a) (0, ee i)) t
  -- componentwise Poincaré
  have hcomp : ∀ a : Fin 3, cellInt (fun x => (V (t, x) a - m a)^2)
      ≤ 3 * ∑ i, cellInt (fun x => (dvec (0, ee i) (fun w => V w a) (t, x))^2) := by
    intro a
    have hf : ContDiff ℝ 1 (fun y : E3 => V (t, y) a) :=
      (contDiff_slice (fun w => V w a) (hVc a) t).of_le (by exact_mod_cast le_top)
    have hmean : cellInt (fun y : E3 => V (t, y) a) = m a := hm a
    have hp := cellInt_poincare (fun y : E3 => V (t, y) a) hf
    rw [hmean] at hp
    have hd : ∀ (i : Fin 3) (x : E3),
        fderiv ℝ (fun y : E3 => V (t, y) a) x (ee i) = dvec (0, ee i) (fun w => V w a) (t, x) :=
      fun i x => fderiv_slice_apply (fun w => V w a)
        (differentiable_of_contDiffTop (hVc a)) t x (ee i)
    simpa only [hd] using hp
  have hsplit : devEnergy V m t = ∑ a, cellInt (fun x => (V (t, x) a - m a)^2) :=
    cellInt_finset_sum Finset.univ _ (fun a _ => ((hcont a).sub continuous_const).pow 2)
  have hstep : ∑ a, cellInt (fun x => (V (t, x) a - m a)^2)
      ≤ ∑ a, 3 * ∑ i, cellInt (fun x => (dvec (0, ee i) (fun w => V w a) (t, x))^2) :=
    Finset.sum_le_sum fun a _ => hcomp a
  have hgrad : ∑ a, 3 * ∑ i, cellInt (fun x => (dvec (0, ee i) (fun w => V w a) (t, x))^2)
      = 3 * cellInt (fun x => gradSq (fun a w => V w a) (t, x)) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    have h1 : ∀ i : Fin 3, ∑ a, cellInt (fun x => (dvec (0, ee i) (fun w => V w a) (t, x))^2)
        = cellInt (fun x => ∑ a, (dvec (0, ee i) (fun w => V w a) (t, x))^2) :=
      fun i => (cellInt_finset_sum Finset.univ _ (fun a _ => (hcontD i a).pow 2)).symm
    rw [Finset.sum_congr rfl fun i _ => h1 i]
    rw [← cellInt_finset_sum Finset.univ
      (fun i x => ∑ a, (dvec (0, ee i) (fun w => V w a) (t, x))^2)
      (fun i _ => continuous_finset_sum _ fun a _ => (hcontD i a).pow 2)]
    refine (cellInt_congr ?_).symm
    intro x
    simp only [gradSq]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring
  calc devEnergy V m t = ∑ a, cellInt (fun x => (V (t, x) a - m a)^2) := hsplit
    _ ≤ ∑ a, 3 * ∑ i, cellInt (fun x => (dvec (0, ee i) (fun w => V w a) (t, x))^2) := hstep
    _ = 3 * cellInt (fun x => gradSq (fun a w => V w a) (t, x)) := hgrad
    _ = 3 * (2 * enstrophy V t) := by rw [cellInt_gradSq_eq_two_enstrophy V hV hVper hdiv t]
    _ = 6 * enstrophy V t := by ring

/-! ## The Grönwall mechanism -/

/-- The Galilean-corrected energy `D(t) = E(t) - ½|m|²`, where `m` is the
(time-independent) cell mean of the velocity. -/
def devHalf (V : STime → E3) (t : ℝ) : ℝ := energy V t - (∑ a, (meanComp V 0 a)^2)/2

section Gronwall

variable {nu : ℝ} {V : STime → E3} {P : STime → ℝ}

lemma devEnergy_eq_two_devHalf (hsol : IsAncientNSSolution nu V P) (t : ℝ) :
    devEnergy V (fun a => meanComp V 0 a) t = 2 * devHalf V t := by
  obtain ⟨hV, hP, hVper, hPper, hmom, hdiv⟩ := hsol
  have hm : ∀ a, meanComp V t a = meanComp V 0 a := fun a =>
    meanComp_eq (nu := nu) hV hP hVper hPper hdiv hmom a t 0
  rw [devEnergy_eq V hV _ t hm, devHalf]
  ring

lemma devHalf_nonneg (hsol : IsAncientNSSolution nu V P) (t : ℝ) : 0 ≤ devHalf V t := by
  have h := devEnergy_nonneg V (fun a => meanComp V 0 a) t
  rw [devEnergy_eq_two_devHalf hsol t] at h
  linarith

/-- Poincaré coercivity in the form used by the Grönwall step. -/
lemma devHalf_le_enstrophy (hsol : IsAncientNSSolution nu V P) (t : ℝ) :
    devHalf V t ≤ 3 * enstrophy V t := by
  obtain ⟨hV, hP, hVper, hPper, hmom, hdiv⟩ := hsol
  have hm : ∀ a, meanComp V t a = meanComp V 0 a := fun a =>
    meanComp_eq (nu := nu) hV hP hVper hPper hdiv hmom a t 0
  have h := devEnergy_le_enstrophy V hV hVper hdiv (fun a => meanComp V 0 a) t hm
  rw [devEnergy_eq_two_devHalf ⟨hV, hP, hVper, hPper, hmom, hdiv⟩ t] at h
  linarith

lemma hasDerivAt_devHalf (hsol : IsAncientNSSolution nu V P) (t : ℝ) :
    HasDerivAt (devHalf V) (-(2*nu*enstrophy V t)) t := by
  obtain ⟨hV, hP, hVper, hPper, hmom, hdiv⟩ := hsol
  exact (energy_balance_enstrophy nu V P hV hP hVper hPper hdiv hmom t).sub_const _

/-- **The exponential Lyapunov functional.**  With `k = 2ν/3`, the quantity
`e^{kt} D(t)` is nonincreasing in time. -/
theorem exp_devHalf_antitone (hnu : 0 < nu) (hsol : IsAncientNSSolution nu V P) :
    Antitone (fun t : ℝ => Real.exp ((2*nu/3)*t) * devHalf V t) := by
  set k : ℝ := 2*nu/3 with hk
  have hWderiv : ∀ t, HasDerivAt (fun t : ℝ => Real.exp (k*t) * devHalf V t)
      (k * Real.exp (k*t) * devHalf V t + Real.exp (k*t) * (-(2*nu*enstrophy V t))) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (k*t)) (Real.exp (k*t) * k) t := by
      simpa using (((hasDerivAt_id t).const_mul k).exp)
    have h2 := h1.mul (hasDerivAt_devHalf hsol t)
    have heq : Real.exp (k*t) * k * devHalf V t + Real.exp (k*t) * (-(2*nu*enstrophy V t))
        = k * Real.exp (k*t) * devHalf V t + Real.exp (k*t) * (-(2*nu*enstrophy V t)) := by
      ring
    rw [heq] at h2
    exact h2
  refine antitone_of_deriv_nonpos (fun t => (hWderiv t).differentiableAt) fun t => ?_
  rw [(hWderiv t).deriv]
  have hexp : 0 < Real.exp (k*t) := Real.exp_pos _
  have h1 : k * devHalf V t ≤ 2*nu*enstrophy V t := by
    have := devHalf_le_enstrophy hsol t
    rw [hk]
    nlinarith
  nlinarith [hexp, h1]

/-- Vanishing of the corrected energy at a time pins the velocity to its mean. -/
theorem velocity_eq_mean (hsol : IsAncientNSSolution nu V P) (t : ℝ) (h : devHalf V t = 0)
    (x : E3) : V (t, x) = ∑ a, (meanComp V 0 a) • ee a := by
  obtain ⟨hV, hP, hVper, hPper, hmom, hdiv⟩ := hsol
  set m : Fin 3 → ℝ := fun a => meanComp V 0 a with hmdef
  have hdev : devEnergy V m t = 0 := by
    rw [devEnergy_eq_two_devHalf ⟨hV, hP, hVper, hPper, hmom, hdiv⟩ t, h]
    ring
  have hbcomp : ∀ a : Fin 3, (∑ q, (m q) • ee q : E3) a = m a := by
    intro a
    simp [ee, Pi.single_apply]
  have hVc : ∀ a : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V w a) := fun a => contDiff_coord V hV a
  have hcont : Continuous (fun y : E3 => ∑ a, (V (t, y) a - m a)^2) :=
    continuous_finset_sum _ fun a _ =>
      (((continuous_time_slice (hVc a).continuous t).sub continuous_const).pow 2)
  have hnn : ∀ y : E3, 0 ≤ ∑ a, (V (t, y) a - m a)^2 :=
    fun y => Finset.sum_nonneg fun a _ => sq_nonneg _
  have hper : ∀ (y : E3) (j : Fin 3),
      (∑ a, (V (t, y + ee j) a - m a)^2) = ∑ a, (V (t, y) a - m a)^2 := by
    intro y j
    have hy := hVper (t, y) j
    simp only at hy
    rw [hy]
  have hzero := eq_zero_of_cellInt_eq_zero hcont hnn hper hdev x
  have hcomp : ∀ a : Fin 3, V (t, x) a = m a := by
    intro a
    have hterm : (V (t, x) a - m a)^2 = 0 := by
      have hsum : ∀ b ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ (V (t, x) b - m b)^2 :=
        fun b _ => sq_nonneg _
      exact (Finset.sum_eq_zero_iff_of_nonneg hsum).mp hzero a (Finset.mem_univ a)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hterm
    linarith
  ext a
  rw [hcomp a, hbcomp a]

end Gronwall

/-! ## Exponential relaxation to the mean flow

A by-product of the same mechanism, running *forwards* in time: on the torus and
with zero force, any smooth periodic solution relaxes to its (constant) mean at
the explicit exponential rate `2ν/3`. -/

theorem devHalf_exp_decay {nu : ℝ} {V : STime → E3} {P : STime → ℝ} (hnu : 0 < nu)
    (hsol : IsAncientNSSolution nu V P) {s t : ℝ} (hst : s ≤ t) :
    devHalf V t ≤ Real.exp (-(2*nu/3)*(t-s)) * devHalf V s := by
  have h := exp_devHalf_antitone hnu hsol hst
  simp only at h
  have hexp : 0 < Real.exp ((2*nu/3)*t) := Real.exp_pos _
  have hprod : Real.exp (-(2*nu/3)*(t-s)) * Real.exp ((2*nu/3)*t)
      = Real.exp ((2*nu/3)*s) := by
    rw [← Real.exp_add]
    ring_nf
  calc devHalf V t
      = (Real.exp ((2*nu/3)*t) * devHalf V t) / Real.exp ((2*nu/3)*t) := by
        field_simp
    _ ≤ (Real.exp ((2*nu/3)*s) * devHalf V s) / Real.exp ((2*nu/3)*t) := by
        exact div_le_div_of_nonneg_right h hexp.le
    _ = Real.exp (-(2*nu/3)*(t-s)) * devHalf V s := by
        rw [← hprod]
        field_simp

/-! ## The Liouville theorem -/

/-- **Liouville theorem for bounded ancient periodic Navier–Stokes solutions.**
A smooth `ℤ³`-periodic solution defined for all times whose cell energy is
bounded is a constant vector field. -/
theorem ancient_periodic_liouville (nu : ℝ) (hnu : 0 < nu) (V : STime → E3) (P : STime → ℝ)
    (hsol : IsAncientNSSolution nu V P) (M : ℝ) (hbdd : ∀ t : ℝ, energy V t ≤ M) :
    ∃ b : E3, ∀ z : STime, V z = b := by
  set k : ℝ := 2*nu/3 with hk
  have hkpos : 0 < k := by rw [hk]; positivity
  set S : ℝ := ∑ a, (meanComp V 0 a)^2 with hS
  set M' : ℝ := max (M - S/2) 0 with hM'
  have hM'nn : 0 ≤ M' := le_max_right _ _
  have hDM' : ∀ s, devHalf V s ≤ M' := by
    intro s
    refine le_trans ?_ (le_max_left (M - S/2) 0)
    have h := hbdd s
    rw [devHalf, ← hS]
    linarith
  have hanti := exp_devHalf_antitone hnu hsol
  have hlim : Filter.Tendsto (fun s : ℝ => Real.exp (k*s) * M') Filter.atBot (nhds 0) := by
    have h1 : Filter.Tendsto (fun s : ℝ => k*s) Filter.atBot Filter.atBot :=
      Filter.Tendsto.const_mul_atBot hkpos Filter.tendsto_id
    have h2 := Real.tendsto_exp_atBot.comp h1
    simpa using h2.mul_const M'
  have hDzero : ∀ t, devHalf V t = 0 := by
    intro t
    have hle : Real.exp (k*t) * devHalf V t ≤ 0 := by
      refine ge_of_tendsto hlim ?_
      filter_upwards [Filter.eventually_le_atBot t] with s hs
      have hexp : 0 < Real.exp (k*s) := Real.exp_pos _
      have hstep := hanti hs
      simp only [← hk] at hstep
      calc Real.exp (k*t) * devHalf V t ≤ Real.exp (k*s) * devHalf V s := hstep
        _ ≤ Real.exp (k*s) * M' := by nlinarith [hDM' s]
    have hexp : 0 < Real.exp (k*t) := Real.exp_pos _
    have h := devHalf_nonneg hsol t
    nlinarith
  exact ⟨∑ a, (meanComp V 0 a) • ee a,
    fun z => velocity_eq_mean hsol z.1 (hDzero z.1) z.2⟩


/-! ## The sup-norm formulation

Koch–Nadirashvili–Seregin–Šverák state the Liouville problem for solutions that
are bounded in the *sup* norm.  On the torus a sup bound implies an energy
bound, so the theorem applies verbatim in that formulation. -/

/-- On the cell, `∑ a (v a)² = ‖v‖²`. -/
lemma sum_sq_eq_norm_sq (v : E3) : ∑ a, v a * v a = ‖v‖^2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl fun a _ => by rw [Real.norm_eq_abs, sq_abs]; ring

/-- A uniform sup bound on the velocity gives a uniform bound on the cell energy. -/
theorem energy_le_of_norm_le (V : STime → E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (K : ℝ)
    (hK : ∀ z : STime, ‖V z‖ ≤ K) (t : ℝ) : energy V t ≤ K^2/2 := by
  have hVc : ∀ a : Fin 3, Continuous (fun w : STime => V w a) :=
    fun a => (contDiff_coord V hV a).continuous
  have hkin : Continuous (fun w : STime => kin V w) := by
    simp only [kin, quad]
    exact continuous_const.mul (continuous_finset_sum _ fun a _ => (hVc a).mul (hVc a))
  have hpt : ∀ x : E3, kin V (t, x) ≤ K^2/2 := by
    intro x
    have h1 : kin V (t, x) = ‖V (t, x)‖^2 / 2 := by
      simp only [kin, quad, sum_sq_eq_norm_sq]
      ring
    have h2 : ‖V (t, x)‖ ≤ K := hK (t, x)
    have h3 : (0 : ℝ) ≤ ‖V (t, x)‖ := norm_nonneg _
    nlinarith
  have := cellInt_mono (continuous_time_slice hkin t) (continuous_const (y := K^2/2)) hpt
  simpa [energy, cellInt_const] using this

/-- **Liouville theorem, sup-norm form.**  A smooth `ℤ³`-periodic Navier–Stokes
solution defined for all times whose velocity is uniformly bounded is constant. -/
theorem ancient_periodic_liouville_of_norm_le (nu : ℝ) (hnu : 0 < nu) (V : STime → E3)
    (P : STime → ℝ) (hsol : IsAncientNSSolution nu V P) (K : ℝ)
    (hK : ∀ z : STime, ‖V z‖ ≤ K) : ∃ b : E3, ∀ z : STime, V z = b :=
  ancient_periodic_liouville nu hnu V P hsol (K^2/2)
    (fun t => energy_le_of_norm_le V hsol.smoothVelocity K hK t)


end ClayNS
