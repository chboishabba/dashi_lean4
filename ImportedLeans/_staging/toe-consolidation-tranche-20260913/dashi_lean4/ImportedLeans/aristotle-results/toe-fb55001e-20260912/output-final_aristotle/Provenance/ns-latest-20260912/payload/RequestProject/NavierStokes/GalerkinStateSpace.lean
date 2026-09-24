/-
# The finite Galerkin state space and its quadratic vector field

The Galerkin lane of this development works with the structure
`ClayNS.Waleffe.GalerkinFlow`, which *postulates* a differentiable trajectory
solving the truncated Navier–Stokes system

  `u̇_k = −ν|k|² u_k + f_k(u)`,  `f_k(u) = −P_k ((u·∇)u)^_k`,

on a finite mode set.  Nothing in the development so far constructs such a
trajectory: the time derivative is an assumption of the structure.

This file is the first of three that remove that assumption.  Here we

* realise the truncated Fourier field as a point of the finite-dimensional real
  normed space `State modes = ↥modes → (Fin 3 → ℂ)` (`spread` extends a state to
  a field on the whole lattice by zero);
* define the literal Galerkin vector field `vfield` on that space, whose value
  is exactly the right-hand side appearing in `GalerkinFlow.ode`;
* prove that this vector field is `C^∞` — it is a polynomial of degree two in
  the real coordinates, the Leray projection contributing only constant
  denominators `|k|² ≠ 0`;
* record the energy `en` as a smooth function of the state and the smooth
  cutoff `cut R` which equals `1` where `en ≤ R` and vanishes where
  `en ≥ R + 1`.

No analytic input is assumed: everything here is finite-dimensional calculus.
-/
import RequestProject.NavierStokes.WaleffeGalerkinEnergy
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

noncomputable section

open Set

namespace ClayNS.GalerkinODE

open ClayNS.Waleffe

variable (modes : Finset Wave)

/-! ## The state space -/

/-- The state space of the Galerkin truncation: one complex 3-vector per
retained mode.  As a finite product of finite-dimensional real normed spaces it
is a finite-dimensional real Banach space. -/
abbrev State (modes : Finset Wave) := ↥modes → Fin 3 → ℂ

/-- Extend a state to a Fourier field on the whole lattice by zero. -/
def spread (v : State modes) : Wave → Fin 3 → ℂ :=
  fun k => if h : k ∈ modes then v ⟨k, h⟩ else 0

variable {modes}

@[simp] theorem spread_of_mem (v : State modes) {k : Wave} (h : k ∈ modes) :
    spread modes v k = v ⟨k, h⟩ := dif_pos h

@[simp] theorem spread_coe (v : State modes) (k : ↥modes) :
    spread modes v (k : Wave) = v k := by
  simp [spread]

theorem spread_of_not_mem (v : State modes) {k : Wave} (h : k ∉ modes) :
    spread modes v k = 0 := dif_neg h

variable (modes)

/-- Every coordinate of the extended field is a smooth (indeed continuous
linear) function of the state. -/
theorem contDiff_spread_coord (k : Wave) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun v : State modes => spread modes v k i) := by
  unfold spread
  split
  · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) i).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥modes => Fin 3 → ℂ) _)).contDiff
  · exact contDiff_const

/-! ## The literal Galerkin vector field -/

/-- The literal right-hand side of the truncated Navier–Stokes system, as a
vector field on the finite-dimensional state space:
`v ↦ (k ↦ −ν|k|² v_k + f_k(v))` with `f` the projected advective forcing. -/
def vfield (nu : ℝ) (v : State modes) : State modes :=
  fun k i => -((nu * wsq (k : Wave) : ℝ) : ℂ) * spread modes v (k : Wave) i
      + modalForcing modes (spread modes v) (k : Wave) i

variable {modes}

theorem vfield_apply (nu : ℝ) (v : State modes) (k : ↥modes) (i : Fin 3) :
    vfield modes nu v k i
      = -((nu * wsq (k : Wave) : ℝ) : ℂ) * spread modes v (k : Wave) i
        + modalForcing modes (spread modes v) (k : Wave) i := rfl

variable (modes)

/-- **The Galerkin vector field is smooth.**  It is a degree-two polynomial in
the real coordinates of the state: the viscous part is linear, the advective
part is bilinear, and the Leray projection divides only by the constants
`|k|²`. -/
theorem contDiff_vfield (nu : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (vfield modes nu) := by
  rw [contDiff_pi]
  intro k
  rw [contDiff_pi]
  intro i
  have hadv : ∀ (m : Wave) (j : Fin 3),
      ContDiff ℝ (⊤ : ℕ∞) (fun v : State modes => advection modes (spread modes v) m j) := by
    intro m j
    unfold advection
    refine ContDiff.sum fun p _ => ?_
    refine ContDiff.mul ?_ (contDiff_spread_coord modes (m - p) j)
    refine ContDiff.mul contDiff_const ?_
    exact ContDiff.sum fun q _ => (contDiff_spread_coord modes p q).mul contDiff_const
  have hforce : ∀ (m : Wave) (j : Fin 3),
      ContDiff ℝ (⊤ : ℕ∞) (fun v : State modes => modalForcing modes (spread modes v) m j) := by
    intro m j
    unfold modalForcing leray
    refine ContDiff.neg ?_
    refine ContDiff.sub (hadv m j) ?_
    refine ContDiff.mul ?_ contDiff_const
    refine ContDiff.div_const ?_ _
    unfold herm
    exact ContDiff.sum fun q _ => ContDiff.mul contDiff_const (hadv m q)
  exact ContDiff.add (ContDiff.mul contDiff_const (contDiff_spread_coord modes _ i))
    (hforce (k : Wave) i)

/-! ## Energy as a smooth function of the state -/

/-- The Galerkin energy of a state. -/
def en (v : State modes) : ℝ := ∑ k : ↥modes, nsq (v k)

variable {modes}

theorem en_nonneg (v : State modes) : 0 ≤ en modes v :=
  Finset.sum_nonneg fun k _ => nsq_nonneg (v k)

theorem en_spread (v : State modes) : en modes v = ∑ k ∈ modes, nsq (spread modes v k) := by
  rw [en, ← Finset.sum_coe_sort modes fun k => nsq (spread modes v k)]
  exact Finset.sum_congr rfl fun k _ => by rw [spread_coe]

variable (modes)

theorem contDiff_en : ContDiff ℝ (⊤ : ℕ∞) (en modes) := by
  unfold en
  refine ContDiff.sum fun k _ => ?_
  unfold nsq
  refine ContDiff.sum fun i _ => ?_
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun v : State modes => v k i) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) i).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥modes => Fin 3 → ℂ) k)).contDiff
  have hre : ContDiff ℝ (⊤ : ℕ∞) (fun v : State modes => (v k i).re) :=
    Complex.reCLM.contDiff.comp h
  have him : ContDiff ℝ (⊤ : ℕ∞) (fun v : State modes => (v k i).im) :=
    Complex.imCLM.contDiff.comp h
  simpa [Complex.normSq_apply] using (hre.mul hre).add (him.mul him)

/-! ## The smooth energy cutoff -/

/-- A smooth cutoff of the state space: it equals `1` where the energy is at
most `R` and vanishes where the energy is at least `R + 1`. -/
def cut (R : ℝ) (v : State modes) : ℝ := Real.smoothTransition (R + 1 - en modes v)

variable {modes}

theorem cut_nonneg (R : ℝ) (v : State modes) : 0 ≤ cut modes R v :=
  Real.smoothTransition.nonneg _

theorem cut_le_one (R : ℝ) (v : State modes) : cut modes R v ≤ 1 :=
  Real.smoothTransition.le_one _

theorem cut_eq_one {R : ℝ} {v : State modes} (h : en modes v ≤ R) : cut modes R v = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem cut_eq_zero {R : ℝ} {v : State modes} (h : R + 1 ≤ en modes v) : cut modes R v = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

variable (modes)

theorem contDiff_cut (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (cut modes R) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_en modes))

/-- The truncated Galerkin vector field: the literal field multiplied by the
smooth energy cutoff.  It agrees with `vfield` on states of energy at most `R`
and vanishes on states of energy at least `R + 1`. -/
def tvfield (nu R : ℝ) (v : State modes) : State modes := cut modes R v • vfield modes nu v

variable {modes}

theorem tvfield_eq_vfield {nu R : ℝ} {v : State modes} (h : en modes v ≤ R) :
    tvfield modes nu R v = vfield modes nu v := by
  rw [tvfield, cut_eq_one h, one_smul]

theorem tvfield_eq_zero {nu R : ℝ} {v : State modes} (h : R + 1 ≤ en modes v) :
    tvfield modes nu R v = 0 := by
  rw [tvfield, cut_eq_zero h, zero_smul]

variable (modes)

theorem contDiff_tvfield (nu R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (tvfield modes nu R) :=
  (contDiff_cut modes R).smul (contDiff_vfield modes nu)

variable {modes}

end ClayNS.GalerkinODE
