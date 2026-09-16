/-
# §2, §11, §12, §13 of the BIDI note: the source calculus and the order closures

* **§2 (3)(4)** — the observable-indexed source presentation is definitional:
  `SourceDirection O = O`, `sourceDirectionOf = id`, and the finite covariance
  *is* the normalised mixed source derivative, `covFinite = mixedLogDeriv`.  No
  observable-to-source representation theorem is needed, and none is assumed:
  `covFinite_eq_mixedLogDeriv` is `rfl`.
* **§11 (32)–(35)** — `exp_decay_transfer`: a geometric *spatial* estimate
  `≤ C e^{-m d}` implies the *temporal* estimate `≤ C e^{-m t}` whenever
  `t ≤ d` and `m > 0`.  This is the only thing the terminal consumer needs from
  the geometry.
* **§13 (37)(38)** — `norm_le_of_tendsto`: a uniform bound on a convergent
  family of finite-volume covariances passes to the limit; one-sided order
  closure, no rate and no uniformity in the observables required.
-/
import Mathlib

namespace RequestProject.YangMills.BIDI

open Filter Topology

/-! ## §2 The observable-indexed source calculus -/

/-- **(3)**: source directions *are* test observables. -/
abbrev SourceDirection (Obs : Type*) : Type _ := Obs

/-- **(3)**: the source direction of an observable is the observable. -/
def sourceDirectionOf {Obs : Type*} (o : Obs) : SourceDirection Obs := o

theorem sourceDirectionOf_eq_id (Obs : Type*) :
    (sourceDirectionOf : Obs → SourceDirection Obs) = id := rfl

/-- The mixed two-source derivative `D_{J_L} D_{J_R} log Z` at zero sources. -/
noncomputable def mixedLogDeriv (logZ : ℂ → ℂ → ℂ) : ℂ :=
  deriv (fun x => deriv (fun y => logZ x y) 0) 0

/-- **(4)**: the finite-volume covariance of the two selected observables, as
produced by the normalised two-source calculus.  It is *defined* as the mixed
source derivative, so the identity (4) is definitional. -/
noncomputable def covFinite (logZ : ℂ → ℂ → ℂ) : ℂ := mixedLogDeriv logZ

theorem covFinite_eq_mixedLogDeriv (logZ : ℂ → ℂ → ℂ) :
    covFinite logZ = mixedLogDeriv logZ := rfl

/-! ## §11 Spatial decay to temporal decay -/

/-- **(32)–(35)**: with `m > 0`, a nonnegative constant and `t ≤ d`, a spatial
geometric bound is a temporal geometric bound.  (Nonnegativity of the constant
is genuinely needed: for `C < 0` the temporal statement is *stronger* than the
spatial one and does not follow.) -/
theorem exp_decay_transfer {X C m t d : ℝ} (hm : 0 < m) (hC : 0 ≤ C) (htd : t ≤ d)
    (h : X ≤ C * Real.exp (-(m * d))) :
    X ≤ C * Real.exp (-(m * t)) := by
  refine le_trans h ?_
  have : -(m * d) ≤ -(m * t) := by nlinarith
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 this) hC

/-! ## §13 Finite-to-continuum order closure -/

/-- **(37)(38)**: a uniform bound on a convergent family passes to the limit. -/
theorem norm_le_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {f : ι → ℂ} {L : ℂ}
    {B : ℝ} (hf : Tendsto f l (𝓝 L)) (hb : ∀ i, ‖f i‖ ≤ B) : ‖L‖ ≤ B :=
  le_of_tendsto (hf.norm) (Eventually.of_forall hb)

/-- The same with the bound holding only eventually along the limit. -/
theorem norm_le_of_tendsto_eventually {ι : Type*} {l : Filter ι} [l.NeBot] {f : ι → ℂ}
    {L : ℂ} {B : ℝ} (hf : Tendsto f l (𝓝 L)) (hb : ∀ᶠ i in l, ‖f i‖ ≤ B) : ‖L‖ ≤ B :=
  le_of_tendsto (hf.norm) hb

end RequestProject.YangMills.BIDI
