/-
# Assembling window solutions into a global one

This file discharges the remaining *plumbing* obligation of `OpenGates.lean`:
`ClayNS.GlobalAssemblyGate`, i.e. that local existence, uniqueness on windows,
continuation and the absence of velocity blow-up together give the literal Clay
periodic target `ClayNS.ClayPeriodicTargetB`.

The two analytic ingredients are

* pressure normalization — the pressure of a window solution is determined by
  the velocity up to a function of time, so normalizing `P(t,0) = 0` makes
  window solutions with the same datum *literally* unique, pressure included;
* gluing — a family of normalized window solutions with the same datum is
  locally, around every spacetime point, equal to a single member of the
  family, so the glued field is smooth and solves the system.

Then a supremum argument over the set of reachable window lengths, using
continuation and the absence of velocity blow-up, shows that every length is
reachable, and a final gluing produces the global solution.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.WindowUniqueness

open scoped BigOperators
open MeasureTheory Set

noncomputable section

namespace ClayNS

/-! ## Slices of a spacetime field -/

/-- **A field with vanishing spatial gradient at time `t` is constant in
space.** -/
lemma slice_const_of_spatial_grad_zero {F : STime → ℝ} (hF : Differentiable ℝ F) (t : ℝ)
    (h0 : ∀ (x : E3) (j : Fin 3), dvec (0, ee j) F (t, x) = 0) (x : E3) :
    F (t, x) = F (t, 0) := by
  have hdiff : Differentiable ℝ (fun y : E3 => F (t, y)) := fun y =>
    (hasFDerivAt_slice F hF t y).differentiableAt
  have hzero : ∀ y : E3, fderiv ℝ (fun y : E3 => F (t, y)) y = 0 := by
    intro y
    rw [(hasFDerivAt_slice F hF t y).fderiv]
    ext m
    have hexp : fderiv ℝ F (t, y) (0, m) = ∑ i, (m i) • dspace F i (t, y) :=
      fderiv_space_vector F (t, y) m
    have : ∀ i : Fin 3, dspace F i (t, y) = 0 := fun i => h0 y i
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.inr_apply]
    rw [hexp]
    simp [this]
  exact is_const_of_fderiv_eq_zero hdiff hzero x 0

/-! ## Pressure normalization -/

/-- The linear map `z ↦ (z.1, 0)` onto the time axis. -/
def timeAxis : STime →L[ℝ] STime :=
  (ContinuousLinearMap.inl ℝ ℝ E3).comp (ContinuousLinearMap.fst ℝ ℝ E3)

@[simp] lemma timeAxis_apply (z : STime) : timeAxis z = (z.1, 0) := rfl

lemma contDiff_gauge {P : STime → ℝ} (hP : ContDiff ℝ (⊤ : ℕ∞) P) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : STime => P z - P (z.1, 0)) :=
  hP.sub (hP.comp timeAxis.contDiff)

lemma dvec_space_gauge {P : STime → ℝ} (hP : ContDiff ℝ (⊤ : ℕ∞) P) (i : Fin 3) (z : STime) :
    dvec (0, ee i) (fun w : STime => P w - P (w.1, 0)) z = dvec (0, ee i) P z := by
  have hPd : Differentiable ℝ P := differentiable_of_contDiffTop hP
  have hc : HasFDerivAt (fun w : STime => P (w.1, 0))
      ((fderiv ℝ P (z.1, 0)).comp timeAxis) z :=
    (hPd (z.1, 0)).hasFDerivAt.comp z timeAxis.hasFDerivAt
  have hsub := dvec_sub P (fun w : STime => P (w.1, 0)) z (hPd z) hc.differentiableAt (0, ee i)
  have hzero : dvec (0, ee i) (fun w : STime => P (w.1, 0)) z = 0 := by
    rw [dvec, hc.fderiv]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, timeAxis_apply]
    exact map_zero _
  rw [hsub, hzero, sub_zero]

lemma grad_gauge {P : STime → ℝ} (hP : ContDiff ℝ (⊤ : ℕ∞) P) (z : STime) :
    grad (fun w : STime => P w - P (w.1, 0)) z = grad P z :=
  Finset.sum_congr rfl fun i _ => by
    rw [show dspace (fun w : STime => P w - P (w.1, 0)) i z
      = dvec (0, ee i) (fun w : STime => P w - P (w.1, 0)) z from rfl,
      dvec_space_gauge hP i z]
    rfl

/-- A window solution whose pressure gauge is fixed by `P(t,0) = 0`. -/
structure NormalizedWindow (nu T : ℝ) (u₀ : E3 → E3) (V : STime → E3) (P : STime → ℝ) : Prop where
  sol : IsNSSolutionOn nu T V P
  datum : ∀ x : E3, V (0, x) = u₀ x
  gauge : ∀ t : ℝ, P (t, 0) = 0

/-- **Every window solution can be normalized.**  Subtracting the value of the
pressure on the time axis changes neither the velocity nor the equations. -/
theorem exists_normalized_window {nu T : ℝ} {u₀ : E3 → E3} {V : STime → E3} {P : STime → ℝ}
    (hsol : IsNSSolutionOn nu T V P) (hdat : ∀ x : E3, V (0, x) = u₀ x) :
    ∃ Q : STime → ℝ, NormalizedWindow nu T u₀ V Q := by
  refine ⟨fun z => P z - P (z.1, 0), ?_⟩
  refine ⟨⟨hsol.smoothVelocity, contDiff_gauge hsol.smoothPressure, hsol.periodicVelocity,
    ?_, ?_, hsol.incompressible⟩, hdat, ?_⟩
  · intro z j
    show P (z.1, z.2 + ee j) - P ((z.1, z.2 + ee j).1, 0) = P z - P (z.1, 0)
    rw [hsol.periodicPressure z j]
  · intro z hz hzT
    rw [grad_gauge hsol.smoothPressure z]
    exact hsol.momentum z hz hzT
  · intro t
    simp

/-! ## Derivatives only see a neighbourhood -/

/-- Two fields that agree on an open set have the same time derivative,
advection and Laplacian there. -/
lemma derivs_eq_of_eqOn_open {V V' : STime → E3} {U : Set STime} (hU : IsOpen U)
    (heq : EqOn V V' U) {z : STime} (hz : z ∈ U) :
    dtime V z = dtime V' z ∧ adv V z = adv V' z ∧ lap V z = lap V' z := by
  have hfd : ∀ w ∈ U, fderiv ℝ V w = fderiv ℝ V' w := fun w hw =>
    (heq.eventuallyEq_of_mem (hU.mem_nhds hw)).fderiv_eq
  have hdsp : ∀ (i : Fin 3), EqOn (fun w => dspace V i w) (fun w => dspace V' i w) U := by
    intro i w hw
    show fderiv ℝ V w (0, ee i) = fderiv ℝ V' w (0, ee i)
    rw [hfd w hw]
  refine ⟨?_, ?_, ?_⟩
  · show fderiv ℝ V z (1, 0) = fderiv ℝ V' z (1, 0)
    rw [hfd z hz]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [heq hz]
    exact congrArg (fun s : E3 => (V' z).ofLp i • s) (hdsp i hz)
  · refine Finset.sum_congr rfl fun i _ => ?_
    show fderiv ℝ (fun w => dspace V i w) z (0, ee i)
      = fderiv ℝ (fun w => dspace V' i w) z (0, ee i)
    rw [((hdsp i).eventuallyEq_of_mem (hU.mem_nhds hz)).fderiv_eq]

/-! ## Uniqueness of normalized window solutions -/

/-- The `i`-th component of a gradient is the `i`-th spatial derivative. -/
lemma grad_apply (P : STime → ℝ) (z : STime) (i : Fin 3) : grad P z i = dspace P i z := by
  simp [grad, ee, Pi.single_apply]

/-- **Normalized window solutions with the same datum coincide**, velocity and
pressure, on the common window. -/
theorem normalizedWindow_unique {nu T T' : ℝ} {u₀ : E3 → E3} {V V' : STime → E3}
    {P P' : STime → ℝ} (hnu : 0 < nu) (hT : 0 < T) (hT' : 0 < T')
    (h : NormalizedWindow nu T u₀ V P) (h' : NormalizedWindow nu T' u₀ V' P')
    {z : STime} (hz : 0 ≤ z.1) (hzT : z.1 < T) (hzT' : z.1 < T') :
    V z = V' z ∧ P z = P' z := by
  set m : ℝ := min T T' with hm
  have hmpos : 0 < m := lt_min hT hT'
  -- velocities agree on the common window
  have hvel : ∀ w : STime, 0 ≤ w.1 → w.1 < m → V w = V' w := by
    rintro ⟨t, x⟩ hw hwm
    exact velocity_eq_of_same_datum_on nu m V V' P P'
      h.sol.smoothVelocity h'.sol.smoothVelocity h.sol.smoothPressure h'.sol.smoothPressure
      h.sol.periodicVelocity h'.sol.periodicVelocity h.sol.periodicPressure h'.sol.periodicPressure
      hnu.le
      (fun w hw0 hwm => h.sol.incompressible w hw0 (lt_of_lt_of_le hwm (min_le_left _ _)))
      (fun w hw0 hwm => h'.sol.incompressible w hw0 (lt_of_lt_of_le hwm (min_le_right _ _)))
      (fun w hw0 hwm => h.sol.momentum w hw0 (lt_of_lt_of_le hwm (min_le_left _ _)))
      (fun w hw0 hwm => h'.sol.momentum w hw0 (lt_of_lt_of_le hwm (min_le_right _ _)))
      (fun x => by rw [h.datum x, h'.datum x]) hw hwm x
  -- pressures agree at interior times
  have hUopen : IsOpen {w : STime | 0 < w.1 ∧ w.1 < m} :=
    (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
  have hgrad : ∀ w : STime, 0 < w.1 → w.1 < m → grad P w = grad P' w := by
    intro w hw0 hwm
    have hmem : w ∈ {w : STime | 0 < w.1 ∧ w.1 < m} := ⟨hw0, hwm⟩
    obtain ⟨hdt, hadv, hlap⟩ := derivs_eq_of_eqOn_open hUopen
      (fun y hy => hvel y hy.1.le hy.2) hmem
    have h1 := h.sol.momentum w hw0.le (lt_of_lt_of_le hwm (min_le_left _ _))
    have h2 := h'.sol.momentum w hw0.le (lt_of_lt_of_le hwm (min_le_right _ _))
    rw [hdt, hadv, hlap] at h1
    have : - grad P w = - grad P' w := by
      exact add_right_cancel (h1.symm.trans h2)
    simpa using congrArg Neg.neg this
  have hPint : ∀ (t : ℝ), 0 < t → t < m → ∀ x : E3, P (t, x) = P' (t, x) := by
    intro t ht htm x
    have hzero : ∀ (y : E3) (j : Fin 3),
        dvec (0, ee j) (fun w : STime => P w - P' w) (t, y) = 0 := by
      intro y j
      have hg := congrFun (congrArg (fun v : E3 => (v : Fin 3 → ℝ)) (hgrad (t, y) ht htm)) j
      have hPP : dspace P j (t, y) = dspace P' j (t, y) := by
        rw [← grad_apply P (t, y) j, ← grad_apply P' (t, y) j]
        exact hg
      have := dvec_sub P P' (t, y)
        ((differentiable_of_contDiffTop h.sol.smoothPressure) (t, y))
        ((differentiable_of_contDiffTop h'.sol.smoothPressure) (t, y)) (0, ee j)
      rw [this]
      show dspace P j (t, y) - dspace P' j (t, y) = 0
      rw [hPP, sub_self]
    have hFd : Differentiable ℝ (fun w : STime => P w - P' w) := fun w =>
      ((differentiable_of_contDiffTop h.sol.smoothPressure) w).sub
        ((differentiable_of_contDiffTop h'.sol.smoothPressure) w)
    have hconst := slice_const_of_spatial_grad_zero hFd t hzero x
    have hval : P (t, x) - P' (t, x) = P (t, 0) - P' (t, 0) := hconst
    have h0 : P (t, 0) - P' (t, 0) = 0 := by rw [h.gauge t, h'.gauge t, sub_zero]
    linarith [hval, h0]
  -- and at `t = 0` by continuity
  have hPall : ∀ (t : ℝ), 0 ≤ t → t < m → ∀ x : E3, P (t, x) = P' (t, x) := by
    intro t ht htm x
    rcases lt_or_eq_of_le ht with h0 | h0
    · exact hPint t h0 htm x
    · have hf : Continuous fun r : ℝ => P (r, x) :=
        h.sol.smoothPressure.continuous.comp (by fun_prop)
      have hg : Continuous fun r : ℝ => P' (r, x) :=
        h'.sol.smoothPressure.continuous.comp (by fun_prop)
      have heqOn : EqOn (fun r : ℝ => P (r, x)) (fun r : ℝ => P' (r, x)) (Ioo 0 m) :=
        fun r hr => hPint r hr.1 hr.2 x
      have hcl := heqOn.closure hf hg
      rw [closure_Ioo hmpos.ne] at hcl
      have : (0 : ℝ) ∈ Icc (0 : ℝ) m := ⟨le_refl 0, hmpos.le⟩
      have h00 := hcl this
      rw [← h0]
      exact h00
  refine ⟨hvel z hz (lt_min hzT hzT'), ?_⟩
  have := hPall z.1 hz (lt_min hzT hzT') z.2
  simpa using this

/-! ## Congruence of the remaining operators -/

/-- Two fields agreeing on an open set have the same divergence there. -/
lemma divg_eq_of_eqOn_open {V V' : STime → E3} {U : Set STime} (hU : IsOpen U)
    (heq : EqOn V V' U) {z : STime} (hz : z ∈ U) : divg V z = divg V' z := by
  have hfd : fderiv ℝ V z = fderiv ℝ V' z :=
    (heq.eventuallyEq_of_mem (hU.mem_nhds hz)).fderiv_eq
  simp only [divg, dspace, hfd]

/-- Two scalar fields agreeing on an open set have the same gradient there. -/
lemma grad_eq_of_eqOn_open {P P' : STime → ℝ} {U : Set STime} (hU : IsOpen U)
    (heq : EqOn P P' U) {z : STime} (hz : z ∈ U) : grad P z = grad P' z := by
  have hfd : fderiv ℝ P z = fderiv ℝ P' z :=
    (heq.eventuallyEq_of_mem (hU.mem_nhds hz)).fderiv_eq
  simp only [grad, dspace, hfd]

/-! ## Gluing a family of normalized window solutions -/

open scoped Classical in
/-- The least index of a window containing the time `t`; times below `0` are
clipped to `0`, which makes the index locally constant near `t = 0` and lets the
gluing avoid the region where the members of the family are unrelated. -/
noncomputable def glueIdx (Tf : ℕ → ℝ) (t : ℝ) : ℕ :=
  if h : ∃ n, max t 0 < Tf n then Nat.find h else 0

/-- The glued velocity field. -/
noncomputable def glueVel (Tf : ℕ → ℝ) (V : ℕ → STime → E3) (z : STime) : E3 :=
  V (glueIdx Tf z.1) z

/-- The glued pressure field. -/
noncomputable def gluePres (Tf : ℕ → ℝ) (Pr : ℕ → STime → ℝ) (z : STime) : ℝ :=
  Pr (glueIdx Tf z.1) z

lemma glueIdx_spec (Tf : ℕ → ℝ) {t : ℝ} (h : ∃ n, max t 0 < Tf n) :
    max t 0 < Tf (glueIdx Tf t) := by
  classical
  rw [glueIdx, dif_pos h]
  exact Nat.find_spec h

lemma glueIdx_eq_zero {Tf : ℕ → ℝ} {t : ℝ} (h0 : max t 0 < Tf 0) : glueIdx Tf t = 0 := by
  classical
  have h : ∃ n, max t 0 < Tf n := ⟨0, h0⟩
  rw [glueIdx, dif_pos h]
  exact Nat.eq_zero_of_le_zero (Nat.find_le h0)

section Gluing

variable {nu : ℝ} {u₀ : E3 → E3} {Tf : ℕ → ℝ} {V : ℕ → STime → E3} {Pr : ℕ → STime → ℝ}

/-- **The glued field is locally a single member of the family.**  Around every
spacetime point whose time lies in some window, there is an open neighbourhood
on which the glued velocity and pressure coincide with those of one fixed
member.  This is what makes the glued field smooth and a solution. -/
theorem glue_local (hnu : 0 < nu) (hpos : ∀ n, 0 < Tf n)
    (hfam : ∀ n, NormalizedWindow nu (Tf n) u₀ (V n) (Pr n))
    (z₀ : STime) (h₀ : ∃ n, z₀.1 < Tf n) :
    ∃ (m : ℕ) (U : Set STime), IsOpen U ∧ z₀ ∈ U ∧ z₀.1 < Tf m ∧
      EqOn (glueVel Tf V) (V m) U ∧ EqOn (gluePres Tf Pr) (Pr m) U := by
  by_cases hc : z₀.1 < Tf 0
  · refine ⟨0, {z : STime | z.1 < Tf 0}, isOpen_lt continuous_fst continuous_const, hc, hc,
      ?_, ?_⟩
    · intro z hz
      show V (glueIdx Tf z.1) z = V 0 z
      rw [glueIdx_eq_zero (max_lt hz (hpos 0))]
    · intro z hz
      show Pr (glueIdx Tf z.1) z = Pr 0 z
      rw [glueIdx_eq_zero (max_lt hz (hpos 0))]
  · push_neg at hc
    have hz0pos : 0 < z₀.1 := lt_of_lt_of_le (hpos 0) hc
    have hmax : max z₀.1 0 = z₀.1 := max_eq_left hz0pos.le
    have hex : ∃ n, max z₀.1 0 < Tf n := by rw [hmax]; exact h₀
    have hmlt : z₀.1 < Tf (glueIdx Tf z₀.1) := by
      have := glueIdx_spec Tf hex; rwa [hmax] at this
    set m := glueIdx Tf z₀.1 with hm
    have key : ∀ z ∈ {z : STime | 0 < z.1 ∧ z.1 < Tf m},
        V (glueIdx Tf z.1) z = V m z ∧ Pr (glueIdx Tf z.1) z = Pr m z := by
      rintro z ⟨hz0, hzm⟩
      have hmaxz : max z.1 0 = z.1 := max_eq_left hz0.le
      have hexz : ∃ n, max z.1 0 < Tf n := ⟨m, by rw [hmaxz]; exact hzm⟩
      have hnlt : z.1 < Tf (glueIdx Tf z.1) := by
        have := glueIdx_spec Tf hexz; rwa [hmaxz] at this
      exact normalizedWindow_unique hnu (hpos _) (hpos m) (hfam _) (hfam m) hz0.le hnlt hzm
    exact ⟨m, {z : STime | 0 < z.1 ∧ z.1 < Tf m},
      (isOpen_lt continuous_const continuous_fst).inter
        (isOpen_lt continuous_fst continuous_const),
      ⟨hz0pos, hmlt⟩, hmlt, fun z hz => (key z hz).1, fun z hz => (key z hz).2⟩

/-- The glued velocity keeps the common initial datum. -/
theorem glueVel_datum (hfam : ∀ n, NormalizedWindow nu (Tf n) u₀ (V n) (Pr n)) (x : E3) :
    glueVel Tf V (0, x) = u₀ x :=
  (hfam (glueIdx Tf (0 : ℝ))).datum x

/-- The glued velocity is spatially periodic. -/
theorem glueVel_periodic (hfam : ∀ n, NormalizedWindow nu (Tf n) u₀ (V n) (Pr n)) :
    SpacePeriodic (glueVel Tf V) := by
  intro z j
  exact (hfam (glueIdx Tf z.1)).sol.periodicVelocity z j

/-- The glued pressure is spatially periodic. -/
theorem gluePres_periodic (hfam : ∀ n, NormalizedWindow nu (Tf n) u₀ (V n) (Pr n)) :
    SpacePeriodic (gluePres Tf Pr) := by
  intro z j
  exact (hfam (glueIdx Tf z.1)).sol.periodicPressure z j

/-- **The glue of a family of normalized window solutions is a slab solution**
on any time `Tstar` covered by the windows. -/
theorem glue_isNSSolutionSlab (hnu : 0 < nu) (hpos : ∀ n, 0 < Tf n)
    (hfam : ∀ n, NormalizedWindow nu (Tf n) u₀ (V n) (Pr n)) {Tstar : ℝ}
    (hcov : ∀ t : ℝ, t < Tstar → ∃ n, t < Tf n) :
    IsNSSolutionSlab nu Tstar (glueVel Tf V) (gluePres Tf Pr) := by
  refine { smoothVelocity := ?_, smoothPressure := ?_,
           periodicVelocity := glueVel_periodic hfam,
           periodicPressure := gluePres_periodic hfam,
           momentum := ?_, incompressible := ?_ }
  · intro z hz
    obtain ⟨m, U, hU, hzU, _, hV, _⟩ := glue_local hnu hpos hfam z (hcov z.1 hz)
    exact ((hfam m).sol.smoothVelocity.contDiffAt).congr_of_eventuallyEq
      (hV.eventuallyEq_of_mem (hU.mem_nhds hzU))
  · intro z hz
    obtain ⟨m, U, hU, hzU, _, _, hP⟩ := glue_local hnu hpos hfam z (hcov z.1 hz)
    exact ((hfam m).sol.smoothPressure.contDiffAt).congr_of_eventuallyEq
      (hP.eventuallyEq_of_mem (hU.mem_nhds hzU))
  · intro z hz0 hz
    obtain ⟨m, U, hU, hzU, hmlt, hV, hP⟩ := glue_local hnu hpos hfam z (hcov z.1 hz)
    obtain ⟨hdt, hadv, hlap⟩ := derivs_eq_of_eqOn_open hU hV hzU
    rw [hdt, hadv, hlap, grad_eq_of_eqOn_open hU hP hzU]
    exact (hfam m).sol.momentum z hz0 hmlt
  · intro z hz0 hz
    obtain ⟨m, U, hU, hzU, hmlt, hV, _⟩ := glue_local hnu hpos hfam z (hcov z.1 hz)
    rw [divg_eq_of_eqOn_open hU hV hzU]
    exact (hfam m).sol.incompressible z hz0 hmlt

/-- **The glue of a family of windows exhausting all of time is a global
solution.** -/
theorem glue_isNSSolution (hnu : 0 < nu) (hpos : ∀ n, 0 < Tf n)
    (hfam : ∀ n, NormalizedWindow nu (Tf n) u₀ (V n) (Pr n))
    (hcov : ∀ t : ℝ, ∃ n, t < Tf n) :
    IsNSSolution nu (glueVel Tf V) (gluePres Tf Pr) := by
  have hslab : ∀ Tstar : ℝ, IsNSSolutionSlab nu Tstar (glueVel Tf V) (gluePres Tf Pr) :=
    fun Tstar => glue_isNSSolutionSlab hnu hpos hfam (fun t _ => hcov t)
  refine { smoothVelocity := ?_, smoothPressure := ?_,
           periodicVelocity := glueVel_periodic hfam,
           periodicPressure := gluePres_periodic hfam,
           momentum := ?_, incompressible := ?_ }
  · exact contDiff_iff_contDiffAt.2 fun z => (hslab (z.1 + 1)).smoothVelocity z (by linarith)
  · exact contDiff_iff_contDiffAt.2 fun z => (hslab (z.1 + 1)).smoothPressure z (by linarith)
  · exact fun z hz => (hslab (z.1 + 1)).momentum z hz (by linarith)
  · exact fun z hz => (hslab (z.1 + 1)).incompressible z hz (by linarith)

end Gluing

/-! ## The maximal-time argument -/

/-- The set of window lengths reachable by a normalized window solution with a
given datum. -/
def windowLengths (nu : ℝ) (u₀ : E3 → E3) : Set ℝ :=
  {T : ℝ | 0 < T ∧ ∃ (V : STime → E3) (P : STime → ℝ), NormalizedWindow nu T u₀ V P}

/-- A window solution restricts to any shorter window. -/
theorem isNSSolutionOn_mono {nu T T' : ℝ} {V : STime → E3} {P : STime → ℝ}
    (h : IsNSSolutionOn nu T V P) (hle : T' ≤ T) : IsNSSolutionOn nu T' V P :=
  { smoothVelocity := h.smoothVelocity
    smoothPressure := h.smoothPressure
    periodicVelocity := h.periodicVelocity
    periodicPressure := h.periodicPressure
    momentum := fun z hz hzT => h.momentum z hz (lt_of_lt_of_le hzT hle)
    incompressible := fun z hz hzT => h.incompressible z hz (lt_of_lt_of_le hzT hle) }

/-- **Reachable window lengths are unbounded.**  Local existence gives one
window; if the reachable lengths were bounded, gluing produces a slab solution
up to the supremum, the absence of velocity blow-up bounds it there, and
continuation produces a strictly longer window — contradicting the supremum. -/
theorem windowLengths_unbounded (hLE : LocalExistenceGate) (hCont : ContinuationGate)
    (hNB : NoVelocityBlowupGate) {nu : ℝ} (hnu : 0 < nu) {u₀ : E3 → E3}
    (hu₀ : AdmissibleDatum u₀) (b : ℝ) : ∃ T ∈ windowLengths nu u₀, b < T := by
  classical
  -- the set is nonempty
  obtain ⟨T₀, hT₀pos, V₀, P₀, hsol₀, hdat₀⟩ := hLE nu hnu u₀ hu₀
  obtain ⟨Q₀, hQ₀⟩ := exists_normalized_window hsol₀ hdat₀
  have hne : (windowLengths nu u₀).Nonempty := ⟨T₀, hT₀pos, V₀, Q₀, hQ₀⟩
  by_contra hcon
  push_neg at hcon
  have hbdd : BddAbove (windowLengths nu u₀) := ⟨b, fun T hT => hcon T hT⟩
  set Ts := sSup (windowLengths nu u₀) with hTs
  have hTspos : 0 < Ts := lt_of_lt_of_le hT₀pos (le_csSup hbdd ⟨hT₀pos, V₀, Q₀, hQ₀⟩)
  -- an exhausting family of windows
  have hstep : ∀ n : ℕ, ∃ (T : ℝ) (Vn : STime → E3) (Pn : STime → ℝ),
      0 < T ∧ NormalizedWindow nu T u₀ Vn Pn ∧ Ts - 1 / (n + 1 : ℝ) < T := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    obtain ⟨a, ha, hlt⟩ := exists_lt_of_lt_csSup hne (show Ts - 1 / (n + 1 : ℝ) < Ts by linarith)
    exact ⟨a, ha.2.choose, ha.2.choose_spec.choose, ha.1, ha.2.choose_spec.choose_spec, hlt⟩
  choose Tf Vf Pf hpos hfam hgt using hstep
  have hcov : ∀ t : ℝ, t < Ts → ∃ n, t < Tf n := by
    intro t ht
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < Ts - t by linarith)
    exact ⟨n, lt_of_lt_of_le (by linarith [hgt n]) le_rfl⟩
  have hslab := glue_isNSSolutionSlab hnu hpos hfam hcov
  obtain ⟨K, hK⟩ := hNB nu hnu Ts hTspos _ _ hslab
  obtain ⟨T', hT', V', P', hsol', hagree⟩ := hCont nu hnu Ts hTspos _ _ hslab ⟨K, hK⟩
  have hdat' : ∀ x : E3, V' (0, x) = u₀ x := by
    intro x
    have := hagree (0, x) le_rfl hTspos
    rw [this]
    exact glueVel_datum hfam x
  obtain ⟨Q', hQ'⟩ := exists_normalized_window hsol' hdat'
  have hmem : T' ∈ windowLengths nu u₀ := ⟨lt_trans hTspos hT', V', Q', hQ'⟩
  exact absurd (le_csSup hbdd hmem) (not_le.2 hT')

/-- **The global assembly gate holds.**  Local existence, window uniqueness,
continuation and the absence of velocity blow-up give the literal periodic Clay
target (B).  Window uniqueness is not needed as a hypothesis here because it is
proved outright in `WindowUniqueness.lean`. -/
theorem globalAssemblyGate_holds : GlobalAssemblyGate := by
  intro hLE _hWU hCont hNB nu hnu u₀ hu₀
  classical
  have hstep : ∀ n : ℕ, ∃ (T : ℝ) (Vn : STime → E3) (Pn : STime → ℝ),
      0 < T ∧ NormalizedWindow nu T u₀ Vn Pn ∧ (n : ℝ) < T := by
    intro n
    obtain ⟨T, hT, hlt⟩ := windowLengths_unbounded hLE hCont hNB hnu hu₀ (n : ℝ)
    exact ⟨T, hT.2.choose, hT.2.choose_spec.choose, hT.1, hT.2.choose_spec.choose_spec, hlt⟩
  choose Tf Vf Pf hpos hfam hgt using hstep
  have hcov : ∀ t : ℝ, ∃ n, t < Tf n :=
    fun t => ⟨⌈t⌉₊, lt_of_le_of_lt (Nat.le_ceil t) (hgt ⌈t⌉₊)⟩
  exact ⟨glueVel Tf Vf, gluePres Tf Pf, glue_isNSSolution hnu hpos hfam hcov,
    glueVel_datum hfam⟩

/-- **The reduced plumbing statement.**  Window uniqueness is proved outright
(`ClayNS.windowUniquenessGate_holds`), so the literal periodic Clay target
follows from local existence, continuation and the absence of velocity blow-up
alone.  Only the last of these three carries the frontier content. -/
theorem clayPeriodicTargetB_of_gates (hLE : LocalExistenceGate) (hCont : ContinuationGate)
    (hNB : NoVelocityBlowupGate) : ClayPeriodicTargetB :=
  globalAssemblyGate_holds hLE windowUniquenessGate_holds hCont hNB

end ClayNS
