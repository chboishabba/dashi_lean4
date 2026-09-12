/-
# A literal, analytically interpreted statement of the periodic Clay
# Navier–Stokes target, and the genuinely derived Galilean reduction.

The Agda material in this repository states the Clay target through an
*uninterpreted* carrier record (`FeffermanPeriodicClayCarrier`): smoothness,
periodicity, divergence-freeness and the momentum equation are abstract
`Set`-valued fields.  `DASHI/Papers/NavierStokes/ClayCarrierVacuityAudit.agda`
shows (machine-checked) that the resulting statement type is inhabited by a
degenerate carrier, so it carries no analytic content by itself.

This file supplies the missing analytic interpretation, over the real numbers,
with honest Fréchet derivatives:

* `ClayNS.IsNSSolution` — the three-dimensional incompressible Navier–Stokes
  system with zero force;
* `ClayNS.ClayPeriodicTargetB` — Fefferman's periodic alternative (B):
  arbitrary positive viscosity, arbitrary smooth `ℤ³`-periodic divergence-free
  datum, no mean-zero hypothesis, no uniqueness hypothesis, global smooth
  periodic velocity *and* pressure, momentum equation, incompressibility and
  initial trace as separate conclusions.

Remark on the time domain.  Fefferman asks for `u, p ∈ C^∞(ℝ³ × [0,∞))`.  Here
the witness is required to be `C^∞` on all of `ℝ × ℝ³` while the equations are
imposed only for `t ≥ 0`.  Any witness in this sense restricts to a Fefferman
witness, so `ClayPeriodicTargetB` implies the Clay periodic alternative (B).
Nothing is weakened.

The mathematical content proved here is the **mean/Galilean reduction (step L1
of the roadmap)**, which in the Agda development is only an abstract record
shuffle with the reduction itself assumed as a field
(`restoreGalileanSolution`).  Here it is an actual derivation:
`ClayNS.isNSSolution_galileanShift` proves that if `(V, P)` solves periodic
Navier–Stokes then so does
`u(t,x) = V(t, x - t·m) + m`, `p(t,x) = P(t, x - t·m)`,
with datum shifted by the constant vector `m`; every clause (smoothness, both
periodicities, momentum, incompressibility, initial trace) is derived from the
equations.

No `sorry`, no postulates, no axioms beyond Lean/Mathlib's standard three.
-/
import Mathlib

open scoped BigOperators

noncomputable section

namespace ClayNS

/-! ## Space, spacetime and differential operators -/

/-- Physical space `ℝ³`. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- Spacetime `ℝ × ℝ³`, the first coordinate being time. -/
abbrev STime := ℝ × E3

/-- The `i`-th coordinate unit vector of `ℝ³`. -/
def ee (i : Fin 3) : E3 := EuclideanSpace.single i (1 : ℝ)

lemma basis_expand (m : E3) : (∑ i, (m i) • ee i) = m := by
  ext j
  simp [ee, Pi.single_apply]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Time derivative `∂_t`. -/
def dtime (V : STime → F) (z : STime) : F := fderiv ℝ V z (1, 0)

/-- Spatial derivative `∂_i`. -/
def dspace (V : STime → F) (i : Fin 3) (z : STime) : F := fderiv ℝ V z (0, ee i)

/-- Spatial Laplacian `Δ = ∑ ∂_i∂_i`. -/
def lap (V : STime → F) (z : STime) : F := ∑ i, dspace (fun w => dspace V i w) i z

/-- Spatial gradient of a scalar field. -/
def grad (P : STime → ℝ) (z : STime) : E3 := ∑ i, (dspace P i z) • ee i

/-- The advective term `(u · ∇)u`. -/
def adv (V : STime → E3) (z : STime) : E3 := ∑ i, (V z i) • dspace V i z

/-- Spatial divergence `div u = ∑ ∂_i u_i`. -/
def divg (V : STime → E3) (z : STime) : ℝ := ∑ i, (dspace V i z) i

/-- Spatial `ℤ³`-periodicity: invariance under the unit lattice translations. -/
def SpacePeriodic (V : STime → F) : Prop :=
  ∀ (z : STime) (j : Fin 3), V (z.1, z.2 + ee j) = V z

/-- A directional spatial derivative expands in the coordinate directions. -/
lemma fderiv_space_vector (V : STime → F) (w : STime) (m : E3) :
    fderiv ℝ V w (0, m) = ∑ i, (m i) • dspace V i w := by
  have key : ((0 : ℝ), m) = ∑ i, (m i) • ((0 : ℝ), ee i) := by
    have h : (∑ i, (m i) • ((0 : ℝ), ee i))
        = ContinuousLinearMap.inr ℝ ℝ E3 (∑ i, (m i) • ee i) := by
      rw [map_sum]
      simp
    rw [h, basis_expand]
    rfl
  rw [key, map_sum]
  simp only [map_smul, dspace]

/-! ## The Navier–Stokes system -/

/-- `(V, P)` is a global smooth spatially `ℤ³`-periodic solution of the
three-dimensional incompressible Navier–Stokes system with viscosity `ν` and
zero external force, for all nonnegative times. -/
structure IsNSSolution (ν : ℝ) (V : STime → E3) (P : STime → ℝ) : Prop where
  smoothVelocity : ContDiff ℝ (⊤ : ℕ∞) V
  smoothPressure : ContDiff ℝ (⊤ : ℕ∞) P
  periodicVelocity : SpacePeriodic V
  periodicPressure : SpacePeriodic P
  momentum : ∀ z : STime, 0 ≤ z.1 → dtime V z + adv V z = - grad P z + ν • lap V z
  incompressible : ∀ z : STime, 0 ≤ z.1 → divg V z = 0

/-- A Clay-admissible initial datum: smooth, `ℤ³`-periodic and divergence free.
No mean-zero condition is imposed. -/
structure AdmissibleDatum (u₀ : E3 → E3) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) u₀
  periodic : ∀ (x : E3) (j : Fin 3), u₀ (x + ee j) = u₀ x
  divergenceFree : ∀ x : E3, (∑ i, (fderiv ℝ u₀ x (ee i)) i) = 0

/-- **Fefferman's periodic alternative (B)**, stated literally: for every
positive viscosity and every smooth periodic divergence-free datum there is a
globally smooth periodic velocity/pressure pair solving Navier–Stokes with the
given initial datum. -/
def ClayPeriodicTargetB : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : E3 → E3, AdmissibleDatum u₀ →
    ∃ (V : STime → E3) (P : STime → ℝ),
      IsNSSolution ν V P ∧ (∀ x : E3, V (0, x) = u₀ x)

/-! ### Non-vacuity of the definitions -/

/-- Sanity check that `IsNSSolution` is satisfiable: every constant velocity
field with zero pressure solves the system.  (This also confirms that the
differential operators above are not accidentally contradictory.) -/
theorem isNSSolution_const (nu : ℝ) (c : E3) :
    IsNSSolution nu (fun _ => c) (fun _ => 0) := by
  have hd : ∀ (i : Fin 3) (z : STime), dspace (fun _ : STime => c) i z = 0 := by
    intro i z; simp [dspace]
  have hdP : ∀ (i : Fin 3) (z : STime), dspace (fun _ : STime => (0 : ℝ)) i z = 0 := by
    intro i z; simp [dspace]
  refine
    { smoothVelocity := contDiff_const
      smoothPressure := contDiff_const
      periodicVelocity := fun _ _ => rfl
      periodicPressure := fun _ _ => rfl
      momentum := ?_
      incompressible := ?_ }
  · intro z _
    have hlap : lap (fun _ : STime => c) z = 0 := by
      simp [lap, dspace]
    simp [dtime, adv, grad, hd, hdP, hlap]
  · intro z _
    simp [divg, hd]

/-! ## The Galilean change of spacetime coordinates -/

/-- The Galilean change of coordinates `(t, x) ↦ (t, x - t·m)`, a continuous
linear automorphism of spacetime. -/
def shiftCLM (m : E3) : STime →L[ℝ] STime :=
  (ContinuousLinearMap.fst ℝ ℝ E3).prod
    ((ContinuousLinearMap.snd ℝ ℝ E3) -
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.fst ℝ ℝ E3) m))

@[simp] lemma shiftCLM_apply (m : E3) (z : STime) :
    shiftCLM m z = (z.1, z.2 - z.1 • m) := rfl

/-- The Galilean boost of a velocity field. -/
def galVel (m : E3) (V : STime → E3) : STime → E3 := fun z => V (shiftCLM m z) + m

/-- The Galilean transport of a pressure field. -/
def galPres (m : E3) (P : STime → ℝ) : STime → ℝ := fun z => P (shiftCLM m z)

/-! ### Derivatives of the transformed fields -/

lemma fderiv_comp_shift (V : STime → F) (m : E3) (z : STime)
    (hV : DifferentiableAt ℝ V (shiftCLM m z)) :
    fderiv ℝ (fun y => V (shiftCLM m y)) z
      = (fderiv ℝ V (shiftCLM m z)).comp (shiftCLM m) :=
  (hV.hasFDerivAt.comp z ((shiftCLM m).hasFDerivAt)).fderiv

lemma fderiv_galVel (m : E3) (V : STime → E3) (hV : Differentiable ℝ V) (z : STime) :
    fderiv ℝ (galVel m V) z = (fderiv ℝ V (shiftCLM m z)).comp (shiftCLM m) :=
  ((((hV (shiftCLM m z)).hasFDerivAt).comp z ((shiftCLM m).hasFDerivAt)).add_const m).fderiv

lemma dspace_comp (V : STime → F) (m : E3) (hV : Differentiable ℝ V) (i : Fin 3) (z : STime) :
    dspace (fun y => V (shiftCLM m y)) i z = dspace V i (shiftCLM m z) := by
  rw [dspace, fderiv_comp_shift V m z (hV _)]
  simp [dspace]

lemma dspace_galPres (m : E3) (P : STime → ℝ) (hP : Differentiable ℝ P)
    (i : Fin 3) (z : STime) :
    dspace (galPres m P) i z = dspace P i (shiftCLM m z) :=
  dspace_comp P m hP i z

lemma dspace_galVel (m : E3) (V : STime → E3) (hV : Differentiable ℝ V)
    (i : Fin 3) (z : STime) :
    dspace (galVel m V) i z = dspace V i (shiftCLM m z) := by
  rw [dspace, fderiv_galVel m V hV z]
  simp [dspace]

lemma dtime_galVel (m : E3) (V : STime → E3) (hV : Differentiable ℝ V) (z : STime) :
    dtime (galVel m V) z
      = dtime V (shiftCLM m z) - ∑ i, (m i) • dspace V i (shiftCLM m z) := by
  rw [dtime, fderiv_galVel m V hV z]
  have hz : (shiftCLM m) ((1 : ℝ), (0 : E3)) = ((1 : ℝ), -m) := by
    simp
  have hsplit : ((1 : ℝ), -m) = ((1 : ℝ), (0 : E3)) + ((0 : ℝ), -m) := by
    simp
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, hz, hsplit, map_add]
  rw [fderiv_space_vector V (shiftCLM m z) (-m)]
  simp [dtime, sub_eq_add_neg]

lemma lap_galVel (m : E3) (V : STime → E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (z : STime) :
    lap (galVel m V) z = lap V (shiftCLM m z) := by
  have hdiff : Differentiable ℝ V := hV.differentiable (by simp)
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fun w : STime => fderiv ℝ V w) :=
    hV.fderiv_right (by simp)
  refine Finset.sum_congr rfl ?_
  intro i _
  have hfun : (fun w => dspace (galVel m V) i w) = fun w => dspace V i (shiftCLM m w) := by
    funext w; exact dspace_galVel m V hdiff i w
  rw [hfun]
  have hd1 : Differentiable ℝ (fun w : STime => dspace V i w) := by
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun w : STime => dspace V i w) := by
      have hc : ContDiff ℝ (⊤ : ℕ∞)
          ((ContinuousLinearMap.apply ℝ E3 ((0 : ℝ), ee i)) ∘
            (fun w : STime => fderiv ℝ V w)) :=
        (ContinuousLinearMap.apply ℝ E3 ((0 : ℝ), ee i)).contDiff.comp hfd
      simpa [dspace, Function.comp] using hc
    exact h2.differentiable (by simp)
  exact dspace_comp (fun w => dspace V i w) m hd1 i z

lemma grad_galPres (m : E3) (P : STime → ℝ) (hP : Differentiable ℝ P) (z : STime) :
    grad (galPres m P) z = grad P (shiftCLM m z) := by
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [dspace_galPres m P hP i z]

lemma adv_galVel (m : E3) (V : STime → E3) (hV : Differentiable ℝ V) (z : STime) :
    adv (galVel m V) z
      = adv V (shiftCLM m z) + ∑ i, (m i) • dspace V i (shiftCLM m z) := by
  simp only [adv]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [dspace_galVel m V hV i z]
  have hcoord : (galVel m V z) i = V (shiftCLM m z) i + m i := rfl
  rw [hcoord, add_smul]

lemma divg_galVel (m : E3) (V : STime → E3) (hV : Differentiable ℝ V) (z : STime) :
    divg (galVel m V) z = divg V (shiftCLM m z) := by
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [dspace_galVel m V hV i z]

/-! ### The Galilean reduction theorem -/

/-- **Galilean/mean restoration.**  If `(V, P)` is a global smooth periodic
solution of Navier–Stokes with viscosity `ν`, then so is the constant-velocity
boost `u(t,x) = V(t, x - t·m) + m`, `p(t,x) = P(t, x - t·m)`.  Every clause of
`IsNSSolution` is derived. -/
theorem isNSSolution_galileanShift (ν : ℝ) (m : E3) (V : STime → E3) (P : STime → ℝ)
    (h : IsNSSolution ν V P) :
    IsNSSolution ν (galVel m V) (galPres m P) := by
  have hVd : Differentiable ℝ V := h.smoothVelocity.differentiable (by simp)
  have hPd : Differentiable ℝ P := h.smoothPressure.differentiable (by simp)
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun y : STime => V (shiftCLM m y)) :=
    h.smoothVelocity.comp (shiftCLM m).contDiff
  refine
    { smoothVelocity := hcomp.add contDiff_const
      smoothPressure := h.smoothPressure.comp (shiftCLM m).contDiff
      periodicVelocity := ?_
      periodicPressure := ?_
      momentum := ?_
      incompressible := ?_ }
  · intro z j
    have hz : shiftCLM m (z.1, z.2 + ee j) = ((shiftCLM m z).1, (shiftCLM m z).2 + ee j) := by
      simp [shiftCLM_apply]; abel
    show V (shiftCLM m (z.1, z.2 + ee j)) + m = V (shiftCLM m z) + m
    rw [hz, h.periodicVelocity (shiftCLM m z) j]
  · intro z j
    have hz : shiftCLM m (z.1, z.2 + ee j) = ((shiftCLM m z).1, (shiftCLM m z).2 + ee j) := by
      simp [shiftCLM_apply]; abel
    show P (shiftCLM m (z.1, z.2 + ee j)) = P (shiftCLM m z)
    rw [hz, h.periodicPressure (shiftCLM m z) j]
  · intro z hz
    have hz' : (0 : ℝ) ≤ (shiftCLM m z).1 := hz
    rw [dtime_galVel m V hVd z, adv_galVel m V hVd z,
      grad_galPres m P hPd z, lap_galVel m V h.smoothVelocity z]
    have hm := h.momentum (shiftCLM m z) hz'
    rw [← hm]
    abel
  · intro z hz
    have hz' : (0 : ℝ) ≤ (shiftCLM m z).1 := hz
    rw [divg_galVel m V hVd z]
    exact h.incompressible (shiftCLM m z) hz'

@[simp] lemma galVel_initial (m : E3) (V : STime → E3) (x : E3) :
    galVel m V (0, x) = V (0, x) + m := by
  simp [galVel]

/-- A constant-velocity boost of an admissible datum is admissible. -/
theorem admissibleDatum_add_const {u₀ : E3 → E3} (h : AdmissibleDatum u₀) (m : E3) :
    AdmissibleDatum (fun x => u₀ x + m) := by
  have hu : Differentiable ℝ u₀ := h.smooth.differentiable (by simp)
  refine { smooth := h.smooth.add contDiff_const, periodic := ?_, divergenceFree := ?_ }
  · intro x j; show u₀ (x + ee j) + m = u₀ x + m; rw [h.periodic x j]
  · intro x
    have hd : fderiv ℝ (fun x => u₀ x + m) x = fderiv ℝ u₀ x :=
      (((hu x).hasFDerivAt).add_const m).fderiv
    rw [hd]
    exact h.divergenceFree x

/-- **Reduction to a centred subclass.**  Let `Centred` be any property of data.
If the Clay periodic problem is solvable for every admissible datum satisfying
`Centred`, and every admissible datum becomes `Centred` after subtracting a
suitable constant vector, then the full Clay periodic alternative (B) holds.

Instantiating `Centred` with "spatial mean zero" and the constant with the
spatial mean gives exactly the mean-zero reduction (`L1`) of the roadmap.  Here
the Navier–Stokes content of that reduction — that the boosted pair really
solves the equations — is derived, not assumed. -/
theorem clayPeriodicTargetB_of_centred (Centred : (E3 → E3) → Prop)
    (solveCentred : ∀ ν : ℝ, 0 < ν → ∀ v₀ : E3 → E3, AdmissibleDatum v₀ → Centred v₀ →
      ∃ (V : STime → E3) (P : STime → ℝ),
        IsNSSolution ν V P ∧ (∀ x : E3, V (0, x) = v₀ x))
    (centring : ∀ u₀ : E3 → E3, AdmissibleDatum u₀ →
      ∃ m : E3, Centred (fun x => u₀ x - m)) :
    ClayPeriodicTargetB := by
  intro ν hν u₀ hu₀
  obtain ⟨m, hm⟩ := centring u₀ hu₀
  have hv₀ : AdmissibleDatum (fun x => u₀ x - m) := by
    have h := admissibleDatum_add_const hu₀ (-m)
    simpa [sub_eq_add_neg] using h
  obtain ⟨V, P, hsol, hinit⟩ := solveCentred ν hν (fun x => u₀ x - m) hv₀ hm
  refine ⟨galVel m V, galPres m P, isNSSolution_galileanShift ν m V P hsol, ?_⟩
  intro x
  rw [galVel_initial, hinit x]
  abel

end ClayNS
