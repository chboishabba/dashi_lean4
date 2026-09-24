/-
# The complete inventory of unresolved obligations

This file is the machine-checkable version of "what is still open".  Every gate
that the periodic Clay target still depends on is written here as a **`Prop`**
(never as an axiom or a postulate), in the vocabulary of the development, and
the links that *are* proved are proved here or referenced from where they live.

The gates fall into three groups.

## Frontier (genuinely new PDE input required)

* `ClayNS.DynamicVelocityScaleDefect` (in `DynamicDefectReduction.lean`) and its
  oscillation form `ClayNS.PhysicalVelocityScaleDefectGate` below — **A_dyn**:
  a first singularity cannot be asymptotically flat at its own velocity scale.
  All of the scaling bookkeeping around it is proved; the dynamical input is
  not.
* `ClayNS.LocalizedDefectTransferGate` — **C₁**: an intermediate-scale cutoff
  family on the expanding tori for which the (proved) Kármán–Howarth cutoff
  error tends to zero *while* the localized structure function keeps a
  unit-scale defect.
* `ClayNS.OscillationContractionGate` — **C₂**: the unit-scale oscillation
  improvement for the ancient increment defect.  The strong-minimum shortcut is
  refuted (`ClayNS.parabolic_strong_minimum_no_go`), so this must be a genuine
  decay estimate for subsolutions.
* `ClayNS.CubicSparsePropagation` — **C_sparse**, the proposed unification of
  C₁ and C₂ by an anti-concentration estimate.  This file records that the
  *linear* skeleton refutes the cubic form of it
  (`ClayNS.cubicSparsePropagation_fails_for_linear_skeleton`), so any proof must
  use the nonlinear structure.

## Compactness (standard but not formalized here)

* `ClayNS.BlowupLimitGate` — **B'**: extraction of a locally uniform ancient
  limit from the rescaled fields.  The *consequence* of the extraction that the
  route uses (persistence of the defect under uniform limits) is proved
  (`ClayNS.oscOn_ge_of_uniform_limit`).

## Existence / continuation plumbing (no frontier content, not formalized here)

* `ClayNS.LocalExistenceGate`, `ClayNS.WindowUniquenessGate`,
  `ClayNS.ContinuationGate`, `ClayNS.NoVelocityBlowupGate` — the standard
  Cauchy-theory scaffolding, stated on finite time windows
  (`ClayNS.IsNSSolutionOn`).  `ClayNS.ClayPeriodicTargetB` is not derivable in
  this development without them.

## What is proved here

`ClayNS.blowup_route_false_of_gates` — the three route gates A, B', C₂ are
jointly contradictory, i.e. they do exclude the blow-up scenario; and
`ClayNS.cubicSparsePropagation_fails_for_linear_skeleton` — the linear-skeleton
verdict on C_sparse.

No `sorry`, no postulates, no axioms beyond Lean/Mathlib's standard three.
-/
import RequestProject.NavierStokes.AncientOscillationContraction
import RequestProject.NavierStokes.DynamicDefectReduction
import RequestProject.NavierStokes.LinearSkeletonPropagation
import RequestProject.NavierStokes.KarmanHowarthPressureGauge
import RequestProject.NavierStokes.FrequencyDoubling
import RequestProject.NavierStokes.DeGiorgiIteration
import RequestProject.NavierStokes.IncrementConvexSubsolution
import RequestProject.NavierStokes.IncrementLevelSetEnergy
import RequestProject.NavierStokes.IncrementLocalizedLevelSet
import RequestProject.NavierStokes.FrequencyAlmostMonotone
import RequestProject.NavierStokes.OneStepDyadicNoGo

open scoped BigOperators
open MeasureTheory Filter Topology Metric

noncomputable section

namespace ClayNS

/-! ## Group 1: the frontier gates -/

/-- **A_dyn, oscillation form.**  Along the singular sequence the physical
oscillation on the ball of radius `R₀/M_k` about `x_k` is at least `c₀·M_k`:
the defect penetrates to the velocity scale.  Equivalent, by
`ClayNS.oscOn_blowupSpace_ge_iff`, to a unit-scale defect for the rescaled
fields. -/
def PhysicalVelocityScaleDefectGate (u : ℕ → E3 → E3) (M : ℕ → ℝ) (x : ℕ → E3)
    (R0 c0 : ℝ) : Prop :=
  ∀ k, c0 * M k ≤ oscOn (u k) (Metric.ball (x k) ((M k)⁻¹ * R0))

/-- **C₁, the intermediate-scale transfer.**  A cutoff family `Φ_k` and fields
whose Kármán–Howarth cutoff error tends to `0` *and* whose localized structure
function keeps a fixed defect at some unit-scale separation.  The two clauses
are what makes the gate nontrivial: a large box kills the error but also
dilutes the defect. -/
def LocalizedDefectTransferGate (Phi : ℕ → STime → ℝ) (V : ℕ → STime → E3)
    (P : ℕ → STime → ℝ) (nu : ℝ) (hstar : E3) (tstar cstar : ℝ) : Prop :=
  Tendsto (fun k => khError nu (Phi k) hstar (V k) (P k) tstar) atTop (𝓝 0)
    ∧ ∀ k, cstar ≤ strFun (Phi k) (V k) tstar hstar

/-- **C₂, the unit-scale oscillation improvement** for the ancient limit. -/
def OscillationContractionGate (U : STime → E3) (theta sig : ℝ) : Prop :=
  ∀ R, 0 < R → oscCyl U (theta * R) ≤ (1 - sig) * oscCyl U R

/-- **C_sparse, cubic form.**  A positive local defect forces a cubic amount of
defect on large balls.  This is the shape that would beat the `O(M^{-2})`
density dilution inherited from the periodic ancestors. -/
def CubicSparsePropagation (S : STime → ℝ) (t c : ℝ) : Prop :=
  ∀ R : ℝ, 1 ≤ R → c * R ^ 3 ≤ ∫ h in ball (0 : E3) R, S (t, h)

/-- **The linear skeleton refutes the cubic form of C_sparse.**  The heat
propagator is a strictly positive exact solution of the viscous skeleton
`∂_t S = κΔ_h S` for which no cubic lower bound holds at any positive time.  So
`C_sparse` cannot be obtained from the diffusive part of the increment equation;
it has to come from the nonlinear Kármán–Howarth structure. -/
theorem cubicSparsePropagation_fails_for_linear_skeleton (kap : ℝ) (hkap : 0 < kap) {t : ℝ}
    (ht : 0 < t) {c : ℝ} (hc : 0 < c) : ¬ CubicSparsePropagation (heatGauss kap) t c :=
  no_cubic_growth_for_linear_skeleton kap hkap ht hc

/-- **C_sparse, general polynomial form**: the defect on `B_R` is bounded below
by `c·R^d`. -/
def PolynomialSparsePropagation (S : STime → ℝ) (t c d : ℝ) : Prop :=
  ∀ R : ℝ, 1 ≤ R → c * R ^ d ≤ ∫ h in ball (0 : E3) R, S (t, h)

/-- **The linear skeleton refutes every polynomial degree**, not just the cubic
one: the ball mass of the propagator grows slower than `R^d` for every `d > 0`. -/
theorem polynomialSparsePropagation_fails_for_linear_skeleton (kap : ℝ) (hkap : 0 < kap)
    {t : ℝ} (ht : 0 < t) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    ¬ PolynomialSparsePropagation (heatGauss kap) t c d :=
  no_polynomial_growth_for_linear_skeleton kap hkap ht hc hd

/-! ## Group 1b: the revised frontier — `A_cascade` and `C_localDG`

The polynomial form of `C_sparse` is refuted above, so the frontier is
reorganised as follows.

**A_cascade.**  The energy method reaches the scale `M^{-2/3}`
(`ClayNS.energy_scale_defect`) and no further (`ClayNS.exists_velocity_scale_plateau`),
while the route consumes a defect at `M^{-1}`; the gap is
`cascadeSteps M ≍ (1/3)log₂ M` dyadic steps (`DyadicCascade.lean`).  What is now
*proved* about that iteration:

* a **fixed multiplicative** one-step loss is fatal
  (`ClayNS.geometric_guarantee_tendsto_zero`);
* a **fixed superlinear** one-step loss is also fatal
  (`ClayNS.superlinear_threshold_fails_eventually`);
* a **summable** one-step loss suffices
  (`ClayNS.cascade_persistence_of_small_total_loss`), and so does **zero** loss,
  i.e. a monotonicity formula for the scale-invariant quantity
  (`ClayNS.weightedScale_antitoneOn_of_frequency_le`,
  `ClayNS.velocityScaleDefect_of_scaleAntitone`);
* more sharply, an **almost-monotonicity** formula — the frequency bound
  perturbed by a nonnegative defect density with finite total defect `E` — loses
  only the single factor `e^{−E}`, which does *not* compound over the
  `cascadeSteps M` steps (`ClayNS.weightedScale_lower_of_almost_frequency_le`,
  `ClayNS.velocityScaleDefect_of_almostMonotone`,
  `ClayNS.dynamicVelocityScaleDefect_of_almostMonotone`), with the discrete
  multiplicative companion `ClayNS.cascade_multiplicative_persistence`;
* but the exponent must be **critical**: a doubling inequality with a strictly
  supercritical exponent still degenerates
  (`ClayNS.frequency_cascade_guarantee_tendsto_zero`);
* and the step inequality cannot be kinematic:
  `ClayNS.no_kinematic_one_step_persistence` exhibits, for every radius and
  every prescribed defect level, a nonnegative continuous density with
  `Q_∇(r) = ε` and `Q_∇(r/2) = 0`, so any one-step lemma must consume the
  Navier–Stokes evolution.

So `A_cascade` is now a single, sharply specified analytic question: does
`r ↦ Q_∇(u; x, t, r)` obey an Almgren/Poon-type frequency bound (equivalently a
monotonicity or almost-monotonicity formula with summable defect) along the
singular sequence?

**C_localDG.**  The De Giorgi route for `q = ½|δ_h u|²` is decomposed into
`C_a` (gauge-fixed pressure control — the gauge invariance itself is proved in
`KarmanHowarthPressureGauge.lean`), `C_b` (the level-set energy inequality) and
`C_c` (oscillation decay from the iteration).  The pointwise half of `C_b` is
now proved: every smooth convex composition `β(q)` is a subsolution of the same
operator (`ClayNS.increment_convex_subsolution`), with the potential form
`ClayNS.increment_convex_subsolution_strain`.  Its integrated form is proved
too: over the periodic cell both structural terms vanish exactly and the level
quantity `∫β(q)` obeys the level-set energy inequality
`ClayNS.deriv_incrBetaEnergy_le`, with potential form
`ClayNS.deriv_incrBetaEnergy_le_potential`.  The *localized* (cutoff) version is
proved as well — `ClayNS.increment_localized_level_set_inequality`, with
potential form `ClayNS.increment_localized_level_set_strain` — so `C_b` now has
its Caccioppoli inequality.  The structural half of `C_a` is proved too
(`ClayNS.incr_pressure_localized_split`): the pressure source is a divergence
plus pairings with `∇Φ` and with `β''(q)∇q` only, so the pressure gauge freedom
applies and no free-standing pressure bound is needed.  What remains is the
*quantitative* half of `C_a` (a Calderón–Zygmund/BMO bound on the pressure
oscillation where `∇Φ ≠ 0`) and `C_c` (running the iteration).  The
two abstract
engines the iteration needs are proved as well
(`ClayNS.deGiorgi_fast_convergence`, `ClayNS.holeFilling_iteration`).
-/

/-- **`A_cascade`, one-step form.**  A one-dyadic-step persistence inequality
for the scale-invariant gradient energy along the radii
`cascadeStart M · 2^{-n}`, with an explicit per-step loss `b n`. -/
def OneStepDefectPersistence (G : ℝ → E3 → ℝ) (t0 : ℝ) (x0 : E3) (M : ℝ) (b : ℕ → ℝ) : Prop :=
  ∀ n < cascadeSteps M,
    QgradCyl G t0 x0 (cascadeStart M / 2 ^ n) - b n
      ≤ QgradCyl G t0 x0 (cascadeStart M / 2 ^ (n + 1))

/-- **`A_cascade`, monotonicity form.**  `Q_∇` is nonincreasing in the radius
between the velocity scale and the energy scale — the zero-loss case, which is
what an Almgren-type frequency bound would give. -/
def ScaleMonotonicityGate (G : ℝ → E3 → ℝ) (t0 : ℝ) (x0 : E3) (M : ℝ) : Prop :=
  AntitoneOn (fun r => QgradCyl G t0 x0 r) (Set.Icc (1 / M) (cascadeStart M))

/-- **The monotonicity gate closes the scale gap with no loss.** -/
theorem velocityScaleDefect_of_scaleMonotonicityGate (G : ℝ → E3 → ℝ) (t0 : ℝ) (x0 : E3)
    {M eps : ℝ} (hle : 1 / M ≤ cascadeStart M) (hgate : ScaleMonotonicityGate G t0 x0 M)
    (hstart : eps ≤ QgradCyl G t0 x0 (cascadeStart M)) :
    eps ≤ QgradCyl G t0 x0 (1 / M) :=
  velocityScaleDefect_of_scaleAntitone G t0 x0 hle hgate hstart

/-- **The summable-loss gate closes the scale gap with half the constant**, and
therefore delivers `ClayNS.DynamicVelocityScaleDefect` (the gate `A_dyn`). -/
theorem dynamicVelocityScaleDefect_of_oneStepPersistence {G : ℕ → ℝ → E3 → ℝ} {M : ℕ → ℝ}
    {t : ℕ → ℝ} {x : ℕ → E3} {eps : ℝ} (heps : 0 < eps) (hM : ∀ k, 0 < M k) (b : ℕ → ℕ → ℝ)
    (hstart : ∀ k, eps ≤ QgradCyl (G k) (t k) (x k) (cascadeStart (M k)))
    (hstep : ∀ k, OneStepDefectPersistence (G k) (t k) (x k) (M k) (b k))
    (hsum : ∀ k, ∑ n ∈ Finset.range (cascadeSteps (M k)), b k n ≤ eps / 2) :
    DynamicVelocityScaleDefect G M t x :=
  dynamicVelocityScaleDefect_of_cascade heps hM b hstart hstep hsum

/-- **`C_b`, the level-set energy recursion.**  The De Giorgi quantities `Y n`
(the level-set energies of `q = ½|δ_h u|²` at the levels `k_n ↑ k_∞` on the
shrinking cylinders) satisfy the superlinear recursion. -/
def LevelSetEnergyRecursion (Y : ℕ → ℝ) (C bb alpha : ℝ) : Prop :=
  (∀ n, 0 ≤ Y n) ∧ ∀ n, Y (n + 1) ≤ C * bb ^ (n : ℝ) * Y n ^ (1 + alpha)

/-- **`C_c` follows from `C_b` plus smallness**: if the level-set energies obey
the recursion and the initial one is below the De Giorgi threshold, they vanish
in the limit — i.e. the limiting level is not exceeded, which is the local
boundedness/oscillation-decay step. -/
theorem levelSetEnergy_tendsto_zero {Y : ℕ → ℝ} {C bb alpha : ℝ}
    (hC : 0 < C) (hb : 1 < bb) (halpha : 0 < alpha)
    (hrec : LevelSetEnergyRecursion Y C bb alpha)
    (hY0 : Y 0 ≤ C ^ (-1 / alpha) * bb ^ (-1 / alpha ^ 2)) :
    Filter.Tendsto Y Filter.atTop (𝓝 0) :=
  deGiorgi_tendsto_zero hC hb halpha hrec.1 hrec.2 hY0

/-! ## Group 2: the compactness gate -/

/-- **B', extraction of the ancient limit.**  The rescaled fields converge
uniformly on `B_{R₀}` to the time-`0` slice of a bounded ancient field `U`. -/
def BlowupLimitGate (u : ℕ → E3 → E3) (M : ℕ → ℝ) (x : ℕ → E3) (U : STime → E3)
    (R0 : ℝ) : Prop :=
  ∀ eps > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ y ∈ Metric.ball (0 : E3) R0,
    ‖blowupSpace (u k) (M k) (x k) y - U (0, y)‖ ≤ eps

/-- **The three route gates are jointly contradictory.**  This is the assembled
blow-up exclusion: A (velocity-scale defect) + B' (extraction) + C₂
(oscillation contraction) ⇒ `False`.  Only the gates are hypotheses; the
iteration that turns the contraction into constancy is proved. -/
theorem blowup_route_false_of_gates (u : ℕ → E3 → E3) (M : ℕ → ℝ) (x : ℕ → E3)
    (U : STime → E3) {K theta sig R0 c0 : ℝ}
    (hM : ∀ k, 0 < M k) (hK : 0 ≤ K) (hb : ∀ z, ‖U z‖ ≤ K)
    (hth0 : 0 < theta) (hth1 : theta < 1) (hs0 : 0 < sig) (hs1 : sig ≤ 1) (hc0 : 0 < c0)
    (hA : PhysicalVelocityScaleDefectGate u M x R0 c0)
    (hB : BlowupLimitGate u M x U R0)
    (hC : OscillationContractionGate U theta sig) : False :=
  clay_blowup_route_contradiction u M x U hM hK hb hth0 hth1 hs0 hs1 hc0 hA hB hC

/-! ## Group 3: the existence and continuation plumbing -/

/-- A smooth periodic solution on the finite time window `[0,T)`. -/
structure IsNSSolutionOn (nu T : ℝ) (V : STime → E3) (P : STime → ℝ) : Prop where
  smoothVelocity : ContDiff ℝ (⊤ : ℕ∞) V
  smoothPressure : ContDiff ℝ (⊤ : ℕ∞) P
  periodicVelocity : SpacePeriodic V
  periodicPressure : SpacePeriodic P
  momentum : ∀ z : STime, 0 ≤ z.1 → z.1 < T → dtime V z + adv V z = - grad P z + nu • lap V z
  incompressible : ∀ z : STime, 0 ≤ z.1 → z.1 < T → divg V z = 0

/-- A global solution restricts to every window. -/
theorem isNSSolutionOn_of_isNSSolution {nu T : ℝ} {V : STime → E3} {P : STime → ℝ}
    (h : IsNSSolution nu V P) : IsNSSolutionOn nu T V P :=
  { smoothVelocity := h.smoothVelocity
    smoothPressure := h.smoothPressure
    periodicVelocity := h.periodicVelocity
    periodicPressure := h.periodicPressure
    momentum := fun z hz _ => h.momentum z hz
    incompressible := fun z hz _ => h.incompressible z hz }

/-- A smooth periodic solution on the **open slab** `{t < T}`: smoothness is
required only where the equations are imposed.  This is what a Cauchy theory
produces on an interval of existence, and it is exactly what a glued family of
window solutions satisfies — a solution on `[0,T)` need not extend smoothly
across `t = T`, so demanding global smoothness there would be a modelling
error.  Every window solution is a slab solution. -/
structure IsNSSolutionSlab (nu T : ℝ) (V : STime → E3) (P : STime → ℝ) : Prop where
  smoothVelocity : ∀ z : STime, z.1 < T → ContDiffAt ℝ (⊤ : ℕ∞) V z
  smoothPressure : ∀ z : STime, z.1 < T → ContDiffAt ℝ (⊤ : ℕ∞) P z
  periodicVelocity : SpacePeriodic V
  periodicPressure : SpacePeriodic P
  momentum : ∀ z : STime, 0 ≤ z.1 → z.1 < T → dtime V z + adv V z = - grad P z + nu • lap V z
  incompressible : ∀ z : STime, 0 ≤ z.1 → z.1 < T → divg V z = 0

/-- Every window solution is a slab solution. -/
theorem isNSSolutionSlab_of_isNSSolutionOn {nu T : ℝ} {V : STime → E3} {P : STime → ℝ}
    (h : IsNSSolutionOn nu T V P) : IsNSSolutionSlab nu T V P :=
  { smoothVelocity := fun _ _ => h.smoothVelocity.contDiffAt
    smoothPressure := fun _ _ => h.smoothPressure.contDiffAt
    periodicVelocity := h.periodicVelocity
    periodicPressure := h.periodicPressure
    momentum := h.momentum
    incompressible := h.incompressible }

/-- **Local existence.**  Every admissible datum is attained by a solution on
some nondegenerate window. -/
def LocalExistenceGate : Prop :=
  ∀ nu : ℝ, 0 < nu → ∀ u₀ : E3 → E3, AdmissibleDatum u₀ →
    ∃ T > 0, ∃ (V : STime → E3) (P : STime → ℝ),
      IsNSSolutionOn nu T V P ∧ ∀ x : E3, V (0, x) = u₀ x

/-- **Uniqueness on a window.**  Two window solutions with the same datum agree
on the window. -/
def WindowUniquenessGate : Prop :=
  ∀ nu : ℝ, 0 < nu → ∀ T : ℝ, 0 < T → ∀ (V V' : STime → E3) (P P' : STime → ℝ),
    IsNSSolutionOn nu T V P → IsNSSolutionOn nu T V' P' →
    (∀ x : E3, V (0, x) = V' (0, x)) →
    ∀ z : STime, 0 ≤ z.1 → z.1 < T → V z = V' z

/-- **Continuation.**  A window solution whose velocity stays bounded on the
window extends to a strictly longer window. -/
def ContinuationGate : Prop :=
  ∀ nu : ℝ, 0 < nu → ∀ T : ℝ, 0 < T → ∀ (V : STime → E3) (P : STime → ℝ),
    IsNSSolutionSlab nu T V P → (∃ K : ℝ, ∀ z : STime, 0 ≤ z.1 → z.1 < T → ‖V z‖ ≤ K) →
    ∃ T' > T, ∃ (V' : STime → E3) (P' : STime → ℝ),
      IsNSSolutionOn nu T' V' P' ∧ ∀ z : STime, 0 ≤ z.1 → z.1 < T → V' z = V z

/-- **No velocity blow-up.**  This is the statement the A/B/C route is designed
to deliver: on every finite window the velocity of a solution is bounded. -/
def NoVelocityBlowupGate : Prop :=
  ∀ nu : ℝ, 0 < nu → ∀ T : ℝ, 0 < T → ∀ (V : STime → E3) (P : STime → ℝ),
    IsNSSolutionSlab nu T V P → ∃ K : ℝ, ∀ z : STime, 0 ≤ z.1 → z.1 < T → ‖V z‖ ≤ K

/-- **The global assembly gate.**  Local existence, uniqueness on windows,
continuation and the absence of velocity blow-up together yield the Clay
periodic alternative (B).  This implication is **proved** in
`GlobalAssembly.lean` (`ClayNS.globalAssemblyGate_holds`), by pressure
normalization, gluing of normalized window solutions and a maximal-time
argument; and `ClayNS.WindowUniquenessGate` itself is proved in
`WindowUniqueness.lean` (`ClayNS.windowUniquenessGate_holds`).  Those files
import this one, so the statements live here and the proofs
live downstream. -/
def GlobalAssemblyGate : Prop :=
  LocalExistenceGate → WindowUniquenessGate → ContinuationGate → NoVelocityBlowupGate →
    ClayPeriodicTargetB

end ClayNS
