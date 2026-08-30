/-
# Oscillation contraction on parabolic cylinders and the ancient rigidity chain
# (targets C, D of the revised route)

The revised route replaces the opaque whole-space Liouville statement R2 by a
*single scale-independent oscillation-decay inequality* (§17):

  `osc_{Q_{θR}} U ≤ (1 − σ) osc_{Q_R} U`   for all `R > 0`,        (C)

with `θ, σ ∈ (0,1)` independent of `R`.  This file proves the parts of the
revised route that are actually derivable, and states the chain precisely:

* `ClayNS.eq_zero_of_geometric_contraction` — the abstract iteration: a
  nonnegative bounded function of the scale which contracts by a fixed factor
  under `R ↦ θR` vanishes identically.  (This is target **D**, and indeed it is
  cheap.)
* `ClayNS.ancient_constant_of_oscillation_contraction` — **D applied**: a
  bounded field on `ℝ³ × (−∞,0]` satisfying the contraction (C) is constant
  there.
* `ClayNS.false_of_defect_and_oscillation_contraction` — the bottom of the
  dependency graph of §18: an R1 defect (a nonzero oscillation of `U(·,0)` on
  some ball) together with (C) is contradictory.  So the whole programme is
  reduced to producing the defect (A/B) and proving the contraction (C).
* `ClayNS.constant_iff_increments_vanish` — the increment reformulation of §15:
  constancy is exactly the vanishing of all increments `δ_h U`.
* `ClayNS.eq_zero_of_constant_of_vanishing_ball_average` and
  `ClayNS.false_of_unit_normalized_constant_with_vanishing_ball_average` — the
  §8 observation: a *vanishing large-scale ball average*, which is the residue
  of the periodic ancestry (the rescaled box mean is `m/M_k → 0`), upgrades
  "constant" to "zero" and therefore contradicts the KNSŠ normalization
  `|U(0,0)| = 1`.  In particular a Liouville theorem producing only *some*
  constant suffices, once the vanishing mean is available.
* `ClayNS.poincare_rate_mul_backward_lifetime` — the §10 scaling audit: the
  product of the rescaled torus Poincaré rate `λ_k ≍ (M_k L)^{-2}` and the
  backward lifetime `A_k ≍ M_k² t_k` is *independent of* `M_k`.  This is a
  no-go: enlarging the backward interval exactly compensates the vanishing
  spectral gap, so no free exponential annihilation is available from
  ancientness alone at the KNSŠ scaling.

No `sorry`, no postulates.  What is **not** proved here is (C) itself, nor the
defect (A); those remain the frontier, exactly as stated in §20 of the route.
-/
import RequestProject.NavierStokes.BlowupOscillation

open scoped Pointwise
open Metric Set Filter Topology MeasureTheory

noncomputable section

namespace ClayNS

/-! ## The abstract contraction iteration (target D) -/

/-- Iterating the contraction `n` times. -/
lemma geometric_contraction_pow {F : ℝ → ℝ} {theta sig : ℝ}
    (hth : 0 < theta) (hs1 : sig ≤ 1)
    (hcon : ∀ R, 0 < R → F (theta * R) ≤ (1 - sig) * F R) :
    ∀ (n : ℕ) (R : ℝ), 0 < R → F (theta ^ n * R) ≤ (1 - sig) ^ n * F R := by
  intro n
  induction n with
  | zero => intro R _; simp
  | succ n ih =>
      intro R hR
      have hpow : (0:ℝ) < theta ^ n * R := by positivity
      have h1 : F (theta * (theta ^ n * R)) ≤ (1 - sig) * F (theta ^ n * R) :=
        hcon _ hpow
      have h2 : (1 - sig) * F (theta ^ n * R) ≤ (1 - sig) * ((1 - sig) ^ n * F R) :=
        mul_le_mul_of_nonneg_left (ih R hR) (by linarith)
      have heq : theta ^ (n + 1) * R = theta * (theta ^ n * R) := by ring
      calc F (theta ^ (n+1) * R) = F (theta * (theta ^ n * R)) := by rw [heq]
        _ ≤ (1 - sig) * F (theta ^ n * R) := h1
        _ ≤ (1 - sig) * ((1 - sig) ^ n * F R) := h2
        _ = (1 - sig) ^ (n+1) * F R := by ring

/-- **Target D (abstract form).**  A nonnegative function of the scale which is
bounded and contracts by a fixed factor `1 − σ < 1` when the scale is shrunk by
a fixed factor `θ < 1` vanishes at every positive scale. -/
theorem eq_zero_of_geometric_contraction {F : ℝ → ℝ} {theta sig Cb : ℝ}
    (hth0 : 0 < theta) (hth1 : theta < 1) (hs0 : 0 < sig) (hs1 : sig ≤ 1)
    (hF0 : ∀ R, 0 ≤ F R) (hFb : ∀ R, F R ≤ Cb)
    (hcon : ∀ R, 0 < R → F (theta * R) ≤ (1 - sig) * F R) :
    ∀ r, 0 < r → F r = 0 := by
  intro r hr
  have hCb : 0 ≤ Cb := le_trans (hF0 r) (hFb r)
  have hkey : ∀ n : ℕ, F r ≤ (1 - sig) ^ n * Cb := by
    intro n
    have hpow : (0:ℝ) < theta ^ n := pow_pos hth0 n
    have hR : 0 < r / theta ^ n := div_pos hr hpow
    have h := geometric_contraction_pow hth0 hs1 hcon n (r / theta ^ n) hR
    have heq : theta ^ n * (r / theta ^ n) = r := by field_simp
    rw [heq] at h
    have h2 : (1 - sig) ^ n * F (r / theta ^ n) ≤ (1 - sig) ^ n * Cb :=
      mul_le_mul_of_nonneg_left (hFb _) (pow_nonneg (by linarith) n)
    exact le_trans h h2
  have hlim : Tendsto (fun n : ℕ => (1 - sig) ^ n * Cb) atTop (𝓝 0) := by
    have h1 : |1 - sig| < 1 := by
      rw [abs_lt]; constructor <;> linarith
    have := tendsto_pow_atTop_nhds_zero_of_abs_lt_one h1
    simpa using this.mul_const Cb
  have : F r ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hkey)
  exact le_antisymm this (hF0 r)

/-! ## Parabolic cylinders and the ancient oscillation -/

/-- The parabolic cylinder `Q_R = B_R × (−R², 0]`. -/
def parCyl (R : ℝ) : Set STime := {z : STime | -(R ^ 2) < z.1 ∧ z.1 ≤ 0 ∧ ‖z.2‖ < R}

/-- The oscillation of an ancient field on the parabolic cylinder of scale `R`. -/
def oscCyl (U : STime → E3) (R : ℝ) : ℝ := oscOn U (parCyl R)

lemma oscCyl_nonneg (U : STime → E3) (R : ℝ) : 0 ≤ oscCyl U R := oscOn_nonneg _ _

lemma oscCyl_le (U : STime → E3) {K : ℝ} (hK : 0 ≤ K) (hb : ∀ z, ‖U z‖ ≤ K) (R : ℝ) :
    oscCyl U R ≤ 2 * K :=
  oscOn_le_two_mul hK fun z _ => hb z

/-- Every ancient spacetime point lies in a large enough parabolic cylinder. -/
lemma mem_parCyl_of_large {z : STime} (hz : z.1 ≤ 0) {R : ℝ}
    (h1 : ‖z.2‖ < R) (h2 : Real.sqrt (-z.1) < R) : z ∈ parCyl R := by
  refine ⟨?_, hz, h1⟩
  have hnn : 0 ≤ -z.1 := by linarith
  have hs : Real.sqrt (-z.1) ^ 2 = -z.1 := Real.sq_sqrt hnn
  have hR0 : 0 ≤ Real.sqrt (-z.1) := Real.sqrt_nonneg _
  have : Real.sqrt (-z.1) ^ 2 < R ^ 2 := by
    have := mul_self_lt_mul_self hR0 h2
    nlinarith
  rw [hs] at this
  linarith

/-- **Target D applied (C ⇒ constancy).**  A bounded field on
`ℝ³ × (−∞, 0]` whose parabolic-cylinder oscillation contracts by a fixed factor
is constant on the ancient region. -/
theorem ancient_constant_of_oscillation_contraction (U : STime → E3) {K theta sig : ℝ}
    (hK : 0 ≤ K) (hb : ∀ z, ‖U z‖ ≤ K)
    (hth0 : 0 < theta) (hth1 : theta < 1) (hs0 : 0 < sig) (hs1 : sig ≤ 1)
    (hcon : ∀ R, 0 < R → oscCyl U (theta * R) ≤ (1 - sig) * oscCyl U R) :
    ∃ b : E3, ∀ z : STime, z.1 ≤ 0 → U z = b := by
  have hzero : ∀ r, 0 < r → oscCyl U r = 0 :=
    eq_zero_of_geometric_contraction hth0 hth1 hs0 hs1 (oscCyl_nonneg U)
      (fun R => oscCyl_le U hK hb R) hcon
  refine ⟨U (0, 0), ?_⟩
  intro z hz
  set R : ℝ := max ‖z.2‖ (Real.sqrt (-z.1)) + 1 with hR
  have hR1 : ‖z.2‖ < R := by
    have := le_max_left ‖z.2‖ (Real.sqrt (-z.1)); rw [hR]; linarith
  have hR2 : Real.sqrt (-z.1) < R := by
    have := le_max_right ‖z.2‖ (Real.sqrt (-z.1)); rw [hR]; linarith
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg _) hR1
  have hzmem : z ∈ parCyl R := mem_parCyl_of_large hz hR1 hR2
  have h0mem : ((0:ℝ), (0:E3)) ∈ parCyl R := by
    refine ⟨?_, le_refl _, ?_⟩
    · have : 0 < R ^ 2 := by positivity
      linarith
    · simpa using hRpos
  have hbdd : Bornology.IsBounded (U '' parCyl R) := by
    refine (Metric.isBounded_closedBall (x := (0:E3)) (r := K)).subset ?_
    rintro p ⟨w, _, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hb w
  have := norm_sub_le_oscOn hbdd hzmem h0mem
  rw [show oscOn U (parCyl R) = oscCyl U R from rfl, hzero R hRpos] at this
  have hzz : ‖U z - U (0,0)‖ = 0 := le_antisymm this (norm_nonneg _)
  exact sub_eq_zero.1 (norm_eq_zero.1 hzz)

/-! ## The bottom of the dependency graph (§18) -/

/-- **R1 defect + oscillation contraction ⇒ ⊥.**  If a bounded ancient field
carries a nonzero oscillation defect on some spatial ball at time `0`
(the strengthened R1 conclusion), it cannot satisfy the scale-independent
oscillation contraction (C).  Equivalently: A/B + C close the route. -/
theorem false_of_defect_and_oscillation_contraction (U : STime → E3) {K theta sig R0 c0 : ℝ}
    (hK : 0 ≤ K) (hb : ∀ z, ‖U z‖ ≤ K)
    (hth0 : 0 < theta) (hth1 : theta < 1) (hs0 : 0 < sig) (hs1 : sig ≤ 1)
    (hcon : ∀ R, 0 < R → oscCyl U (theta * R) ≤ (1 - sig) * oscCyl U R)
    (hc0 : 0 < c0)
    (hdefect : c0 ≤ oscOn (fun x : E3 => U (0, x)) (Metric.ball 0 R0)) : False := by
  obtain ⟨b, hbconst⟩ :=
    ancient_constant_of_oscillation_contraction U hK hb hth0 hth1 hs0 hs1 hcon
  have hconst : (fun x : E3 => U (0, x)) = fun _ : E3 => b := by
    funext x; exact hbconst (0, x) (le_refl 0)
  rw [hconst, oscOn_const] at hdefect
  linarith

/-! ## Increments (§15) -/

/-- **The increment reformulation.**  A field is constant precisely when all of
its increments `δ_h U = U(· + h) − U(·)` vanish. -/
theorem constant_iff_increments_vanish (U : E3 → E3) :
    (∀ h x : E3, U (x + h) - U x = 0) ↔ ∃ b : E3, ∀ x, U x = b := by
  constructor
  · intro h
    refine ⟨U 0, fun x => ?_⟩
    have := h x 0
    simpa using sub_eq_zero.1 this
  · rintro ⟨b, hb⟩ h x
    simp [hb]

/-! ## Vanishing large-scale mean (§8, §9) -/

/-- A constant field with vanishing large-scale ball averages is zero. -/
theorem eq_zero_of_constant_of_vanishing_ball_average (U : E3 → E3) (b : E3)
    (hU : ∀ x, U x = b)
    (hmean : Tendsto (fun R : ℝ => ⨍ x in Metric.ball (0:E3) R, U x) atTop (𝓝 0)) :
    b = 0 := by
  have hev : (fun R : ℝ => ⨍ x in Metric.ball (0:E3) R, U x) =ᶠ[atTop] (fun _ => b) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    have h0 : (volume (Metric.ball (0:E3) R)) ≠ 0 :=
      ne_of_gt (measure_ball_pos volume 0 hR)
    have htop : (volume (Metric.ball (0:E3) R)) ≠ ⊤ :=
      ne_of_lt measure_ball_lt_top
    calc (⨍ x in Metric.ball (0:E3) R, U x)
        = ⨍ _x in Metric.ball (0:E3) R, b := by simp [hU]
      _ = b := setAverage_const h0 htop b
  have h1 : Tendsto (fun R : ℝ => ⨍ x in Metric.ball (0:E3) R, U x) atTop (𝓝 b) :=
    Tendsto.congr' hev.symm tendsto_const_nhds
  exact tendsto_nhds_unique h1 hmean

/-- **§8.**  The KNSŠ normalization `|U(0,0)| = 1` is incompatible with a
constant ancient limit *whose large-scale ball averages vanish*.  So, in the
presence of the periodic ancestry (which forces the rescaled box mean `m/M_k`
to tend to `0`), a Liouville theorem producing merely *some* constant already
closes the contradiction. -/
theorem false_of_unit_normalized_constant_with_vanishing_ball_average
    (U : STime → E3) (b : E3) (hconst : ∀ z : STime, z.1 ≤ 0 → U z = b)
    (hnorm : ‖U (0, 0)‖ = 1)
    (hmean : Tendsto (fun R : ℝ => ⨍ x in Metric.ball (0:E3) R, U (0, x)) atTop (𝓝 0)) :
    False := by
  have hb : b = 0 :=
    eq_zero_of_constant_of_vanishing_ball_average (fun x => U (0, x)) b
      (fun x => hconst (0, x) (le_refl 0)) hmean
  rw [hconst (0, 0) (le_refl 0), hb] at hnorm
  simp at hnorm

/-! ## The §10 scaling audit: no free damping from ancientness -/

/-- **§10, the no-go computation.**  On a torus of period `L_k = M L`, the
Poincaré (spectral gap) rate is `λ = 4π²/(M L)²`, and the KNSŠ rescaling gives
backward lifetime `A = M² t`.  The dimensionless damping `λ·A` equals
`4π² t / L²`: it is *independent of the blow-up factor* `M`.  Enlarging the
backward interval exactly compensates the vanishing spectral gap, so ancientness
alone provides no exponential annihilation at this scaling. -/
theorem poincare_rate_mul_backward_lifetime (L M t : ℝ) (hL : L ≠ 0) (hM : M ≠ 0) :
    (4 * Real.pi ^ 2 / (M * L) ^ 2) * (M ^ 2 * t) = 4 * Real.pi ^ 2 * t / L ^ 2 := by
  field_simp

/-! ## The assembled route (§18), modulo the two frontier inputs A and C -/

/-- **B + C ⇒ ⊥ from a sequence-level defect.**  If the rescaled fields carry a
uniform oscillation defect `c₀` on a ball, converge uniformly there to the time
`0` slice of a bounded ancient field `U`, and `U` satisfies the scale-independent
oscillation contraction, then a contradiction follows. -/
theorem false_of_sequence_defect_and_contraction (v : ℕ → E3 → E3) (U : STime → E3)
    {K theta sig R0 c0 : ℝ} (hK : 0 ≤ K) (hb : ∀ z, ‖U z‖ ≤ K)
    (hth0 : 0 < theta) (hth1 : theta < 1) (hs0 : 0 < sig) (hs1 : sig ≤ 1)
    (hcon : ∀ R, 0 < R → oscCyl U (theta * R) ≤ (1 - sig) * oscCyl U R)
    (hc0 : 0 < c0)
    (hconv : ∀ eps > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ y ∈ Metric.ball (0 : E3) R0,
      ‖v k y - U (0, y)‖ ≤ eps)
    (hdef : ∀ k, c0 ≤ oscOn (v k) (Metric.ball 0 R0)) : False := by
  have hbU : Bornology.IsBounded ((fun y : E3 => U (0, y)) '' Metric.ball (0 : E3) R0) := by
    refine (Metric.isBounded_closedBall (x := (0 : E3)) (r := K)).subset ?_
    rintro p ⟨w, _, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hb (0, w)
  have hdefU : c0 ≤ oscOn (fun y : E3 => U (0, y)) (Metric.ball 0 R0) :=
    oscOn_ge_of_uniform_limit hbU hconv hdef
  exact false_of_defect_and_oscillation_contraction U hK hb hth0 hth1 hs0 hs1 hcon hc0 hdefU

/-- **The revised dependency graph of §18, assembled.**  Inputs:

* `hA` — the *physical* velocity-scale oscillation defect
  `osc_{B_{R₀/M_k}(x_k)} u_k ≥ c₀ M_k` (target **A**, the frontier item: this is
  `SingularScaleVelocityScaleMatching` in oscillation form);
* `hB` — uniform convergence of the rescaled fields on `B_{R₀}` to the time-`0`
  slice of a bounded ancient field `U` (target **B**, compactness);
* `hC` — the scale-independent oscillation contraction for `U` (target **C**).

Conclusion: contradiction.  Hence no such configuration exists, which is exactly
the blow-up exclusion the route asks for.  Nothing here is postulated: `A`, `B`
and `C` appear as explicit hypotheses, and `D` (the iteration) is proved. -/
theorem clay_blowup_route_contradiction (u : ℕ → E3 → E3) (M : ℕ → ℝ) (x : ℕ → E3)
    (U : STime → E3) {K theta sig R0 c0 : ℝ}
    (hM : ∀ k, 0 < M k) (hK : 0 ≤ K) (hb : ∀ z, ‖U z‖ ≤ K)
    (hth0 : 0 < theta) (hth1 : theta < 1) (hs0 : 0 < sig) (hs1 : sig ≤ 1) (hc0 : 0 < c0)
    (hA : ∀ k, c0 * M k ≤ oscOn (u k) (Metric.ball (x k) ((M k)⁻¹ * R0)))
    (hB : ∀ eps > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ y ∈ Metric.ball (0 : E3) R0,
      ‖blowupSpace (u k) (M k) (x k) y - U (0, y)‖ ≤ eps)
    (hC : ∀ R, 0 < R → oscCyl U (theta * R) ≤ (1 - sig) * oscCyl U R) : False := by
  have hdef : ∀ k, c0 ≤ oscOn (blowupSpace (u k) (M k) (x k)) (Metric.ball 0 R0) := fun k =>
    (oscOn_blowupSpace_ge_iff (u k) (hM k) (x k) R0 c0).2 (hA k)
  exact false_of_sequence_defect_and_contraction
    (fun k => blowupSpace (u k) (M k) (x k)) U hK hb hth0 hth1 hs0 hs1 hC hc0 hB hdef

/-! ## Reduction of C to a single unit-scale improvement (§17) -/

/-- The parabolic (Navier–Stokes) rescaling of a spacetime field:
`U_λ(y,s) = λ U(λy, λ²s)`. -/
def parRescale (U : STime → E3) (lam : ℝ) : STime → E3 :=
  fun z => lam • U (lam ^ 2 * z.1, lam • z.2)

lemma image_parCyl {lam : ℝ} (hlam : 0 < lam) (R : ℝ) :
    (fun z : STime => (lam ^ 2 * z.1, lam • z.2)) '' parCyl R = parCyl (lam * R) := by
  have hlam2 : (0:ℝ) < lam ^ 2 := by positivity
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hz
    refine ⟨?_, ?_, ?_⟩
    · have : lam ^ 2 * (-(R ^ 2)) < lam ^ 2 * z.1 := mul_lt_mul_of_pos_left h1 hlam2
      calc -((lam * R) ^ 2) = lam ^ 2 * (-(R ^ 2)) := by ring
        _ < lam ^ 2 * z.1 := this
    · exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hlam2) h2
    · have hn : ‖lam • z.2‖ = lam * ‖z.2‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
      rw [hn]
      exact mul_lt_mul_of_pos_left h3 hlam
  · intro hw
    obtain ⟨h1, h2, h3⟩ := hw
    refine ⟨((lam ^ 2)⁻¹ * w.1, lam⁻¹ • w.2), ⟨?_, ?_, ?_⟩, ?_⟩
    · have hlt : (lam ^ 2)⁻¹ * (-((lam * R) ^ 2)) < (lam ^ 2)⁻¹ * w.1 :=
        mul_lt_mul_of_pos_left h1 (inv_pos.mpr hlam2)
      have heq : (lam ^ 2)⁻¹ * (-((lam * R) ^ 2)) = -(R ^ 2) := by
        field_simp
      rw [heq] at hlt
      exact hlt
    · exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (inv_pos.mpr hlam2)) h2
    · have hn : ‖lam⁻¹ • w.2‖ = lam⁻¹ * ‖w.2‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam)]
      rw [hn]
      have := mul_lt_mul_of_pos_left h3 (inv_pos.mpr hlam)
      rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hlam), one_mul] at this
    · have h1' : lam ^ 2 * ((lam ^ 2)⁻¹ * w.1) = w.1 := by
        field_simp
      have h2' : lam • (lam⁻¹ • w.2) = w.2 := by
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hlam), one_smul]
      simp [h1', h2']

/-- The parabolic rescaling of the cylinder oscillation:
`osc_{Q_R} U_λ = λ · osc_{Q_{λR}} U`. -/
theorem oscCyl_parRescale (U : STime → E3) {lam : ℝ} (hlam : 0 < lam) (R : ℝ) :
    oscCyl (parRescale U lam) R = lam * oscCyl U (lam * R) := by
  have h1 : oscCyl (parRescale U lam) R
      = |lam| * oscOn (fun z : STime => U (lam ^ 2 * z.1, lam • z.2)) (parCyl R) :=
    oscOn_smul _ _ _
  rw [h1, oscOn_comp U (fun z : STime => (lam ^ 2 * z.1, lam • z.2)), image_parCyl hlam,
    abs_of_pos hlam]
  rfl

/-- **C reduces to one unit-scale improvement.**  If a class of fields is closed
under the parabolic rescaling and every member improves its oscillation once,
from scale `1` to scale `θ`, then every member satisfies the scale-independent
contraction at *every* scale — which by
`ancient_constant_of_oscillation_contraction` forces constancy.  This is the
precise sense in which the frontier item C is a single estimate, not a family
of them. -/
theorem contraction_of_unit_step (Cls : (STime → E3) → Prop) {theta sig : ℝ}
    (hclosed : ∀ (U : STime → E3) (lam : ℝ), Cls U → 0 < lam → Cls (parRescale U lam))
    (hstep : ∀ U : STime → E3, Cls U → oscCyl U theta ≤ (1 - sig) * oscCyl U 1)
    (U : STime → E3) (hU : Cls U) {R : ℝ} (hR : 0 < R) :
    oscCyl U (theta * R) ≤ (1 - sig) * oscCyl U R := by
  have hUR : Cls (parRescale U R) := hclosed U R hU hR
  have h := hstep (parRescale U R) hUR
  rw [oscCyl_parRescale U hR theta, oscCyl_parRescale U hR 1, mul_one] at h
  have hfinal : oscCyl U (R * theta) ≤ (1 - sig) * oscCyl U R :=
    le_of_mul_le_mul_left
      (by linarith : R * oscCyl U (R * theta) ≤ R * ((1 - sig) * oscCyl U R)) hR
  rwa [mul_comm theta R]

end ClayNS
