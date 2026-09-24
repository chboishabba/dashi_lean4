/-
# Rigidity branches for a hypothetical critical element

The critical-element strategy reduces a hypothetical failure of a critical
spacetime bound to a single *minimal* trajectory whose critical size stays
bounded away from zero, and which is compact modulo the symmetries.  The
scenario decomposition then asks which of the branches

* a **soliton-like** orbit (bounded frequency scale), and
* a **frequency cascade** (the concentration scale runs off to infinity)

can be killed by the energy theorem alone, before any backward-uniqueness input
is needed.

This file settles both branches for the literal Galerkin carrier of the Waleffe
lane (`ClayNS.Waleffe.GalerkinFlow`), and it does so *without* any compactness
hypothesis, by interpolation:

* `GalerkinFlow.critEnergy_sq_le_energy_mul_dissipation` — the exact Cauchy–Schwarz
  interpolation `(∑_k |k|‖u_k‖²)² ≤ (∑_k ‖u_k‖²)(∑_k |k|²‖u_k‖²)`, i.e.
  `‖u‖_{Ḣ^{1/2}}⁴ ≤ ‖u‖_{L²}² ‖u‖_{Ḣ¹}²`, on the finite mode set;
* `GalerkinFlow.dissipation_ge_of_critEnergy_floor` — hence a **positive
  dissipation floor**: a trajectory whose critical energy never drops below
  `K > 0` has `𝔇(t) ≥ K²/E(t) ≥ K²/E(t₀)`;
* `GalerkinFlow.lifetime_bound_of_critEnergy_floor` — combined with the energy
  balance `E(t₁) + 2ν∫𝔇 = E(t₀)`, the floor can be sustained only for a bounded
  time: `t₁ − t₀ ≤ E(t₀)²/(2νK²)`;
* `GalerkinFlow.volume_critEnergy_ge_le` — the measure-theoretic form: for every
  terminal time `T` and threshold `K > 0`, the set of times in `[0,T]` where the
  critical energy is at least `K` has Lebesgue measure at most `E(0)²/(2νK²)`,
  independently of `T` and of the cutoff;
* `GalerkinFlow.no_eternal_critical_element` — so there is **no** eternal
  trajectory of the truncated system keeping its critical energy above a fixed
  positive level.  This kills the soliton-like branch outright, with no
  compactness, no almost periodicity and no backward uniqueness;
* `GalerkinFlow.integral_critEnergy_sq_le` — unconditionally,
  `∫ (∑_k |k|‖u_k‖²)² dt ≤ E(t₀)²/(2ν)`, uniformly in the terminal time and in
  the cutoff (in continuum notation `u ∈ L⁴_t Ḣ^{1/2}_x`);
* `GalerkinFlow.integral_le_of_pointwise_critEnergy_dissipation_bound` — the
  conditional defect budget: any density dominated pointwise by `C·E₁₂·𝔇` is
  paid by `C·K·E(t₀)/(2ν)` on a window where `E₁₂ ≤ K`, so the missing input for
  a spacetime estimate of that shape is the uniform-in-time critical bound `K`,
  not the energy budget;
* `GalerkinFlow.lifetime_bound_of_frequency_cascade` — in the cascade branch,
  where the energy of the concentrating profile obeys `E(t) ≤ C/N`, the same
  argument gives the much shorter lifetime `C·E(t₀)/(2νK²N)`, which tends to `0`
  as `N → ∞`.

The compactness route the scenario decomposition suggests is also recorded, in
its correct general form, and shown to be strictly weaker in this setting:

* `exists_floor_of_compact_orbit` — a continuous positive functional on a compact
  set has a positive floor along any orbit contained in it;
* `false_of_positive_floor_of_budget` — a positive floor is incompatible with a
  finite time-integrated budget;
* `GalerkinFlow.no_compact_orbit_of_positive_dissipation` — their instantiation
  on the Galerkin carrier.

**What this does not do.**  Everything here is a statement about the truncated
(Galerkin) system, whose constants are cutoff-uniform but whose conclusions are
about the critical *energy* `∑_k |k|‖u_k‖²`, not about the missing spacetime
estimate for the mixed-helicity defect.  In particular the branch that the
scenario decomposition leaves for a backward-uniqueness argument — finite-time
concentration — is untouched, and no claim is made about the Clay target.
-/
import RequestProject.NavierStokes.WaleffeCriticalEnergyBarrier

noncomputable section

open Finset

namespace ClayNS.Waleffe

/-! ## The abstract compactness route -/

/-- A continuous, strictly positive functional on a compact set has a positive
floor along any orbit that stays inside that set.  This is the general form of
the step "nonzero compact orbit ⇒ positive dissipation floor". -/
theorem exists_floor_of_compact_orbit {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsCompact S) {D : X → ℝ} (hD : ContinuousOn D S) (hpos : ∀ x ∈ S, 0 < D x)
    {u : ℝ → X} (hu : ∀ t, u t ∈ S) :
    ∃ c > 0, ∀ t, c ≤ D (u t) := by
  obtain ⟨x₀, hx₀S, hmin⟩ := hS.exists_isMinOn ⟨u 0, hu 0⟩ hD
  exact ⟨D x₀, hpos _ hx₀S, fun t => isMinOn_iff.1 hmin _ (hu t)⟩

/-- A positive floor is incompatible with a finite time-integrated budget: if
`f ≥ c > 0` everywhere and `∫₀^T f ≤ B` for every `T ≥ 0`, there is a
contradiction. -/
theorem false_of_positive_floor_of_budget {f : ℝ → ℝ} (hf : Continuous f) {c B : ℝ}
    (hc : 0 < c) (hfloor : ∀ t, c ≤ f t)
    (hbudget : ∀ T : ℝ, 0 ≤ T → (∫ t in (0:ℝ)..T, f t) ≤ B) : False := by
  set T : ℝ := (|B| + 1) / c with hT
  have hT0 : 0 ≤ T := by positivity
  have hlow : (∫ t in (0:ℝ)..T, c) ≤ ∫ t in (0:ℝ)..T, f t := by
    refine intervalIntegral.integral_mono_on hT0 (intervalIntegrable_const)
      (hf.intervalIntegrable _ _) ?_
    intro x _
    exact hfloor x
  rw [intervalIntegral.integral_const] at hlow
  have hval : (T - 0) • c = |B| + 1 := by
    simp only [sub_zero, smul_eq_mul, hT]
    field_simp
  rw [hval] at hlow
  have := hbudget T hT0
  have hB : B ≤ |B| := le_abs_self B
  linarith

namespace GalerkinFlow

variable (G : GalerkinFlow)

/-! ## The interpolation floor -/

/-- **Interpolation on the literal carrier.**  `(∑_k |k| ‖u_k‖²)² ≤
(∑_k ‖u_k‖²)(∑_k |k|² ‖u_k‖²)`, i.e. `‖u‖_{Ḣ^{1/2}}⁴ ≤ ‖u‖_{L²}²‖u‖_{Ḣ¹}²`;
a Cauchy–Schwarz identity on the finite mode set, with no cutoff dependence. -/
theorem critEnergy_sq_le_energy_mul_dissipation (t : ℝ) :
    (G.critEnergy t) ^ 2 ≤ G.energy t * G.dissipation t := by
  classical
  set f : Wave → ℝ := fun k => Real.sqrt (nsq (G.u t k)) with hf
  set g : Wave → ℝ := fun k => Real.sqrt (wsq k * nsq (G.u t k)) with hg
  have hfg : ∀ k ∈ G.modes, f k * g k = wlen k * nsq (G.u t k) := by
    intro k _
    have ha : 0 ≤ nsq (G.u t k) := nsq_nonneg _
    have hval : nsq (G.u t k) * (wsq k * nsq (G.u t k)) = wsq k * nsq (G.u t k) ^ 2 := by ring
    rw [hf, hg, ← Real.sqrt_mul ha, hval, Real.sqrt_mul (wsq_nonneg k), Real.sqrt_sq ha]
    rfl
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq G.modes f g
  have hfsq : ∑ k ∈ G.modes, f k ^ 2 = G.energy t := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hf]
    exact Real.sq_sqrt (nsq_nonneg _)
  have hgsq : ∑ k ∈ G.modes, g k ^ 2 = G.dissipation t := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hg]
    exact Real.sq_sqrt (mul_nonneg (wsq_nonneg k) (nsq_nonneg _))
  have hleft : ∑ k ∈ G.modes, f k * g k = G.critEnergy t := by
    rw [critEnergy]
    exact Finset.sum_congr rfl hfg
  rw [hleft, hfsq, hgsq] at hcs
  exact hcs

/-- A trajectory with positive critical energy has positive energy. -/
theorem energy_pos_of_critEnergy_pos {t : ℝ} (h : 0 < G.critEnergy t) : 0 < G.energy t := by
  rcases (G.energy_nonneg t).lt_or_eq with h1 | h1
  · exact h1
  · exfalso
    have hint := G.critEnergy_sq_le_energy_mul_dissipation t
    rw [← h1, zero_mul] at hint
    nlinarith

/-- **The dissipation floor.**  If the critical energy is at least `K` and the
energy is at most `M`, the dissipation is at least `K²/M`.  No compactness, no
almost periodicity: the floor is pure interpolation. -/
theorem dissipation_ge_of_critEnergy_floor {t K M : ℝ} (hK : 0 < K) (hM : 0 < M)
    (hcrit : K ≤ G.critEnergy t) (hen : G.energy t ≤ M) :
    K ^ 2 / M ≤ G.dissipation t := by
  have hint := G.critEnergy_sq_le_energy_mul_dissipation t
  have hD0 : 0 ≤ G.dissipation t := G.dissipation_nonneg t
  have hsq : K ^ 2 ≤ (G.critEnergy t) ^ 2 := by nlinarith [G.critEnergy_nonneg t]
  rw [div_le_iff₀ hM]
  nlinarith

/-! ## The energy budget -/

/-- **The floor–budget inequality.**  A dissipation floor `c` on `[t₀,t₁]` costs
`(t₁ − t₀)·c` of the total dissipation budget `E(t₀)/(2ν)`. -/
theorem time_mul_floor_le (hnu : 0 < G.nu) {t₀ t₁ c : ℝ} (h : t₀ ≤ t₁)
    (hfl : ∀ x ∈ Set.Icc t₀ t₁, c ≤ G.dissipation x) :
    (t₁ - t₀) * c ≤ G.energy t₀ / (2 * G.nu) := by
  have hlow : (∫ _t in t₀..t₁, c) ≤ ∫ t in t₀..t₁, G.dissipation t :=
    intervalIntegral.integral_mono_on h (continuous_const.intervalIntegrable _ _)
      (G.continuous_dissipation.intervalIntegrable _ _) hfl
  rw [intervalIntegral.integral_const, smul_eq_mul] at hlow
  linarith [G.integral_dissipation_le t₀ t₁ hnu]

/-! ## The soliton branch -/

/-- **Bounded lifetime of a critical-energy floor.**  A Galerkin trajectory whose
critical energy stays at or above `K > 0` throughout `[t₀,t₁]` satisfies
`t₁ − t₀ ≤ E(t₀)²/(2νK²)`.  The bound involves only the initial energy, the
viscosity and the threshold — no cutoff, no mode count. -/
theorem lifetime_bound_of_critEnergy_floor (hnu : 0 < G.nu) {t₀ t₁ K : ℝ} (h : t₀ ≤ t₁)
    (hK : 0 < K) (hfloor : ∀ t ∈ Set.Icc t₀ t₁, K ≤ G.critEnergy t) :
    t₁ - t₀ ≤ G.energy t₀ ^ 2 / (2 * G.nu * K ^ 2) := by
  have hcrit0 : K ≤ G.critEnergy t₀ := hfloor t₀ (Set.mem_Icc.2 ⟨le_rfl, h⟩)
  have hE0 : 0 < G.energy t₀ := G.energy_pos_of_critEnergy_pos (lt_of_lt_of_le hK hcrit0)
  -- pointwise floor for the dissipation on the interval
  have hfl : ∀ x ∈ Set.Icc t₀ t₁, K ^ 2 / G.energy t₀ ≤ G.dissipation x := by
    intro x hx
    exact G.dissipation_ge_of_critEnergy_floor hK hE0 (hfloor x hx)
      (G.energy_le_initial (Set.mem_Icc.1 hx).1)
  have hkey := G.time_mul_floor_le hnu h hfl
  have h4 : (t₁ - t₀) * (K ^ 2 / G.energy t₀) * (2 * G.nu * G.energy t₀)
      ≤ G.energy t₀ / (2 * G.nu) * (2 * G.nu * G.energy t₀) :=
    mul_le_mul_of_nonneg_right hkey (by positivity)
  have hE0' : G.energy t₀ ≠ 0 := ne_of_gt hE0
  have hnu' : G.nu ≠ 0 := ne_of_gt hnu
  field_simp at h4
  rw [le_div_iff₀ (by positivity)]
  nlinarith [h4]

/-- **No eternal critical element.**  No Galerkin trajectory can keep its
critical energy above a fixed positive level for all time: the soliton-like
branch of the scenario decomposition is empty, by the energy theorem alone. -/
theorem no_eternal_critical_element (hnu : 0 < G.nu) {t₀ K : ℝ} (hK : 0 < K)
    (hfloor : ∀ t, t₀ ≤ t → K ≤ G.critEnergy t) : False := by
  set B : ℝ := G.energy t₀ ^ 2 / (2 * G.nu * K ^ 2) with hB
  have hB0 : 0 ≤ B := by
    have : (0:ℝ) ≤ G.energy t₀ ^ 2 := sq_nonneg _
    positivity
  have hle : t₀ + B + 1 - t₀ ≤ B :=
    G.lifetime_bound_of_critEnergy_floor hnu (by linarith) hK
      (fun t ht => hfloor t (Set.mem_Icc.1 ht).1)
  linarith

/-- **The critical energy must drop.**  Equivalently: on any interval longer than
`E(t₀)²/(2νK²)` the critical energy dips strictly below `K`. -/
theorem exists_critEnergy_lt_of_long_interval (hnu : 0 < G.nu) {t₀ t₁ K : ℝ} (hK : 0 < K)
    (h : t₀ ≤ t₁) (hlong : G.energy t₀ ^ 2 / (2 * G.nu * K ^ 2) < t₁ - t₀) :
    ∃ t ∈ Set.Icc t₀ t₁, G.critEnergy t < K := by
  by_contra hcon
  push_neg at hcon
  exact absurd (G.lifetime_bound_of_critEnergy_floor hnu h hK hcon) (not_le.2 hlong)

/-- **A cutoff-uniform spacetime bound for the critical energy.**  Interpolation
against the energy budget gives `∫_{t₀}^{t₁} (∑_k |k|‖u_k‖²)² dt ≤ E(t₀)²/(2ν)`,
with no dependence on the terminal time or on the Galerkin cutoff.  (In
continuum notation: `u ∈ L⁴_t Ḣ^{1/2}_x`, with the Leray energy constant.) -/
theorem integral_critEnergy_sq_le (hnu : 0 < G.nu) {t₀ t₁ : ℝ} (h : t₀ ≤ t₁) :
    (∫ t in t₀..t₁, (G.critEnergy t) ^ 2) ≤ G.energy t₀ ^ 2 / (2 * G.nu) := by
  have hmono : (∫ t in t₀..t₁, (G.critEnergy t) ^ 2)
      ≤ ∫ t in t₀..t₁, G.energy t₀ * G.dissipation t := by
    refine intervalIntegral.integral_mono_on h
      ((G.continuous_critEnergy.pow 2).intervalIntegrable _ _)
      ((continuous_const.mul G.continuous_dissipation).intervalIntegrable _ _) ?_
    intro x hx
    have hint := G.critEnergy_sq_le_energy_mul_dissipation x
    have hE : G.energy x ≤ G.energy t₀ := G.energy_le_initial (Set.mem_Icc.1 hx).1
    nlinarith [G.dissipation_nonneg x]
  rw [intervalIntegral.integral_const_mul] at hmono
  have hbud := G.integral_dissipation_le t₀ t₁ hnu
  have hE0 : 0 ≤ G.energy t₀ := G.energy_nonneg t₀
  have hstep : G.energy t₀ * (∫ t in t₀..t₁, G.dissipation t)
      ≤ G.energy t₀ * (G.energy t₀ / (2 * G.nu)) := mul_le_mul_of_nonneg_left hbud hE0
  have hval : G.energy t₀ * (G.energy t₀ / (2 * G.nu)) = G.energy t₀ ^ 2 / (2 * G.nu) := by
    field_simp
  linarith [hval ▸ hstep]

/-- **The conditional defect budget.**  Any spacetime density `Q` dominated
pointwise by `C·E₁₂(t)·𝔇(t)` has, on a time window where the critical energy stays
below `K`, the cutoff-uniform budget `∫ Q ≤ C·K·E(t₀)/(2ν)`.  This isolates the
missing input for a spacetime defect estimate of that shape: not the energy
budget, which is supplied here, but the uniform-in-time critical bound `K`. -/
theorem integral_le_of_pointwise_critEnergy_dissipation_bound (hnu : 0 < G.nu)
    {t₀ t₁ C K : ℝ} (h : t₀ ≤ t₁) (hC : 0 ≤ C) {Q : ℝ → ℝ} (hQ : Continuous Q)
    (hpt : ∀ t ∈ Set.Icc t₀ t₁, Q t ≤ C * G.critEnergy t * G.dissipation t)
    (hK : ∀ t ∈ Set.Icc t₀ t₁, G.critEnergy t ≤ K) :
    (∫ t in t₀..t₁, Q t) ≤ C * K * (G.energy t₀ / (2 * G.nu)) := by
  have hK0 : 0 ≤ K :=
    le_trans (G.critEnergy_nonneg t₀) (hK t₀ (Set.mem_Icc.2 ⟨le_rfl, h⟩))
  have hmono : (∫ t in t₀..t₁, Q t) ≤ ∫ t in t₀..t₁, C * K * G.dissipation t := by
    refine intervalIntegral.integral_mono_on h (hQ.intervalIntegrable _ _)
      ((continuous_const.mul G.continuous_dissipation).intervalIntegrable _ _) ?_
    intro x hx
    have h1 := hpt x hx
    have h3 : G.critEnergy x * G.dissipation x ≤ K * G.dissipation x :=
      mul_le_mul_of_nonneg_right (hK x hx) (G.dissipation_nonneg x)
    calc Q x ≤ C * G.critEnergy x * G.dissipation x := h1
      _ = C * (G.critEnergy x * G.dissipation x) := by ring
      _ ≤ C * (K * G.dissipation x) := mul_le_mul_of_nonneg_left h3 hC
      _ = C * K * G.dissipation x := by ring
  rw [intervalIntegral.integral_const_mul] at hmono
  have hbud := G.integral_dissipation_le t₀ t₁ hnu
  have hfin : C * K * (∫ t in t₀..t₁, G.dissipation t) ≤ C * K * (G.energy t₀ / (2 * G.nu)) :=
    mul_le_mul_of_nonneg_left hbud (mul_nonneg hC hK0)
  linarith

/-- A configuration of zero energy has zero critical energy. -/
theorem critEnergy_eq_zero_of_energy_eq_zero {t : ℝ} (h : G.energy t = 0) :
    G.critEnergy t = 0 := by
  have hint := G.critEnergy_sq_le_energy_mul_dissipation t
  rw [h, zero_mul] at hint
  nlinarith [G.critEnergy_nonneg t]

/-- **The critical energy is large only on a set of bounded measure.**  For every
terminal time `T` and every threshold `K > 0`, the set of times in `[0,T]` at
which the critical energy is at least `K` has Lebesgue measure at most
`E(0)²/(2νK²)` — a bound independent of `T` and of the Galerkin cutoff.  This is
the measure-theoretic form of the lifetime bound, and it does not require the
floor to be sustained on an interval. -/
theorem volume_critEnergy_ge_le (hnu : 0 < G.nu) {T K : ℝ} (hT : 0 ≤ T) (hK : 0 < K) :
    (MeasureTheory.volume (Set.Icc (0:ℝ) T ∩ {t | K ≤ G.critEnergy t})).toReal
      ≤ G.energy 0 ^ 2 / (2 * G.nu * K ^ 2) := by
  classical
  set S : Set ℝ := Set.Icc (0:ℝ) T ∩ {t | K ≤ G.critEnergy t} with hSdef
  have hmeas : MeasurableSet S :=
    measurableSet_Icc.inter (isClosed_le continuous_const G.continuous_critEnergy).measurableSet
  have hsub : S ⊆ Set.Icc (0:ℝ) T := Set.inter_subset_left
  have hfin : MeasureTheory.volume S ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (MeasureTheory.measure_mono hsub)
  rcases (G.energy_nonneg 0).lt_or_eq with hE0 | hE0
  · -- positive initial energy: the dissipation floor applies on `S`
    have hfl : ∀ x ∈ S, K ^ 2 / G.energy 0 ≤ G.dissipation x := by
      intro x hx
      exact G.dissipation_ge_of_critEnergy_floor hK hE0 hx.2
        (G.energy_le_initial (Set.mem_Icc.1 hx.1).1)
    have hintIcc : MeasureTheory.IntegrableOn G.dissipation (Set.Icc (0:ℝ) T) :=
      G.continuous_dissipation.integrableOn_Icc
    have hintS : MeasureTheory.IntegrableOn G.dissipation S := hintIcc.mono_set hsub
    have hlow : K ^ 2 / G.energy 0 * (MeasureTheory.volume S).toReal
        ≤ ∫ x in S, G.dissipation x :=
      MeasureTheory.setIntegral_ge_of_const_le_real hmeas hfin hfl hintS
    have hmid : (∫ x in S, G.dissipation x) ≤ ∫ x in Set.Icc (0:ℝ) T, G.dissipation x := by
      refine MeasureTheory.setIntegral_mono_set hintIcc ?_ (MeasureTheory.ae_of_all _ hsub)
      exact MeasureTheory.ae_of_all _ fun x => G.dissipation_nonneg x
    have hIcc : (∫ x in Set.Icc (0:ℝ) T, G.dissipation x) = ∫ t in (0:ℝ)..T, G.dissipation t := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hT]
    have hbud := G.integral_dissipation_le 0 T hnu
    have hkey : K ^ 2 / G.energy 0 * (MeasureTheory.volume S).toReal
        ≤ G.energy 0 / (2 * G.nu) := by
      rw [hIcc] at hmid
      linarith
    have h4 : K ^ 2 / G.energy 0 * (MeasureTheory.volume S).toReal * (2 * G.nu * G.energy 0)
        ≤ G.energy 0 / (2 * G.nu) * (2 * G.nu * G.energy 0) :=
      mul_le_mul_of_nonneg_right hkey (by positivity)
    have hE0' : G.energy 0 ≠ 0 := ne_of_gt hE0
    have hnu' : G.nu ≠ 0 := ne_of_gt hnu
    field_simp at h4
    rw [le_div_iff₀ (by positivity)]
    nlinarith [h4]
  · -- zero initial energy: the set is empty
    have hempty : S = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
      have hx0 : G.energy x ≤ 0 := by
        have := G.energy_le_initial (Set.mem_Icc.1 hx.1).1
        rw [← hE0] at this
        exact this
      have hxz : G.energy x = 0 := le_antisymm hx0 (G.energy_nonneg x)
      have hz := G.critEnergy_eq_zero_of_energy_eq_zero hxz
      have hmem : K ≤ G.critEnergy x := hx.2
      rw [hz] at hmem
      linarith
    rw [hempty]
    simp [← hE0]

/-! ## The frequency-cascade branch -/

/-- **Cascade lifetime.**  If, in addition, the trajectory concentrates at
frequency scale `N` in the sense that its energy obeys `E(t) ≤ C/N` on the
interval, then the same critical-energy floor can be sustained only for a time
`≤ C·E(t₀)/(2νK²N)`, which tends to `0` as the concentration scale `N → ∞`. -/
theorem lifetime_bound_of_frequency_cascade (hnu : 0 < G.nu) {t₀ t₁ K C N : ℝ} (h : t₀ ≤ t₁)
    (hK : 0 < K) (hC : 0 < C) (hN : 0 < N)
    (hfloor : ∀ t ∈ Set.Icc t₀ t₁, K ≤ G.critEnergy t)
    (hscale : ∀ t ∈ Set.Icc t₀ t₁, G.energy t ≤ C / N) :
    t₁ - t₀ ≤ C * G.energy t₀ / (2 * G.nu * K ^ 2 * N) := by
  have hCN : 0 < C / N := by positivity
  have hfl : ∀ x ∈ Set.Icc t₀ t₁, K ^ 2 * N / C ≤ G.dissipation x := by
    intro x hx
    have hrw : K ^ 2 / (C / N) = K ^ 2 * N / C := by field_simp
    rw [← hrw]
    exact G.dissipation_ge_of_critEnergy_floor hK hCN (hfloor x hx) (hscale x hx)
  have hkey := G.time_mul_floor_le hnu h hfl
  have h4 : (t₁ - t₀) * (K ^ 2 * N / C) * (2 * G.nu * C)
      ≤ G.energy t₀ / (2 * G.nu) * (2 * G.nu * C) :=
    mul_le_mul_of_nonneg_right hkey (by positivity)
  have hCne : C ≠ 0 := ne_of_gt hC
  have hnu' : G.nu ≠ 0 := ne_of_gt hnu
  field_simp at h4
  rw [le_div_iff₀ (by positivity)]
  nlinarith [h4]

/-! ## The compactness route, for comparison -/

/-- The dissipation as a functional of a Fourier configuration. -/
def dissipationOf (modes : Finset Wave) (v : Wave → Fin 3 → ℂ) : ℝ :=
  ∑ k ∈ modes, wsq k * nsq (v k)

theorem continuous_dissipationOf (modes : Finset Wave) :
    Continuous (dissipationOf modes) := by
  refine continuous_finset_sum _ fun k _ => continuous_const.mul ?_
  refine continuous_finset_sum _ fun i _ => ?_
  exact Complex.continuous_normSq.comp ((continuous_apply i).comp (continuous_apply k))

theorem dissipationOf_u (t : ℝ) : dissipationOf G.modes (G.u t) = G.dissipation t := rfl

/-- **The compactness route on the Galerkin carrier.**  A trajectory that stays
in a compact set of configurations on which the dissipation is strictly positive
cannot exist for all forward time.  This is the general "compact orbit ⇒
dissipation floor ⇒ infinite budget" argument; on this carrier it is strictly
weaker than `no_eternal_critical_element`, which needs no compactness at all. -/
theorem no_compact_orbit_of_positive_dissipation (hnu : 0 < G.nu)
    {S : Set (Wave → Fin 3 → ℂ)} (hS : IsCompact S)
    (hpos : ∀ v ∈ S, 0 < dissipationOf G.modes v) (hu : ∀ t, G.u t ∈ S) : False := by
  obtain ⟨c, hc, hfloor⟩ :=
    exists_floor_of_compact_orbit hS (continuous_dissipationOf G.modes).continuousOn hpos hu
  exact false_of_positive_floor_of_budget (B := G.energy 0 / (2 * G.nu))
    G.continuous_dissipation hc (fun t => hfloor t)
    (fun T hT => G.integral_dissipation_le 0 T hnu)

end GalerkinFlow

end ClayNS.Waleffe
