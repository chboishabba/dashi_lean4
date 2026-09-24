/-
# The physical constraints are preserved by the Galerkin flow

A `ClayNS.Waleffe.GalerkinFlow` carries three *kinematic* constraints — support
on the retained modes, incompressibility (transversality) and the reality
condition of a real velocity field — at **every** time.  For a constructed
trajectory these have to be *proved* to propagate, and that is what this file
does, for the cut-off field of `GalerkinTruncatedField.lean` (hence also for the
literal field, which agrees with it below the cutoff).

* Transversality propagates because the projected forcing is Leray-transverse:
  the scalar `⟪k, u_k⟫` obeys the *linear* damped equation `ċ = −φ ν|k|² c`, so
  it vanishes identically once it vanishes initially.

* The reality condition propagates by an equivariance argument: the reflection
  `(𝓡v)_k = conj v_{−k}` commutes with the vector field, so `t ↦ 𝓡(α t)` solves
  the same ODE with the same initial value, and ODE uniqueness forces
  `𝓡(α t) = α t`.

Neither statement uses the energy; they are used *before* the energy estimate in
`GalerkinExistence.lean`, which needs them via energy neutrality.
-/
import RequestProject.NavierStokes.GalerkinTruncatedField
import Mathlib.Analysis.ODE.Gronwall

noncomputable section

open Set

namespace ClayNS.GalerkinODE

open ClayNS.Waleffe

variable {modes : Finset Wave}

/-! ## Coordinates of a solution -/

/-- Evaluation of a state at one mode and one component, as a continuous linear
map. -/
def coordCLM (k : ↥modes) (i : Fin 3) : State modes →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥modes => Fin 3 → ℂ) k)

theorem hasDerivAt_coord {α : ℝ → State modes} {d : State modes} {t : ℝ}
    (h : HasDerivAt α d t) (k : ↥modes) (i : Fin 3) :
    HasDerivAt (fun s => α s k i) (d k i) t := by
  have := (coordCLM k i).hasFDerivAt.comp_hasDerivAt t h
  simpa [coordCLM, Function.comp_def] using this

theorem wsq_ne_zero_of_mem (hzero : (0 : Wave) ∉ modes) {k : Wave} (hk : k ∈ modes) :
    wsq k ≠ 0 := by
  intro h
  apply hzero
  have hk0 : k = 0 := by
    funext i
    have hsum : ∑ j, ((k j : ℝ)) ^ 2 = 0 := h
    have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ ((k j : ℝ)) ^ 2 :=
      fun j _ => sq_nonneg _
    have := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum i (Finset.mem_univ i)
    have : ((k i : ℝ)) = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      exact this
    exact_mod_cast this
  rwa [hk0] at hk

/-! ## Transversality is preserved -/

/-- The projected forcing is Leray-transverse at every retained mode. -/
theorem herm_wC_modalForcing (hzero : (0 : Wave) ∉ modes) (u : Wave → Fin 3 → ℂ)
    {k : Wave} (hk : k ∈ modes) :
    herm (wC k) (modalForcing modes u k) = 0 := by
  have hne : wsq k ≠ 0 := wsq_ne_zero_of_mem hzero hk
  have h : herm (wC k) (leray k (advection modes u k)) = 0 := herm_wC_leray k _ hne
  have hneg : herm (wC k) (modalForcing modes u k)
      = -herm (wC k) (leray k (advection modes u k)) := by
    simp [modalForcing, herm, mul_neg, Finset.sum_neg_distrib]
  rw [hneg, h, neg_zero]

/-- A vanishing state coordinate outside the retained modes makes the
transversality scalar trivially zero. -/
theorem herm_wC_spread_of_not_mem (v : State modes) {k : Wave} (hk : k ∉ modes) :
    herm (wC k) (spread modes v k) = 0 := by
  rw [spread_of_not_mem v hk]
  simp [herm]

/-- **Transversality propagates.**  Along any solution of the cut-off Galerkin
equation, the incompressibility constraint holds at all times as soon as it
holds at the initial time. -/
theorem transverse_of_solution {nu R a b : ℝ} {α : ℝ → State modes}
    (hzero : (0 : Wave) ∉ modes)
    (hsol : ∀ t ∈ Ioo a b, HasDerivAt α (tvfield modes nu R (α t)) t)
    (h0mem : (0 : ℝ) ∈ Ioo a b)
    (hinit : ∀ k : Wave, herm (wC k) (spread modes (α 0) k) = 0) :
    ∀ t ∈ Ioo a b, ∀ k : Wave, herm (wC k) (spread modes (α t) k) = 0 := by
  intro t ht k
  by_cases hk : k ∈ modes
  · -- the transversality scalar solves a linear damped equation
    set c : ℝ → ℂ := fun s => herm (wC k) (spread modes (α s) k) with hc
    set coef : ℝ → ℂ := fun s => -((cut modes R (α s) * (nu * wsq k) : ℝ) : ℂ) with hcoef
    have hderiv : ∀ s ∈ Ioo a b, HasDerivAt c (coef s * c s) s := by
      intro s hs
      have hco : ∀ i : Fin 3, HasDerivAt (fun r => spread modes (α r) k i)
          (tvfield modes nu R (α s) ⟨k, hk⟩ i) s := by
        intro i
        have h := hasDerivAt_coord (hsol s hs) ⟨k, hk⟩ i
        simpa [spread_of_mem _ hk] using h
      have hsum : HasDerivAt c
          (∑ i, (starRingEnd ℂ) (wC k i) * tvfield modes nu R (α s) ⟨k, hk⟩ i) s := by
        have := HasDerivAt.sum (u := (Finset.univ : Finset (Fin 3)))
          (A := fun i r => (starRingEnd ℂ) (wC k i) * spread modes (α r) k i)
          (fun i _ => (hco i).const_mul ((starRingEnd ℂ) (wC k i)))
        simpa [hc, herm, Finset.sum_apply] using this
      have hval : (∑ i, (starRingEnd ℂ) (wC k i) * tvfield modes nu R (α s) ⟨k, hk⟩ i)
          = coef s * c s := by
        have hentry : ∀ i : Fin 3, tvfield modes nu R (α s) ⟨k, hk⟩ i
            = ((cut modes R (α s) : ℝ) : ℂ) *
              (-((nu * wsq k : ℝ) : ℂ) * spread modes (α s) k i
                + modalForcing modes (spread modes (α s)) k i) := by
          intro i
          simp [tvfield, vfield_apply, Complex.real_smul, Pi.smul_apply]
          ring
        calc (∑ i, (starRingEnd ℂ) (wC k i) * tvfield modes nu R (α s) ⟨k, hk⟩ i)
            = ∑ i, ((((cut modes R (α s) : ℝ) : ℂ) * -((nu * wsq k : ℝ) : ℂ)) *
                  ((starRingEnd ℂ) (wC k i) * spread modes (α s) k i)
                + ((cut modes R (α s) : ℝ) : ℂ) *
                  ((starRingEnd ℂ) (wC k i) * modalForcing modes (spread modes (α s)) k i)) :=
              Finset.sum_congr rfl fun i _ => by rw [hentry i]; ring
          _ = ((cut modes R (α s) : ℝ) : ℂ) *
                (-((nu * wsq k : ℝ) : ℂ) * herm (wC k) (spread modes (α s) k)
                  + herm (wC k) (modalForcing modes (spread modes (α s)) k)) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
              simp only [herm]
              ring
          _ = coef s * c s := by
              rw [herm_wC_modalForcing hzero _ hk, add_zero, hcoef, hc]
              push_cast
              ring
      rw [← hval]
      exact hsum
    -- the zero function solves the same linear equation, with the same value at `0`
    have hzero_sol : ∀ s ∈ Ioo a b, HasDerivAt (fun _ : ℝ => (0 : ℂ)) (coef s * 0) s := by
      intro s _
      simpa using (hasDerivAt_const s (0 : ℂ))
    have hK : ∀ s ∈ Ioo a b,
        LipschitzOnWith (Real.nnabs (nu * wsq k)) (fun z : ℂ => coef s * z) univ := by
      intro s _
      refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
      have hcs : ‖coef s‖ ≤ |nu * wsq k| := by
        have h1 : ‖coef s‖ = |cut modes R (α s)| * |nu * wsq k| := by
          simp [hcoef, abs_mul]
        have h2 : |cut modes R (α s)| ≤ 1 := by
          rw [abs_of_nonneg (cut_nonneg R (α s))]
          exact cut_le_one R (α s)
        rw [h1]
        nlinarith [abs_nonneg (nu * wsq k), abs_nonneg (cut modes R (α s))]
      have : dist (coef s * x) (coef s * y) = ‖coef s‖ * dist x y := by
        simp [dist_eq_norm, ← mul_sub]
      rw [this]
      have : (Real.nnabs (nu * wsq k) : ℝ) = |nu * wsq k| := rfl
      rw [this]
      exact mul_le_mul_of_nonneg_right hcs dist_nonneg
    have heq : EqOn c (fun _ => (0 : ℂ)) (Ioo a b) := by
      refine ODE_solution_unique_of_mem_Ioo (K := Real.nnabs (nu * wsq k))
        (v := fun s z => coef s * z) (s := fun _ => univ) hK h0mem
        (fun s hs => ⟨hderiv s hs, mem_univ _⟩)
        (fun s hs => ⟨hzero_sol s hs, mem_univ _⟩) ?_
      simpa [hc] using hinit k
    exact heq ht
  · exact herm_wC_spread_of_not_mem (α t) hk

/-! ## Reality is preserved -/

/-- `|−k|² = |k|²`. -/
theorem wsq_neg (k : Wave) : wsq (-k) = wsq k := by
  simp [wsq]

/-- The reflection of a state: `(𝓡v)_k = conj v_{−k}`.  It is the linear
involution whose fixed points are exactly the states satisfying the reality
condition of a real velocity field. -/
def reflSt (hsym : ∀ k ∈ modes, -k ∈ modes) (v : State modes) : State modes :=
  fun k i => (starRingEnd ℂ) (v ⟨-(k : Wave), hsym (k : Wave) k.2⟩ i)

theorem spread_reflSt (hsym : ∀ k ∈ modes, -k ∈ modes) (v : State modes) (k : Wave) (i : Fin 3) :
    spread modes (reflSt hsym v) k i = (starRingEnd ℂ) (spread modes v (-k) i) := by
  by_cases hk : k ∈ modes
  · have hneg : -k ∈ modes := hsym k hk
    rw [spread_of_mem _ hk, spread_of_mem _ hneg]
    rfl
  · have hneg : -k ∉ modes := by
      intro h
      exact hk (by simpa using hsym (-k) h)
    rw [spread_of_not_mem _ hk, spread_of_not_mem _ hneg]
    simp

/-- The advective term is equivariant for the reflection. -/
theorem advection_reflect (hsym : ∀ k ∈ modes, -k ∈ modes)
    (u w : Wave → Fin 3 → ℂ) (hw : ∀ k i, w k i = (starRingEnd ℂ) (u (-k) i))
    (k : Wave) (i : Fin 3) :
    advection modes w k i = (starRingEnd ℂ) (advection modes u (-k) i) := by
  have hreindex : (starRingEnd ℂ) (advection modes u (-k) i)
      = ∑ p ∈ modes, (starRingEnd ℂ)
          ((Complex.I * (∑ j, u (-p) j * (((-k - -p) j : ℤ) : ℂ))) * u (-k - -p) i) := by
    rw [advection, map_sum]
    refine Finset.sum_nbij' (fun p => -p) (fun p => -p) ?_ ?_ ?_ ?_ ?_
    · exact fun p hp => hsym p hp
    · exact fun p hp => hsym p hp
    · exact fun p _ => by simp
    · exact fun p _ => by simp
    · exact fun p _ => by simp
  rw [advection, hreindex]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h1 : ∀ j, w p j = (starRingEnd ℂ) (u (-p) j) := fun j => hw p j
  have h2 : w (k - p) i = (starRingEnd ℂ) (u (-(k - p)) i) := hw (k - p) i
  have h3 : -k - -p = -(k - p) := by abel
  rw [h2, map_mul, map_mul, h3]
  have h4 : (∑ j, w p j * (((k - p) j : ℤ) : ℂ))
      = -(starRingEnd ℂ) (∑ j, u (-p) j * (((-(k - p)) j : ℤ) : ℂ)) := by
    rw [map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hcast : (((-(k - p)) j : ℤ) : ℂ) = -(((k - p) j : ℤ) : ℂ) := by
      simp [Pi.neg_apply]
    rw [h1 j, map_mul, hcast, map_neg, map_intCast]
    ring
  rw [h4, Complex.conj_I]
  ring

/-- The Leray projection is equivariant for the reflection. -/
theorem leray_reflect (k : Wave) (x : Fin 3 → ℂ) (i : Fin 3) :
    leray k (fun j => (starRingEnd ℂ) (x j)) i = (starRingEnd ℂ) (leray (-k) x i) := by
  have hconj : herm (wC k) (fun j => (starRingEnd ℂ) (x j))
      = -(starRingEnd ℂ) (herm (wC (-k)) x) := by
    rw [herm, herm, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [wC, map_mul]
  have hwsq : ((wsq (-k) : ℝ) : ℂ) = ((wsq k : ℝ) : ℂ) := by rw [wsq_neg]
  simp only [leray, hconj, hwsq, map_sub, map_mul, map_div₀, Pi.neg_apply]
  simp only [Complex.conj_ofReal, map_intCast]
  push_cast
  ring

/-- The projected forcing is equivariant for the reflection. -/
theorem modalForcing_reflect (hsym : ∀ k ∈ modes, -k ∈ modes)
    (u w : Wave → Fin 3 → ℂ) (hw : ∀ k i, w k i = (starRingEnd ℂ) (u (-k) i))
    (k : Wave) (i : Fin 3) :
    modalForcing modes w k i = (starRingEnd ℂ) (modalForcing modes u (-k) i) := by
  have hadv : advection modes w k = fun j => (starRingEnd ℂ) (advection modes u (-k) j) := by
    funext j
    exact advection_reflect hsym u w hw k j
  simp only [modalForcing, hadv]
  rw [leray_reflect k (advection modes u (-k)) i]
  simp

/-- **The literal Galerkin vector field commutes with the reflection.** -/
theorem vfield_reflSt (hsym : ∀ k ∈ modes, -k ∈ modes) (nu : ℝ) (v : State modes) :
    vfield modes nu (reflSt hsym v) = reflSt hsym (vfield modes nu v) := by
  funext k i
  have hw : ∀ (m : Wave) (j : Fin 3),
      spread modes (reflSt hsym v) m j = (starRingEnd ℂ) (spread modes v (-m) j) :=
    fun m j => spread_reflSt hsym v m j
  have hforce := modalForcing_reflect hsym (spread modes v) (spread modes (reflSt hsym v)) hw
    (k : Wave) i
  have hneg : (-(-(k : Wave))) = (k : Wave) := by abel
  show -((nu * wsq (k : Wave) : ℝ) : ℂ) * spread modes (reflSt hsym v) (k : Wave) i
      + modalForcing modes (spread modes (reflSt hsym v)) (k : Wave) i
    = (starRingEnd ℂ) (vfield modes nu v ⟨-(k : Wave), hsym (k : Wave) k.2⟩ i)
  rw [hforce, hw (k : Wave) i]
  show _ = (starRingEnd ℂ) (-((nu * wsq (-(k : Wave)) : ℝ) : ℂ) * spread modes v (-(k : Wave)) i
      + modalForcing modes (spread modes v) (-(k : Wave)) i)
  rw [map_add, map_mul, wsq_neg]
  simp

/-- The energy is invariant under the reflection. -/
theorem en_reflSt (hsym : ∀ k ∈ modes, -k ∈ modes) (v : State modes) :
    en modes (reflSt hsym v) = en modes v := by
  have hbij : ∀ k ∈ (Finset.univ : Finset ↥modes),
      (⟨-(k : Wave), hsym (k : Wave) k.2⟩ : ↥modes) ∈ Finset.univ :=
    fun _ _ => Finset.mem_univ _
  refine Finset.sum_nbij' (fun k => (⟨-(k : Wave), hsym (k : Wave) k.2⟩ : ↥modes))
    (fun k => (⟨-(k : Wave), hsym (k : Wave) k.2⟩ : ↥modes)) hbij hbij ?_ ?_ ?_
  · exact fun k _ => Subtype.ext (by simp)
  · exact fun k _ => Subtype.ext (by simp)
  · intro k _
    simp [reflSt, nsq]

/-- The cut-off field commutes with the reflection. -/
theorem tvfield_reflSt (hsym : ∀ k ∈ modes, -k ∈ modes) (nu R : ℝ) (v : State modes) :
    tvfield modes nu R (reflSt hsym v) = reflSt hsym (tvfield modes nu R v) := by
  have hcut : cut modes R (reflSt hsym v) = cut modes R v := by
    rw [cut, cut, en_reflSt hsym v]
  funext k i
  rw [tvfield, tvfield, hcut, vfield_reflSt hsym nu v]
  simp [reflSt, Complex.real_smul]

/-- The reflection as a continuous linear map. -/
def reflCLM (hsym : ∀ k ∈ modes, -k ∈ modes) : State modes →L[ℝ] State modes :=
  LinearMap.toContinuousLinearMap
    { toFun := reflSt hsym
      map_add' := by
        intro v w
        funext k i
        simp [reflSt]
      map_smul' := by
        intro c v
        funext k i
        simp [reflSt, Complex.real_smul] }

@[simp] theorem reflCLM_apply (hsym : ∀ k ∈ modes, -k ∈ modes) (v : State modes) :
    reflCLM hsym v = reflSt hsym v := rfl

/-- **The reality condition propagates.**  Along any solution of the cut-off
Galerkin equation whose initial state is real, every state is real: the
reflected trajectory solves the same equation with the same initial value. -/
theorem reality_of_solution {nu R a b : ℝ} {α : ℝ → State modes}
    (hsym : ∀ k ∈ modes, -k ∈ modes)
    (hsol : ∀ t ∈ Ioo a b, HasDerivAt α (tvfield modes nu R (α t)) t)
    (h0mem : (0 : ℝ) ∈ Ioo a b)
    (hinit : reflSt hsym (α 0) = α 0) :
    ∀ t ∈ Ioo a b, reflSt hsym (α t) = α t := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_tvfield modes nu R
  have hrefl : ∀ t ∈ Ioo a b,
      HasDerivAt (fun s => reflSt hsym (α s)) (tvfield modes nu R (reflSt hsym (α t))) t := by
    intro t ht
    have h := (reflCLM hsym).hasFDerivAt.comp_hasDerivAt t (hsol t ht)
    rw [tvfield_reflSt hsym nu R (α t)]
    simpa [Function.comp_def] using h
  have heq : EqOn (fun s => reflSt hsym (α s)) α (Ioo a b) := by
    refine ODE_solution_unique_of_mem_Ioo (K := K) (v := fun _ v => tvfield modes nu R v)
      (s := fun _ => univ) (fun s _ => hK.lipschitzOnWith) h0mem
      (fun s hs => ⟨hrefl s hs, mem_univ _⟩) (fun s hs => ⟨hsol s hs, mem_univ _⟩) hinit
  exact fun t ht => heq ht

/-- The reality condition in the form used by `GalerkinFlow`. -/
theorem reality_spread {v : State modes} (hsym : ∀ k ∈ modes, -k ∈ modes)
    (h : reflSt hsym v = v) (k : Wave) (i : Fin 3) :
    spread modes v (-k) i = (starRingEnd ℂ) (spread modes v k i) := by
  have := spread_reflSt hsym v (-k) i
  rw [h] at this
  simpa using this

end ClayNS.GalerkinODE
