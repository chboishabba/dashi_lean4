import ClaySpec
import NavierStokes.ComparatorDefinitions

/-!
# Independent semantic bridge: Comparator statement to Clay statement

The only non-Mathlib inputs are the frozen independent `ClaySpec` and OpenAI's
statement-only `ComparatorDefinitions`.  This file does not import
`ComparatorBridge`, `ComparatorSolution`, candidate assembly, uniqueness,
blow-up, or any proof-construction module.
-/

noncomputable section

open MeasureTheory Set InnerProductSpace
open scoped ContDiff Laplacian

namespace SemanticGap

open ClaySpec

theorem nonnegativeTime_eq :
    nonnegativeTime = (Set.univ : Set R3) ×ˢ Set.Ici (0 : ℝ) := by
  ext z
  simp [nonnegativeTime]

theorem uniqueDiffOn_nonnegativeTime : UniqueDiffOn ℝ nonnegativeTime := by
  rw [nonnegativeTime_eq]
  exact uniqueDiffOn_univ.prod (uniqueDiffOn_Ici 0)

theorem iteratedDirectionalWithin_eq_iteratedFDerivWithin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : SpaceTime → E} (hg : ContDiffOn ℝ ∞ g nonnegativeTime)
    (dirs : List SpaceTime) (z : SpaceTime) (hz : z ∈ nonnegativeTime) :
    iteratedDirectionalWithin dirs g z =
      iteratedFDerivWithin ℝ dirs.length g nonnegativeTime z dirs.get := by
  induction dirs generalizing z with
  | nil => simp [iteratedDirectionalWithin]
  | cons v vs ih =>
      rw [iteratedDirectionalWithin]
      change fderivWithin ℝ (iteratedDirectionalWithin vs g) nonnegativeTime z v = _
      have hEqOn : Set.EqOn (iteratedDirectionalWithin vs g)
          (fun y => iteratedFDerivWithin ℝ vs.length g nonnegativeTime y vs.get)
          nonnegativeTime := by
        intro y hy
        exact ih y hy
      rw [fderivWithin_congr' hEqOn hz]
      have hc : DifferentiableWithinAt ℝ
          (iteratedFDerivWithin ℝ vs.length g nonnegativeTime)
          nonnegativeTime z :=
        hg.differentiableOn_iteratedFDerivWithin
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl vs.length)
          uniqueDiffOn_nonnegativeTime z hz
      rw [fderivWithin_continuousMultilinear_apply_const_apply
        (uniqueDiffOn_nonnegativeTime z hz) hc vs.get v]
      change ((fderivWithin ℝ (iteratedFDerivWithin ℝ vs.length g nonnegativeTime)
        nonnegativeTime z) v) vs.get =
          iteratedFDerivWithin ℝ (vs.length + 1) g nonnegativeTime z (v :: vs).get
      rw [iteratedFDerivWithin_succ_apply_left]
      congr 1

theorem iteratedSpatialDirectional_eq_iteratedFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : R3 → E} (hg : ContDiff ℝ ∞ g)
    (dirs : List R3) (x : R3) :
    iteratedSpatialDirectional dirs g x =
      iteratedFDeriv ℝ dirs.length g x dirs.get := by
  induction dirs generalizing x with
  | nil => simp [iteratedSpatialDirectional]
  | cons v vs ih =>
      rw [iteratedSpatialDirectional]
      change fderiv ℝ (iteratedSpatialDirectional vs g) x v = _
      rw [show iteratedSpatialDirectional vs g =
          (fun y => iteratedFDeriv ℝ vs.length g y vs.get) by
        funext y
        exact ih y]
      have hc : DifferentiableAt ℝ (iteratedFDeriv ℝ vs.length g) x :=
        (ContDiff.differentiable_iteratedFDeriv
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl vs.length) hg) x
      rw [fderiv_continuousMultilinear_apply_const_apply hc vs.get v]
      change ((fderiv ℝ (iteratedFDeriv ℝ vs.length g) x) v) vs.get =
        iteratedFDeriv ℝ (vs.length + 1) g x (v :: vs).get
      rw [iteratedFDeriv_succ_apply_left]
      congr 1

theorem norm_spatialBasis (i : Fin 3) : ‖spatialBasis i‖ = 1 := by
  simp [spatialBasis]

theorem norm_spatialDirection (i : Fin 3) : ‖spatialDirection i‖ = 1 := by
  simp [spatialDirection, norm_spatialBasis]

theorem norm_timeDirection : ‖timeDirection‖ = 1 := by
  simp [timeDirection]

theorem spatialWord_get_norm (α : TrustBoundarySpatialMultiIndex)
    (k : Fin (spatialWord α).length) : ‖(spatialWord α).get k‖ = 1 := by
  have hm := List.get_mem (l := spatialWord α) k
  rcases List.mem_map.1 hm with ⟨i, hi, heq⟩
  rw [← heq]
  exact norm_spatialDirection i

theorem initialSpatialWord_get_norm (α : TrustBoundarySpatialMultiIndex)
    (k : Fin (initialSpatialWord α).length) : ‖(initialSpatialWord α).get k‖ = 1 := by
  have hm := List.get_mem (l := initialSpatialWord α) k
  rcases List.mem_map.1 hm with ⟨i, hi, heq⟩
  rw [← heq]
  exact norm_spatialBasis i

theorem mixedWord_get_norm (α : TrustBoundarySpatialMultiIndex) (m : ℕ)
    (k : Fin (mixedWord α m).length) : ‖(mixedWord α m).get k‖ = 1 := by
  have hm := List.get_mem (l := mixedWord α m) k
  rcases List.mem_append.1 hm with hm | hm
  · rcases List.mem_map.1 hm with ⟨i, hi, heq⟩
    rw [← heq]
    exact norm_spatialDirection i
  · rw [List.mem_replicate] at hm
    exact hm.2 ▸ norm_timeDirection

theorem list_map_norm_prod_eq_one {E : Type*} [Norm E]
    (dirs : List E) (hdirs : ∀ v ∈ dirs, ‖v‖ = 1) :
    (dirs.map norm).prod = 1 := by
  induction dirs with
  | nil => simp
  | cons v vs ih =>
      rw [List.map_cons, List.prod_cons, hdirs v (List.mem_cons_self)]
      simp only [one_mul]
      exact ih (fun w hw => hdirs w (List.mem_cons_of_mem v hw))

theorem norm_iteratedDirectionalWithin_le_jet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : SpaceTime → E} (hg : ContDiffOn ℝ ∞ g nonnegativeTime)
    (dirs : List SpaceTime) (hdirs : ∀ v ∈ dirs, ‖v‖ = 1)
    (z : SpaceTime) (hz : z ∈ nonnegativeTime) :
    ‖iteratedDirectionalWithin dirs g z‖ ≤
      ‖iteratedFDerivWithin ℝ dirs.length g nonnegativeTime z‖ := by
  rw [iteratedDirectionalWithin_eq_iteratedFDerivWithin hg dirs z hz]
  calc
    ‖iteratedFDerivWithin ℝ dirs.length g nonnegativeTime z dirs.get‖ ≤
        ‖iteratedFDerivWithin ℝ dirs.length g nonnegativeTime z‖ *
          ∏ k : Fin dirs.length, ‖dirs.get k‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDerivWithin ℝ dirs.length g nonnegativeTime z‖ := by
      simp [list_map_norm_prod_eq_one dirs hdirs]

theorem norm_iteratedSpatialDirectional_le_jet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : R3 → E} (hg : ContDiff ℝ ∞ g)
    (dirs : List R3) (hdirs : ∀ v ∈ dirs, ‖v‖ = 1)
    (x : R3) :
    ‖iteratedSpatialDirectional dirs g x‖ ≤ ‖iteratedFDeriv ℝ dirs.length g x‖ := by
  rw [iteratedSpatialDirectional_eq_iteratedFDeriv hg dirs x]
  calc
    ‖iteratedFDeriv ℝ dirs.length g x dirs.get‖ ≤
        ‖iteratedFDeriv ℝ dirs.length g x‖ * ∏ k : Fin dirs.length, ‖dirs.get k‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ dirs.length g x‖ := by
      simp [list_map_norm_prod_eq_one dirs hdirs]

theorem initialSpatialWord_mem_norm (α : TrustBoundarySpatialMultiIndex)
    {v : R3} (hv : v ∈ initialSpatialWord α) : ‖v‖ = 1 := by
  rcases List.mem_map.1 hv with ⟨i, hi, heq⟩
  rw [← heq]
  exact norm_spatialBasis i

theorem mixedWord_mem_norm (α : TrustBoundarySpatialMultiIndex) (m : ℕ)
    {v : SpaceTime} (hv : v ∈ mixedWord α m) : ‖v‖ = 1 := by
  rcases List.mem_append.1 hv with hv | hv
  · rcases List.mem_map.1 hv with ⟨i, hi, heq⟩
    rw [← heq]
    exact norm_spatialDirection i
  · rw [List.mem_replicate] at hv
    exact hv.2 ▸ norm_timeDirection

theorem fderiv_component_basic {g : R3 → R3} (hg : DifferentiableAt ℝ g x)
    (i : Fin 3) (v : R3) :
    fderiv ℝ (fun y => g y i) x v = (fderiv ℝ g x v) i := by
  let πi : R3 →L[ℝ] ℝ := EuclideanSpace.proj i
  have hc := fderiv_comp x πi.differentiableAt hg
  have hc' := congrArg (fun L => L v) hc
  have hp : fderiv ℝ (πi : R3 → ℝ) (g x) = πi := πi.fderiv
  rw [hp] at hc'
  simpa [πi, Function.comp_def] using hc'

theorem initialDivergence_eq (u₀ : InitialVelocity) (hu₀ : ContDiff ℝ ∞ u₀)
    (x : R3) :
    initialDivergence u₀ x = NavierStokes.Comparator.divergence u₀ x := by
  rw [NavierStokes.Comparator.divergence,
    LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only [initialDivergence]
  apply Finset.sum_congr rfl
  intro i hi
  rw [fderiv_component_basic (hu₀.differentiable (by simp) x) i (spatialBasis i)]
  simp [spatialBasis, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left]

theorem initialRapidDecay_of_comparator {u₀ : InitialVelocity}
    (h : NavierStokes.Comparator.InitialVelocityConditionDecay u₀) :
    InitialRapidDecay u₀ := by
  intro α K
  obtain ⟨C, hC⟩ := h.decay (initialSpatialWord α).length (K : ℝ)
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro x
  calc
    ‖iteratedSpatialDirectional (initialSpatialWord α) u₀ x‖ ≤
        ‖iteratedFDeriv ℝ (initialSpatialWord α).length u₀ x‖ :=
      norm_iteratedSpatialDirectional_le_jet h.smooth (initialSpatialWord α)
        (fun v hv => initialSpatialWord_mem_norm α hv) x
    _ ≤ C / (1 + ‖x‖) ^ K := by
      simpa only [Real.rpow_natCast] using hC x
    _ ≤ max C 0 / (1 + ‖x‖) ^ K := by
      exact div_le_div_of_nonneg_right (le_max_left C 0) (by positivity)

def uncurryField {E : Type*} (g : R3 → ℝ → E) : SpaceTime → E :=
  fun z => g z.1 z.2

@[simp] theorem uncurryField_apply {E : Type*} (g : R3 → ℝ → E) (z : SpaceTime) :
    uncurryField g z = g z.1 z.2 := rfl

theorem uncurryField_eq_hasUncurry {E : Type*} (g : R3 → ℝ → E) :
    uncurryField g = ↿g := by
  rfl

theorem forceRapidDecayR3_of_comparator {f : R3 → ℝ → R3}
    (h : NavierStokes.Comparator.ForceConditionDecay f) :
    ForceRapidDecayR3 (uncurryField f) := by
  have hfs : ContDiffOn ℝ ∞ (uncurryField f) nonnegativeTime := by
    rw [uncurryField_eq_hasUncurry]
    rw [nonnegativeTime_eq]
    exact h.smooth
  intro α m K
  obtain ⟨C, hC⟩ := h.decay (mixedWord α m).length (K : ℝ)
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro z hz
  have hzt : 0 ≤ z.2 := hz
  calc
    ‖iteratedDirectionalWithin (mixedWord α m) (uncurryField f) z‖ ≤
        ‖iteratedFDerivWithin ℝ (mixedWord α m).length (uncurryField f)
          nonnegativeTime z‖ :=
      norm_iteratedDirectionalWithin_le_jet
        hfs
        (mixedWord α m) (fun v hv => mixedWord_mem_norm α m hv) z hz
    _ ≤ C / (1 + ‖z.1‖ + z.2) ^ K := by
      rw [uncurryField_eq_hasUncurry, nonnegativeTime_eq]
      simpa only [Real.rpow_natCast] using hC z.1 z.2 hz
    _ ≤ max C 0 / (1 + ‖z.1‖ + z.2) ^ K := by
      exact div_le_div_of_nonneg_right (le_max_left C 0) (by positivity)

theorem forceRapidDecayPeriodic_of_comparator {f : R3 → ℝ → R3}
    (h : NavierStokes.Comparator.ForceConditionPeriodic f) :
    ForceRapidDecayPeriodic (uncurryField f) := by
  have hfs : ContDiffOn ℝ ∞ (uncurryField f) nonnegativeTime := by
    rw [uncurryField_eq_hasUncurry]
    rw [nonnegativeTime_eq]
    exact h.smooth
  intro α m K
  obtain ⟨C, hC⟩ := h.decay (mixedWord α m).length (K : ℝ)
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro z hz
  calc
    ‖iteratedDirectionalWithin (mixedWord α m) (uncurryField f) z‖ ≤
        ‖iteratedFDerivWithin ℝ (mixedWord α m).length (uncurryField f)
          nonnegativeTime z‖ :=
      norm_iteratedDirectionalWithin_le_jet
        hfs
        (mixedWord α m) (fun v hv => mixedWord_mem_norm α m hv) z hz
    _ ≤ C / (1 + |z.2|) ^ K := by
      have ht : |z.2| = z.2 := abs_of_nonneg hz
      rw [ht]
      rw [uncurryField_eq_hasUncurry, nonnegativeTime_eq]
      simpa only [Real.rpow_natCast] using hC z.1 z.2 hz
    _ ≤ max C 0 / (1 + |z.2|) ^ K := by
      exact div_le_div_of_nonneg_right (le_max_left C 0) (by positivity)

theorem admissibleDataR3_of_comparator {u₀ : InitialVelocity} {f : R3 → ℝ → R3}
    (hu₀ : NavierStokes.Comparator.InitialVelocityConditionDecay u₀)
    (hf : NavierStokes.Comparator.ForceConditionDecay f) :
    AdmissibleDataR3 u₀ (uncurryField f) := by
  refine ⟨hu₀.smooth, ?_, initialRapidDecay_of_comparator hu₀, ?_,
    forceRapidDecayR3_of_comparator hf⟩
  · intro x
    rw [initialDivergence_eq u₀ hu₀.smooth x]
    exact hu₀.div_free x
  · unfold TrustBoundarySmoothOn
    rw [uncurryField_eq_hasUncurry]
    rw [nonnegativeTime_eq]
    exact hf.smooth

theorem admissibleDataPeriodic_of_comparator {u₀ : InitialVelocity} {f : R3 → ℝ → R3}
    (hu₀ : NavierStokes.Comparator.InitialVelocityConditionPeriodic u₀)
    (hf : NavierStokes.Comparator.ForceConditionPeriodic f) :
    AdmissibleDataPeriodic u₀ (uncurryField f) := by
  refine ⟨hu₀.smooth, ?_, ?_, ?_, ?_, forceRapidDecayPeriodic_of_comparator hf⟩
  · intro x
    rw [initialDivergence_eq u₀ hu₀.smooth x]
    exact hu₀.div_free x
  · intro x j
    exact hu₀.isOnePeriodic x j
  · unfold TrustBoundarySmoothOn
    rw [uncurryField_eq_hasUncurry]
    rw [nonnegativeTime_eq]
    exact hf.smooth
  · intro z hz j
    exact hf.isOnePeriodic z.2 hz z.1 j

theorem partialSpace_eq_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : SpaceTime → E} (hg : ContDiffOn ℝ ∞ g nonnegativeTime)
    (x : R3) {t : ℝ} (ht : 0 ≤ t) (i : Fin 3) :
    partialSpace i g (x, t) = fderiv ℝ (fun y => g (y, t)) x (spatialBasis i) := by
  let e : R3 → SpaceTime := fun y => (y, t)
  have he : DifferentiableAt ℝ e x := differentiableAt_id.prodMk (differentiableAt_const t)
  have he_maps : MapsTo e (Set.univ : Set R3) nonnegativeTime := by
    intro y hy
    exact ht
  have hg' : DifferentiableWithinAt ℝ g nonnegativeTime (e x) :=
    hg.differentiableOn (by simp) (e x) (he_maps (Set.mem_univ x))
  have hcomp := fderivWithin_comp x hg' he.differentiableWithinAt he_maps
    (uniqueDiffOn_univ x (Set.mem_univ x))
  have happ := congrArg (fun L => L (spatialBasis i)) hcomp
  have heval : fderiv ℝ e x (spatialBasis i) = (spatialBasis i, 0) := by
    have hp := DifferentiableAt.fderiv_prodMk (x := x)
      (𝕜 := ℝ) differentiableAt_id (differentiableAt_const t)
    have hp' := congrArg (fun L => L (spatialBasis i)) hp
    simpa [e] using hp'
  simpa [partialSpace, e, spatialDirection, Function.comp_def,
    fderivWithin_univ, heval] using happ.symm

theorem partialTime_eq_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : SpaceTime → E} (hg : ContDiffOn ℝ ∞ g nonnegativeTime)
    (x : R3) {t : ℝ} (ht : 0 ≤ t) :
    partialTime g (x, t) = derivWithin (fun s => g (x, s)) (Set.Ici 0) t := by
  let e : ℝ → SpaceTime := fun s => (x, s)
  have he : DifferentiableAt ℝ e t := (differentiableAt_const x).prodMk differentiableAt_id
  have he_maps : MapsTo e (Set.Ici (0 : ℝ)) nonnegativeTime := by
    intro s hs
    exact hs
  have hg' : DifferentiableWithinAt ℝ g nonnegativeTime (e t) :=
    hg.differentiableOn (by simp) (e t) (he_maps ht)
  have hcomp := fderivWithin_comp t hg' he.differentiableWithinAt he_maps
    (uniqueDiffOn_Ici 0 t ht)
  have happ := congrArg (fun L => L (1 : ℝ)) hcomp
  have heval : fderivWithin ℝ e (Set.Ici 0) t (1 : ℝ) = (0, 1) := by
    rw [he.fderivWithin (uniqueDiffOn_Ici 0 t ht)]
    have hp := DifferentiableAt.fderiv_prodMk (x := t)
      (𝕜 := ℝ) (differentiableAt_const x) differentiableAt_id
    have hp' := congrArg (fun L => L (1 : ℝ)) hp
    simpa [e] using hp'
  simpa [partialTime, e, timeDirection, Function.comp_def,
    fderivWithin_derivWithin, heval] using happ.symm

theorem component_smooth {g : SpaceTime → R3}
    (hg : ContDiffOn ℝ ∞ g nonnegativeTime) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun z => g z i) nonnegativeTime := by
  simpa [Function.comp_def] using
    hg.continuousLinearMap_comp (EuclideanSpace.proj i)

theorem partialSpace_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : SpaceTime → E} (hg : ContDiffOn ℝ ∞ g nonnegativeTime) (i : Fin 3) :
    ContDiffOn ℝ ∞ (partialSpace i g) nonnegativeTime := by
  unfold partialSpace
  exact (hg.fderivWithin uniqueDiffOn_nonnegativeTime (by simp)).clm_apply contDiffOn_const

theorem smooth_space_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : SpaceTime → E} (hg : ContDiffOn ℝ ∞ g nonnegativeTime)
    {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ ∞ (fun x => g (x, t)) := by
  rw [← contDiffOn_univ]
  exact hg.comp (contDiff_id.prodMk contDiff_const).contDiffOn
    (fun _ _ => ht)

theorem secondPartial_eq_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : SpaceTime → E} (hg : ContDiffOn ℝ ∞ g nonnegativeTime)
    (x : R3) {t : ℝ} (ht : 0 ≤ t) (j : Fin 3) :
    partialSpace j (partialSpace j g) (x, t) =
      fderiv ℝ (fun y => fderiv ℝ (fun q => g (q, t)) y (spatialBasis j)) x
        (spatialBasis j) := by
  rw [partialSpace_eq_slice (partialSpace_smooth hg j) x ht j]
  rw [show (fun y => partialSpace j g (y, t)) =
      (fun y => fderiv ℝ (fun q => g (q, t)) y (spatialBasis j)) by
    funext y
    exact partialSpace_eq_slice hg y ht j]

theorem secondPartial_eq_iterated {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : SpaceTime → E} (hg : ContDiffOn ℝ ∞ g nonnegativeTime)
    (x : R3) {t : ℝ} (ht : 0 ≤ t) (j : Fin 3) :
    partialSpace j (partialSpace j g) (x, t) =
      iteratedFDeriv ℝ 2 (fun q => g (q, t)) x ![spatialBasis j, spatialBasis j] := by
  rw [secondPartial_eq_slice hg x ht j, iteratedFDeriv_two_apply]
  have hs := smooth_space_slice hg ht
  have hd : DifferentiableAt ℝ (fderiv ℝ (fun q => g (q, t))) x :=
    (hs.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  rw [fderiv_clm_apply hd (differentiableAt_const (spatialBasis j))]
  simp

theorem spatialLaplacianComponent_eq (u : Velocity)
    (hu : ContDiffOn ℝ ∞ u nonnegativeTime) (x : R3) {t : ℝ} (ht : 0 ≤ t)
    (i : Fin 3) :
    spatialLaplacianComponent u i (x, t) = (Δ (fun y => u (y, t)) x) i := by
  let ui : SpaceTime → ℝ := fun z => u z i
  have hui : ContDiffOn ℝ ∞ ui nonnegativeTime := component_smooth hu i
  calc
    spatialLaplacianComponent u i (x, t) =
        ∑ j : Fin 3, iteratedFDeriv ℝ 2 (fun q => ui (q, t)) x
          ![spatialBasis j, spatialBasis j] := by
            simp only [spatialLaplacianComponent]
            apply Finset.sum_congr rfl
            intro j hj
            exact secondPartial_eq_iterated hui x ht j
    _ = Δ (fun q => ui (q, t)) x := by
          rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
            (fun q => ui (q, t)) (EuclideanSpace.basisFun (Fin 3) ℝ)]
          simp [spatialBasis, EuclideanSpace.basisFun_apply]
    _ = (Δ (fun y => u (y, t)) x) i := by
          have hs := smooth_space_slice hu ht
          have hc : ContDiffAt ℝ 2 (fun y => u (y, t)) x :=
            (hs.of_le (by norm_num)).contDiffAt
          have h := hc.laplacian_CLM_comp_left (l := EuclideanSpace.proj i)
          simpa [ui, Function.comp_def] using h

theorem pressureGradientComponent_eq (p : Pressure)
    (hp : ContDiffOn ℝ ∞ p nonnegativeTime) (x : R3) {t : ℝ} (ht : 0 ≤ t)
    (i : Fin 3) :
    partialSpace i p (x, t) = (gradient (fun y => p (y, t)) x) i := by
  rw [partialSpace_eq_slice hp x ht i]
  calc
    fderiv ℝ (fun y => p (y, t)) x (spatialBasis i) =
        ⟪spatialBasis i, gradient (fun y => p (y, t)) x⟫_ℝ := by
          have h := inner_gradient_right (𝕜 := ℝ) (f := fun y => p (y, t))
            (x := spatialBasis i) (y := x)
          simpa only [starRingEnd_apply, star_trivial] using h.symm
    _ = (gradient (fun y => p (y, t)) x) i := by
          simpa [spatialBasis] using
            (EuclideanSpace.inner_single_left i (1 : ℝ)
              (gradient (fun y => p (y, t)) x))

theorem fderiv_component {g : R3 → R3} (hg : DifferentiableAt ℝ g x)
    (i : Fin 3) (v : R3) :
    fderiv ℝ (fun y => g y i) x v = (fderiv ℝ g x v) i := by
  let πi : R3 →L[ℝ] ℝ := EuclideanSpace.proj i
  have hc := fderiv_comp x πi.differentiableAt hg
  have hc' := congrArg (fun L => L v) hc
  have hp : fderiv ℝ (πi : R3 → ℝ) (g x) = πi := by
    exact πi.fderiv
  rw [hp] at hc'
  simpa [πi, Function.comp_def] using hc'

theorem fderivWithin_component {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {g : E → R3} {x : E}
    (hg : DifferentiableWithinAt ℝ g s x) (hs : UniqueDiffWithinAt ℝ s x)
    (i : Fin 3) (v : E) :
    fderivWithin ℝ (fun y => g y i) s x v = (fderivWithin ℝ g s x v) i := by
  let πi : R3 →L[ℝ] ℝ := EuclideanSpace.proj i
  have hc := fderivWithin_comp x πi.differentiableWithinAt hg
    (mapsTo_univ g s) hs
  have hc' := congrArg (fun L => L v) hc
  have hp : fderivWithin ℝ (πi : R3 → ℝ) Set.univ (g x) = πi := by
    exact πi.fderivWithin uniqueDiffWithinAt_univ
  rw [hp] at hc'
  simpa [πi, Function.comp_def] using hc'

theorem partialTime_component (u : Velocity)
    (hu : ContDiffOn ℝ ∞ u nonnegativeTime) (z : SpaceTime)
    (hz : z ∈ nonnegativeTime) (i : Fin 3) :
    partialTime (fun w => u w i) z = (partialTime u z) i := by
  unfold partialTime
  have hd := hu.differentiableOn (by simp) z hz
  exact fderivWithin_component hd (uniqueDiffOn_nonnegativeTime z hz) i timeDirection

theorem convectionComponent_eq (u : Velocity)
    (hu : ContDiffOn ℝ ∞ u nonnegativeTime) (x : R3) {t : ℝ} (ht : 0 ≤ t)
    (i : Fin 3) :
    convectionComponent u i (x, t) =
      (fderiv ℝ (fun y => u (y, t)) x (u (x, t))) i := by
  let L := fderiv ℝ (fun y => u (y, t)) x
  have hui (j : Fin 3) : ContDiffOn ℝ ∞ (fun z => u z i) nonnegativeTime :=
    component_smooth hu i
  have hpartial (j : Fin 3) :
      partialSpace j (fun z => u z i) (x, t) = (L (spatialBasis j)) i := by
    rw [partialSpace_eq_slice (hui j) x ht j]
    have hs := smooth_space_slice hu ht
    have hd : DifferentiableAt ℝ (fun y => u (y, t)) x :=
      hs.differentiable (by simp) x
    exact fderiv_component hd i (spatialBasis j)
  have hexpand : (∑ j : Fin 3, u (x, t) j • spatialBasis j) = u (x, t) := by
    have h := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr' (u (x, t))
    simpa [spatialBasis, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_left] using h
  rw [convectionComponent]
  simp_rw [hpartial]
  calc
    (∑ j : Fin 3, u (x, t) j * (L (spatialBasis j)) i) =
        (L (∑ j : Fin 3, u (x, t) j • spatialBasis j)) i := by
          simp
    _ = (L (u (x, t))) i := by rw [hexpand]

theorem divergence_eq (u : Velocity)
    (hu : ContDiffOn ℝ ∞ u nonnegativeTime) (x : R3) {t : ℝ} (ht : 0 ≤ t) :
    divergence u (x, t) =
      NavierStokes.Comparator.divergence (fun y => u (y, t)) x := by
  rw [NavierStokes.Comparator.divergence,
    LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only [divergence]
  apply Finset.sum_congr rfl
  intro i hi
  rw [partialSpace_eq_slice (component_smooth hu i) x ht i]
  have hs := smooth_space_slice hu ht
  have hd : DifferentiableAt ℝ (fun y => u (y, t)) x :=
    hs.differentiable (by simp) x
  rw [fderiv_component hd i (spatialBasis i)]
  simp [spatialBasis, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left]

def curryField {E : Type*} (g : SpaceTime → E) : R3 → ℝ → E :=
  fun x t => g (x, t)

@[simp] theorem curryField_apply {E : Type*} (g : SpaceTime → E) (x : R3) (t : ℝ) :
    curryField g x t = g (x, t) := rfl

@[simp] theorem uncurry_curryField {E : Type*} (g : SpaceTime → E) :
    Function.uncurry (curryField g) = g := rfl

theorem curryField_uncurryField {E : Type*} (g : R3 → ℝ → E) :
    curryField (uncurryField g) = g := by
  funext x t
  rfl

theorem equationOne_to_comparator (ν : ℝ) (u : Velocity) (p : Pressure) (f : Force)
    (hu : ContDiffOn ℝ ∞ u nonnegativeTime)
    (hp : ContDiffOn ℝ ∞ p nonnegativeTime)
    (hEq : EquationOne ν u p f) :
    ∀ x : R3, ∀ t : ℝ, 0 ≤ t →
      derivWithin (fun s => u (x, s)) (Set.Ici 0) t +
          fderiv ℝ (fun y => u (y, t)) x (u (x, t)) =
        ν • Δ (fun y => u (y, t)) x - gradient (fun y => p (y, t)) x + f (x, t) := by
  intro x t ht
  ext i
  have heq := hEq (x, t) ht i
  rw [partialTime_component u hu (x, t) ht i,
    partialTime_eq_slice hu x ht,
    convectionComponent_eq u hu x ht i,
    spatialLaplacianComponent_eq u hu x ht i,
    pressureGradientComponent_eq p hp x ht i] at heq
  exact heq

theorem claySolutionR3_to_comparator {ν : ℝ} {u₀ : InitialVelocity} {f : Force}
    {u : Velocity} {p : Pressure} (h : ClaySolutionR3 ν u₀ f u p) :
    NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessRn ν u₀
      (curryField f) (curryField u) (curryField p) := by
  rcases h with ⟨hu, hp, heq, hdiv, hinit, henergy⟩
  refine {
    navier_stokes := equationOne_to_comparator ν u p f hu hp heq
    div_free := ?_
    initial_condition := ?_
    velocity_smooth := ?_
    pressure_smooth := ?_
    integrable := ?_
    globally_bounded_energy := ?_ }
  · intro x t ht
    change NavierStokes.Comparator.divergence (fun y => u (y, t)) x = 0
    rw [← divergence_eq u hu x ht]
    exact hdiv (x, t) ht
  · intro x
    exact hinit x
  · change ContDiffOn ℝ ∞ u (Set.univ ×ˢ Set.Ici 0)
    simpa [TrustBoundarySmoothOn, nonnegativeTime_eq] using hu
  · change ContDiffOn ℝ ∞ p (Set.univ ×ˢ Set.Ici 0)
    simpa [TrustBoundarySmoothOn, nonnegativeTime_eq] using hp
  · intro t ht
    exact (henergy.choose_spec t ht).1.norm
  · obtain ⟨C, hC⟩ := henergy
    exact ⟨C, fun t ht => (hC t ht).2⟩

theorem claySolutionPeriodic_to_comparator {ν : ℝ} {u₀ : InitialVelocity} {f : Force}
    {u : Velocity} {p : Pressure} (h : ClaySolutionPeriodic ν u₀ f u p) :
    NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessPeriodic ν u₀
      (curryField f) (curryField u) (curryField p) := by
  rcases h with ⟨hu, hp, heq, hdiv, hinit, huper, hpper⟩
  refine {
    navier_stokes := equationOne_to_comparator ν u p f hu hp heq
    div_free := ?_
    initial_condition := ?_
    velocity_smooth := ?_
    pressure_smooth := ?_
    isOnePeriodic_velocity := ?_
    isOnePeriodic_pressure := ?_ }
  · intro x t ht
    change NavierStokes.Comparator.divergence (fun y => u (y, t)) x = 0
    rw [← divergence_eq u hu x ht]
    exact hdiv (x, t) ht
  · intro x
    exact hinit x
  · change ContDiffOn ℝ ∞ u (Set.univ ×ˢ Set.Ici 0)
    simpa [TrustBoundarySmoothOn, nonnegativeTime_eq] using hu
  · change ContDiffOn ℝ ∞ p (Set.univ ×ˢ Set.Ici 0)
    simpa [TrustBoundarySmoothOn, nonnegativeTime_eq] using hp
  · intro t ht x i
    exact huper (x, t) ht i
  · intro t ht x i
    exact hpper (x, t) ht i

/-! ## The two statement-level implications -/

/-- The universally quantified closure of the Comparator alternative (C). -/
def ComparatorOptionC : Prop :=
  ∀ ν : ℝ, 0 < ν →
    ∃ (u₀ : R3 → R3) (f : R3 → ℝ → R3),
      NavierStokes.Comparator.InitialVelocityConditionDecay u₀ ∧
      NavierStokes.Comparator.ForceConditionDecay f ∧
      ¬ ∃ v p, NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessRn
        ν u₀ f v p

/-- The universally quantified closure of the Comparator alternative (D). -/
def ComparatorOptionD : Prop :=
  ∀ ν : ℝ, 0 < ν →
    ∃ (u₀ : R3 → R3) (f : R3 → ℝ → R3),
      NavierStokes.Comparator.InitialVelocityConditionPeriodic u₀ ∧
      NavierStokes.Comparator.ForceConditionPeriodic f ∧
      ¬ ∃ v p, NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessPeriodic
        ν u₀ f v p

theorem ComparatorOptionC_to_ClayOptionC : ComparatorOptionC → ClayOptionC := by
  intro h ν hν
  obtain ⟨u₀, f, hu₀, hf, hno⟩ := h ν hν
  refine ⟨u₀, uncurryField f, admissibleDataR3_of_comparator hu₀ hf, ?_⟩
  rintro ⟨u, p, hsol⟩
  apply hno
  refine ⟨curryField u, curryField p, ?_⟩
  have hc := claySolutionR3_to_comparator hsol
  rw [curryField_uncurryField] at hc
  exact hc

theorem ComparatorOptionD_to_ClayOptionD : ComparatorOptionD → ClayOptionD := by
  intro h ν hν
  obtain ⟨u₀, f, hu₀, hf, hno⟩ := h ν hν
  refine ⟨u₀, uncurryField f, admissibleDataPeriodic_of_comparator hu₀ hf, ?_⟩
  rintro ⟨u, p, hsol⟩
  apply hno
  refine ⟨curryField u, curryField p, ?_⟩
  have hc := claySolutionPeriodic_to_comparator hsol
  rw [curryField_uncurryField] at hc
  exact hc

#print axioms ComparatorOptionC_to_ClayOptionC
#print axioms ComparatorOptionD_to_ClayOptionD

end SemanticGap
