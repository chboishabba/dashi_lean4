import ClaySpec

/-!
Cross-toolchain extract of the existing DASHI Mathlib-only differential
transport, ExternalClayNS/Gap.lean blob d19d04e4e8db66cf4128d1a063ea6a8b588538df.
No OpenAI comparator imports or new analytic estimates. Retain the original
theorem bodies so Alpöge–Buckmaster's independent solution package can use them
without importing the incompatible OpenAI source graph. This extract does not
assert cross-version proof identity: rebuild it in the original toolchain.
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


end SemanticGap
