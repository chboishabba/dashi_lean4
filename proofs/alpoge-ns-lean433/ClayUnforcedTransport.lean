import UnforcedAdmission
import ClayDifferentialTransport

/-! Direct original unforced-to-literal-Clay D transport.
The donor differential lemmas are unchanged; the new proof uses the same
velocity and pressure under the time/space coordinate swap. No force is
introduced. The original nonexistence permits arbitrary pressure, so the
Clay erratum's stricter periodic-pressure requirement is harmless. -/

noncomputable section
open scoped ContDiff Laplacian ENNReal
open MeasureTheory Set InnerProductSpace
open ClaySpec SemanticGap

namespace DASHI.AlpogeBuckmaster

def timeFirst {E : Type*} (g : SpaceTime → E) : ℝ → R3 → E :=
  fun t x => g (x, t)

theorem timeFirst_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : SpaceTime → E} (hg : TrustBoundarySmoothOn g) :
    ContDiffOn ℝ ∞ (fun z : ℝ × R3 => timeFirst g z.1 z.2)
      (Set.Ici 0 ×ˢ Set.univ) := by
  have hs : ContDiff ℝ ∞ (fun z : ℝ × R3 => (z.2, z.1)) :=
    contDiff_snd.prodMk contDiff_fst
  exact hg.comp hs.contDiffOn (fun z hz => hz.1)

theorem initialDivergence_original {u₀ : InitialVelocity}
    (hs : ContDiff ℝ ∞ u₀) (x : R3) :
    initialDivergence u₀ x = Breakdown.divergenceAt u₀ x := by
  unfold initialDivergence Breakdown.divergenceAt
  apply Finset.sum_congr rfl
  intro i hi
  exact fderiv_component (hs.differentiable (by simp) x) i (spatialBasis i)

theorem divergence_original {u : Velocity}
    (hs : TrustBoundarySmoothOn u) (x : R3) {t : ℝ} (ht : 0 ≤ t) :
    divergence u (x,t) = Breakdown.divergenceAt (timeFirst u t) x := by
  unfold divergence Breakdown.divergenceAt
  apply Finset.sum_congr rfl
  intro i hi
  rw [partialSpace_eq_slice (component_smooth hs i) x ht i]
  exact fderiv_component ((smooth_space_slice hs ht).differentiable (by simp) x)
    i (spatialBasis i)

theorem laplacian_original (v : R3 → R3) (x : R3) :
    Δ v x = Breakdown.sumSecondPartialsAt v x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    v (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [Breakdown.sumSecondPartialsAt, Breakdown.unitVector,
    EuclideanSpace.basisFun_apply]

theorem gradient_original (p : R3 → ℝ) (x : R3) :
    gradient p x = Breakdown.gradientAt p x := by
  ext i
  have h := inner_gradient_right (𝕜 := ℝ) (f := p)
    (x := spatialBasis i) (y := x)
  have hi : fderiv ℝ p x (spatialBasis i) = (gradient p x) i := by
    simpa [spatialBasis, EuclideanSpace.inner_single_left,
      starRingEnd_apply, star_trivial] using h.symm
  simp [Breakdown.gradientAt, Breakdown.unitVector, ← hi, spatialBasis]

/-- Same physical momentum and divergence, no assumptions on the force
except its literal equality to zero. The source requires t>0 only. -/
theorem solution_original {ν : ℝ} {u₀ : InitialVelocity} {u : Velocity} {p : Pressure}
    (hu : TrustBoundarySmoothOn u) (hp : TrustBoundarySmoothOn p)
    (he : EquationOne ν u p (fun _ => 0)) (hd : EquationTwo u)
    (hi : EquationThree u₀ u) :
    Breakdown.IsSmoothSolution ν u₀ (timeFirst u) (timeFirst p) := by
  refine ⟨timeFirst_smooth hu, timeFirst_smooth hp, hi, ?_, ?_⟩
  · intro t ht x
    have h := equationOne_to_comparator ν u p (fun _ => 0) hu hp he x t ht.le
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht), laplacian_original,
      gradient_original, add_zero] at h
    exact h
  · intro t ht x
    rw [← divergence_original hu x ht.le]
    exact hd (x,t) ht.le

theorem zeroDirectional (dirs : List SpaceTime) :
    iteratedDirectionalWithin dirs (fun _ => (0 : R3)) = fun _ => 0 := by
  induction dirs with
  | nil => rfl
  | cons v vs ih =>
    simp [iteratedDirectionalWithin, ih]

theorem zeroPeriodicForce : ForceRapidDecayPeriodic (fun _ => 0) := by
  intro α m K
  refine ⟨0, le_rfl, ?_⟩
  intro z hz
  simp [zeroDirectional]

/-- No need for a pressure-periodicity assumption in the original
nonexistence theorem; any literal Clay solution is among the excluded ones. -/
theorem original_torus_to_clayD (h : Breakdown.BreakdownOnTorus) : ClayOptionD := by
  intro ν hν
  obtain ⟨u₀, hs, hper, hd, hn⟩ := h ν hν
  refine ⟨u₀, (fun _ => 0), ⟨hs, ?_, ?_, contDiffOn_const, ?_, zeroPeriodicForce⟩, ?_⟩
  · intro x
    rw [initialDivergence_original hs]
    exact hd x
  · intro x i
    exact hper i x
  · intro z hz i
    rfl
  · rintro ⟨u,p,hu,hp,he,hdiv,hi,hup,hpp⟩
    apply hn
    refine ⟨timeFirst u, timeFirst p, solution_original hu hp he hdiv hi, ?_⟩
    intro t ht i x
    exact hup (x,t) ht i


/-- A compactly supported smooth field has compactly supported smooth
directional derivatives of every order, with the original word retained. -/
theorem spatialWord_smooth_compact (dirs : List R3) {u₀ : InitialVelocity}
    (hs : ContDiff ℝ ∞ u₀) (hc : HasCompactSupport u₀) :
    ContDiff ℝ ∞ (iteratedSpatialDirectional dirs u₀) ∧
      HasCompactSupport (iteratedSpatialDirectional dirs u₀) := by
  induction dirs with
  | nil => exact ⟨hs, hc⟩
  | cons v vs ih =>
    change ContDiff ℝ ∞
        (fun x => fderiv ℝ (iteratedSpatialDirectional vs u₀) x v) ∧
      HasCompactSupport (fun x => fderiv ℝ (iteratedSpatialDirectional vs u₀) x v)
    exact ⟨(ih.1.fderiv_right (by simp)).clm_apply contDiff_const,
      ih.2.fderiv_apply ℝ v⟩

theorem compactInitialRapidDecay {u₀ : InitialVelocity}
    (hs : ContDiff ℝ ∞ u₀) (hc : HasCompactSupport u₀) : InitialRapidDecay u₀ := by
  intro α K
  let g := iteratedSpatialDirectional (initialSpatialWord α) u₀
  obtain ⟨hgs, hgc⟩ := spatialWord_smooth_compact (initialSpatialWord α) hs hc
  let w : R3 → ℝ := fun x => ‖g x‖ * (1 + ‖x‖)^K
  have hw : Continuous w := hgs.continuous.norm.mul ((continuous_const.add continuous_norm).pow K)
  have hwc : HasCompactSupport w := by
    apply hgc.of_isClosed_subset (isClosed_tsupport w)
    apply closure_mono
    intro x hx
    apply Function.mem_support.mpr
    intro hzero
    exact (Function.mem_support.mp hx) (by simp [w, hzero])
  obtain ⟨B, hB⟩ := hw.bounded_above_of_compact_support hwc
  refine ⟨max B 0, le_max_right _ _, fun x => ?_⟩
  apply (le_div_iff₀ (by positivity : 0 < (1 + ‖x‖)^K)).2
  have hb : 0 ≤ w x := by dsimp [w]; positivity
  calc
    ‖g x‖ * (1 + ‖x‖)^K = |w x| := (abs_of_nonneg hb).symm
    _ ≤ B := by simpa [Real.norm_eq_abs] using hB x
    _ ≤ max B 0 := le_max_left _ _

theorem zeroSpaceForce : ForceRapidDecayR3 (fun _ => 0) := by
  intro α m K
  refine ⟨0, le_rfl, ?_⟩
  intro z hz
  simp [zeroDirectional]

/-- The actual finite Lebesgue integral in ClaySpec bounds the
nonnegative extended-real integral used by the original paper. -/
theorem boundedEnergy_original {u : Velocity} (h : BoundedEnergy u) :
    ∃ C : ℝ, ∀ t ≥ 0,
      (∫⁻ x, ENNReal.ofReal (‖timeFirst u t x‖ ^ 2)) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun t ht => ?_⟩
  obtain ⟨hlp, hlt⟩ := hC t ht
  have hi : Integrable (fun x : R3 => ‖u (x,t)‖ ^ 2) volume :=
    hlp.integrable_norm_pow (p := 2) (by decide)
  have hnn : 0 ≤ᵐ[volume] (fun x : R3 => ‖u (x,t)‖ ^ 2) :=
    Filter.Eventually.of_forall (fun x => sq_nonneg _)
  change (∫⁻ x, ENNReal.ofReal (‖u (x,t)‖ ^ 2)) ≤ ENNReal.ofReal C
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn]
  exact ENNReal.ofReal_le_ofReal hlt.le

/-- Direct whole-space source admission: compactly supported actual initial
data and zero force satisfy the frozen Clay C specification. -/
theorem original_space_to_clayC (h : Breakdown.BreakdownOnSpace) : ClayOptionC := by
  intro ν hν
  obtain ⟨u₀, hs, hc, hd, hn⟩ := h ν hν
  refine ⟨u₀, (fun _ => 0), ⟨hs, ?_, compactInitialRapidDecay hs hc,
    contDiffOn_const, zeroSpaceForce⟩, ?_⟩
  · intro x
    rw [initialDivergence_original hs]
    exact hd x
  · rintro ⟨u,p,hu,hp,he,hdiv,hi,henergy⟩
    exact hn ⟨timeFirst u, timeFirst p, solution_original hu hp he hdiv hi,
      boundedEnergy_original henergy⟩

open Breakdown Breakdown.CertCell Breakdown.CertCell.GivenShape Breakdown.CellLayerSystem

theorem original_cell_condition_to_clayD {k : ℕ} {C : Type} {nE nM : ℕ}
    (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM)
    (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R)
    (Y : CellLayerEntries D R T) (N : CoerciveNumbers) (B : ReductionEntries k)
    (h : CellSystemCondition D X R T Y N B) : ClayOptionD :=
  original_torus_to_clayD (from_original_cell_condition D X R T Y N B h).2.1

theorem original_cell_condition_to_clayC {k : ℕ} {C : Type} {nE nM : ℕ}
    (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM)
    (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R)
    (Y : CellLayerEntries D R T) (N : CoerciveNumbers) (B : ReductionEntries k)
    (h : CellSystemCondition D X R T Y N B) : ClayOptionC :=
  original_space_to_clayC (from_original_cell_condition D X R T Y N B h).1

#print axioms DASHI.AlpogeBuckmaster.original_space_to_clayC
#print axioms DASHI.AlpogeBuckmaster.original_cell_condition_to_clayC
#print axioms DASHI.AlpogeBuckmaster.solution_original
#print axioms DASHI.AlpogeBuckmaster.original_torus_to_clayD
#print axioms DASHI.AlpogeBuckmaster.original_cell_condition_to_clayD

end DASHI.AlpogeBuckmaster
