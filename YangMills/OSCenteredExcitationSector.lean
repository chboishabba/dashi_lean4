import Mathlib
import YangMills.OSGramRawDenseSameFamilyWeld
import YangMills.PreGapOSSemigroup

open Filter MeasureTheory

/-!
# Centered OS excitation sector

The mixed Wilson covariance is a centered correlation.  Therefore the family
carrying exponential decay must be dense in the vacuum-orthogonal excitation
sector, not in a Hilbert space that also contains an invariant vacuum.

This owner makes that correction structural.  For a normalized vacuum `Ω`,

    P₀ x = x - <Ω,x> Ω

is a continuous surjection onto `Ω⊥`.  Since raw OS vectors are already dense
in the quotient completion, their centered images are dense in `Ω⊥` by
composition.  Thus excitation-sector density is again construction-owned once
the physical vacuum and the raw OS carrier are the same objects.
-/

namespace RequestProject.YangMills

/-- The vacuum-orthogonal excitation sector. -/
def vacuumOrthogonalSubmodule
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω : H) : Submodule ℝ H :=
  (innerSL ℝ Ω).ker

/-- Center any Hilbert vector and regard it as a vector in `Ω⊥`. -/
def centerToVacuumOrthogonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω : H) (hNormalized : ⟪Ω, Ω⟫_ℝ = 1) :
    H → vacuumOrthogonalSubmodule Ω :=
  fun x =>
    ⟨osCenteredWilsonVector Ω x, by
      change ⟪Ω, osCenteredWilsonVector Ω x⟫_ℝ = 0
      exact os_centered_wilson_orthogonal Ω x hNormalized⟩

/-- Centering into the excitation sector is continuous. -/
theorem continuous_centerToVacuumOrthogonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω : H) (hNormalized : ⟪Ω, Ω⟫_ℝ = 1) :
    Continuous (centerToVacuumOrthogonal Ω hNormalized) := by
  apply Continuous.subtype_mk
  · simp only [centerToVacuumOrthogonal, osCenteredWilsonVector]
    fun_prop
  · intro x
    exact (centerToVacuumOrthogonal Ω hNormalized x).property

/-- Every excitation-sector vector is fixed by centering, hence centering is onto `Ω⊥`. -/
theorem surjective_centerToVacuumOrthogonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω : H) (hNormalized : ⟪Ω, Ω⟫_ℝ = 1) :
    Function.Surjective (centerToVacuumOrthogonal Ω hNormalized) := by
  intro y
  refine ⟨(y : H), ?_⟩
  apply Subtype.ext
  have hy : ⟪Ω, (y : H)⟫_ℝ = 0 := by
    exact y.property
  simp [centerToVacuumOrthogonal, osCenteredWilsonVector, hy]

/-- The centering projection has dense range because it is surjective. -/
theorem denseRange_centerToVacuumOrthogonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω : H) (hNormalized : ⟪Ω, Ω⟫_ℝ = 1) :
    DenseRange (centerToVacuumOrthogonal Ω hNormalized) :=
  (surjective_centerToVacuumOrthogonal Ω hNormalized).denseRange

namespace OSGramData

/-- Centered OS vector associated to a raw positive-time observable. -/
noncomputable def centeredRawVector
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V)
    (Ω : data.Hilbert) (hNormalized : ⟪Ω, Ω⟫_ℝ = 1) :
    V → vacuumOrthogonalSubmodule Ω :=
  (centerToVacuumOrthogonal Ω hNormalized) ∘ data.rawVector

/--
Centered raw OS vectors are dense in the excitation sector.  This is the
correct structural F2 statement in the presence of a non-null invariant vacuum.
-/
theorem denseRange_centeredRawVector
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V)
    (Ω : data.Hilbert) (hNormalized : ⟪Ω, Ω⟫_ℝ = 1) :
    DenseRange (data.centeredRawVector Ω hNormalized) := by
  exact (denseRange_centerToVacuumOrthogonal Ω hNormalized).comp
    data.denseRange_rawVector
    (continuous_centerToVacuumOrthogonal Ω hNormalized)

/-- The real span of centered raw vectors is dense in `Ω⊥`. -/
theorem dense_centeredRawVector_span
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V)
    (Ω : data.Hilbert) (hNormalized : ⟪Ω, Ω⟫_ℝ = 1) :
    Dense
      (Submodule.span ℝ
        (Set.range (data.centeredRawVector Ω hNormalized)) :
        Set (vacuumOrthogonalSubmodule Ω)) :=
  (data.denseRange_centeredRawVector Ω hNormalized).mono
    (fun _ hx => Submodule.subset_span hx)

end OSGramData

/--
Mixed left/right centering identity.  This is the source-correct algebraic form
for connected Wilson covariance, rather than the autocorrelation-only version.
-/
theorem os_centered_mixed_semigroup_correlation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω left right : H) (T : H →ₗ[ℝ] H)
    (hNormalized : ⟪Ω, Ω⟫_ℝ = 1)
    (hVacuumFixed : T Ω = Ω)
    (hSymmetric : ∀ x y : H, ⟪x, T y⟫_ℝ = ⟪T x, y⟫_ℝ) :
    ⟪osCenteredWilsonVector Ω left,
        T (osCenteredWilsonVector Ω right)⟫_ℝ =
      ⟪left, T right⟫_ℝ - ⟪Ω, left⟫_ℝ * ⟪Ω, right⟫_ℝ := by
  have hVacRight : ⟪Ω, T right⟫_ℝ = ⟪Ω, right⟫_ℝ := by
    rw [hSymmetric Ω right, hVacuumFixed]
  have hLeftVac : ⟪left, Ω⟫_ℝ = ⟪Ω, left⟫_ℝ :=
    real_inner_comm left Ω
  have hT :
      T (osCenteredWilsonVector Ω right) =
        T right - (⟪Ω, right⟫_ℝ) • Ω := by
    simp [osCenteredWilsonVector, map_sub, map_smul, hVacuumFixed]
  rw [osCenteredWilsonVector, hT]
  simp only [inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [hVacRight, hLeftVac, hNormalized]
  ring

/-- A symmetric transfer fixing the vacuum preserves the excitation sector. -/
theorem os_transfer_preserves_vacuumOrthogonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω : H) (T : H →ₗ[ℝ] H)
    (hVacuumFixed : T Ω = Ω)
    (hSymmetric : ∀ x y : H, ⟪x, T y⟫_ℝ = ⟪T x, y⟫_ℝ)
    {x : H} (hx : x ∈ vacuumOrthogonalSubmodule Ω) :
    T x ∈ vacuumOrthogonalSubmodule Ω := by
  change ⟪Ω, T x⟫_ℝ = 0
  rw [hSymmetric Ω x, hVacuumFixed]
  exact hx

end RequestProject.YangMills
