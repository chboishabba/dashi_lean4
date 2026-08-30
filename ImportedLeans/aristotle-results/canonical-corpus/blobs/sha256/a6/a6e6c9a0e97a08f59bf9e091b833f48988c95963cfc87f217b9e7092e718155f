/-
# The localized Poincaré inequality at scale `L` (§12–§13)

The whole-space analogue of the torus spectral-gap argument needs, at scale `R`,
a *localized* Poincaré inequality

  `∫_{Q_R} |U − ⟨U⟩_{Q_R}|² ≤ C R² ∫_{Q_R} |∇U|²`,

with a constant that degenerates exactly like `R²` (this is what produces the
`R⁻²` damping rate of the differential inequality `D_R' + (c/R²) D_R ≤ error_R`).
This file derives it, with the explicit constant `3R²`, from the unit-cell
Poincaré inequality already proved in this development, by the change of
variables `x = x₀ + R y`.

* `ClayNS.integral_scaledCube` — the change of variables
  `∫_{Q_L(x₀)} F = L³ ∫_{[0,1]³} F(x₀ + L y) dy`;
* `ClayNS.parD_comp_scale` — the chain rule `∂_i(g(x₀ + L·)) = L (∂_i g)(x₀+L·)`;
* `ClayNS.scaledCube_poincare` — **the localized Poincaré inequality**
  `∫_{Q_L} (g − ⟨g⟩_{Q_L})² ≤ 3 L² ∑_i ∫_{Q_L} (∂_i g)²`.

This supplies the coercivity half of the localized argument of §12.  The other
half — that the boundary/pressure flux terms vanish as `R → ∞` for bounded
ancient solutions — is *not* proved here and remains part of the frontier
(item C).

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.Poincare

open MeasureTheory Set

noncomputable section

namespace ClayNS

/-- The cube of side `L` with lowest corner `x₀`, in cube coordinates. -/
def scaledCube (x0 : Fin 3 → ℝ) (L : ℝ) : Set (Fin 3 → ℝ) := Set.Icc x0 (x0 + fun _ => L)

/-- The integral over the cube of side `L`. -/
def scaledCubeInt (x0 : Fin 3 → ℝ) (L : ℝ) (g : (Fin 3 → ℝ) → ℝ) : ℝ :=
  ∫ x in scaledCube x0 L, g x

lemma image_cell_scale (x0 : Fin 3 → ℝ) {L : ℝ} (hL : 0 < L) :
    (fun y : Fin 3 → ℝ => x0 + L • y) '' cell = scaledCube x0 L := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' := hy
    rw [cell, Set.mem_Icc] at hy'
    refine Set.mem_Icc.2 ⟨?_, ?_⟩
    · intro i
      have h0 : (0 : ℝ) ≤ y i := hy'.1 i
      have : 0 ≤ L * y i := by positivity
      simpa using this
    · intro i
      have h1 : y i ≤ 1 := hy'.2 i
      have : L * y i ≤ L := by nlinarith
      simpa using this
  · intro hz
    rw [scaledCube, Set.mem_Icc] at hz
    refine ⟨fun i => L⁻¹ * (z i - x0 i), ?_, ?_⟩
    · rw [cell, Set.mem_Icc]
      constructor
      · intro i
        have := hz.1 i
        have hd : 0 ≤ z i - x0 i := by simpa using sub_nonneg.2 this
        have : 0 ≤ L⁻¹ * (z i - x0 i) := by positivity
        simpa using this
      · intro i
        have h2 := hz.2 i
        have hd : z i - x0 i ≤ L := by
          have : z i ≤ x0 i + L := by simpa using h2
          linarith
        have : L⁻¹ * (z i - x0 i) ≤ L⁻¹ * L := by
          exact mul_le_mul_of_nonneg_left hd (le_of_lt (inv_pos.mpr hL))
        rw [inv_mul_cancel₀ (ne_of_gt hL)] at this
        simpa using this
    · funext i
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← mul_assoc,
        mul_inv_cancel₀ (ne_of_gt hL)]

/-- **Change of variables.**  `∫_{Q_L(x₀)} F = L³ ∫_{[0,1]³} F(x₀ + L y) dy`. -/
theorem integral_scaledCube (x0 : Fin 3 → ℝ) {L : ℝ} (hL : 0 < L) (F : (Fin 3 → ℝ) → ℝ) :
    scaledCubeInt x0 L F = L ^ 3 * cubeInt (fun y => F (x0 + L • y)) := by
  have hf' : ∀ y ∈ cell,
      HasFDerivWithinAt (fun y : Fin 3 → ℝ => x0 + L • y)
        (L • ContinuousLinearMap.id ℝ (Fin 3 → ℝ)) cell y := by
    intro y _
    have hlin : HasFDerivAt (fun y : Fin 3 → ℝ => (L • ContinuousLinearMap.id ℝ (Fin 3 → ℝ)) y)
        (L • ContinuousLinearMap.id ℝ (Fin 3 → ℝ)) y := ContinuousLinearMap.hasFDerivAt _
    have h : HasFDerivAt (fun y : Fin 3 → ℝ => x0 + L • y)
        (L • ContinuousLinearMap.id ℝ (Fin 3 → ℝ)) y := by
      simpa using hlin.const_add x0
    exact h.hasFDerivWithinAt
  have hinj : InjOn (fun y : Fin 3 → ℝ => x0 + L • y) cell := by
    intro a _ b _ hab
    have h : L • a = L • b := by
      simpa using congrArg (fun z => z - x0) hab
    exact smul_right_injective (Fin 3 → ℝ) hL.ne' h
  have hcov := integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_cell
    hf' hinj F
  rw [image_cell_scale x0 hL] at hcov
  have hdet : ((L • ContinuousLinearMap.id ℝ (Fin 3 → ℝ)).det) = L ^ 3 := by
    simp [ContinuousLinearMap.det, LinearMap.det_smul]
  simp only [hdet, abs_of_pos (by positivity : (0:ℝ) < L ^ 3), smul_eq_mul] at hcov
  rw [scaledCubeInt, hcov, cubeInt, integral_const_mul]

/-- **Chain rule for the scaling.**  `∂_i (g(x₀ + L ·)) (y) = L (∂_i g)(x₀ + L y)`. -/
theorem parD_comp_scale (x0 : Fin 3 → ℝ) (L : ℝ) (g : (Fin 3 → ℝ) → ℝ)
    (hg : ContDiff ℝ 1 g) (i : Fin 3) (y : Fin 3 → ℝ) :
    parD i (fun y => g (x0 + L • y)) y = L * parD i g (x0 + L • y) := by
  have hg' : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hlin : HasFDerivAt (fun y : Fin 3 → ℝ => (L • ContinuousLinearMap.id ℝ (Fin 3 → ℝ)) y)
      (L • ContinuousLinearMap.id ℝ (Fin 3 → ℝ)) y := ContinuousLinearMap.hasFDerivAt _
  have hinner : HasFDerivAt (fun y : Fin 3 → ℝ => x0 + L • y)
      (L • ContinuousLinearMap.id ℝ (Fin 3 → ℝ)) y := by
    simpa using hlin.const_add x0
  have hcomp : HasFDerivAt (fun y : Fin 3 → ℝ => g (x0 + L • y))
      ((fderiv ℝ g (x0 + L • y)).comp (L • ContinuousLinearMap.id ℝ (Fin 3 → ℝ))) y :=
    (hg' _).hasFDerivAt.comp y hinner
  rw [parD, hcomp.fderiv, parD]
  simp [ContinuousLinearMap.smul_apply]

/-- **The localized Poincaré inequality.**  For a `C¹` function and a cube of
side `L > 0`,
`∫_{Q_L} (g − ⟨g⟩_{Q_L})² ≤ 3 L² ∑_i ∫_{Q_L} (∂_i g)²`,
where `⟨g⟩_{Q_L} = L⁻³ ∫_{Q_L} g`.  The constant degenerates exactly like `L²`,
which is the whole-space analogue of the torus spectral gap. -/
theorem scaledCube_poincare (x0 : Fin 3 → ℝ) {L : ℝ} (hL : 0 < L)
    (g : (Fin 3 → ℝ) → ℝ) (hg : ContDiff ℝ 1 g) :
    scaledCubeInt x0 L (fun x => (g x - (L ^ 3)⁻¹ * scaledCubeInt x0 L g) ^ 2)
      ≤ 3 * L ^ 2 * ∑ i, scaledCubeInt x0 L (fun x => (parD i g x) ^ 2) := by
  have hLne : (L : ℝ) ≠ 0 := ne_of_gt hL
  have hL3 : (L : ℝ) ^ 3 ≠ 0 := by positivity
  set gt : (Fin 3 → ℝ) → ℝ := fun y => g (x0 + L • y) with hgt
  have hsmooth : ContDiff ℝ 1 gt := by
    have haff : ContDiff ℝ 1 (fun y : Fin 3 → ℝ => x0 + L • y) := by fun_prop
    exact hg.comp haff
  have hbase := cubeInt_poincare gt hsmooth
  have hmean : cubeInt gt = (L ^ 3)⁻¹ * scaledCubeInt x0 L g := by
    rw [integral_scaledCube x0 hL g, hgt, ← mul_assoc, inv_mul_cancel₀ hL3, one_mul]
  have hlhs : cubeInt (fun y => (gt y - cubeInt gt) ^ 2)
      = (L ^ 3)⁻¹ * scaledCubeInt x0 L
          (fun x => (g x - (L ^ 3)⁻¹ * scaledCubeInt x0 L g) ^ 2) := by
    rw [hmean, integral_scaledCube x0 hL
      (fun x => (g x - (L ^ 3)⁻¹ * scaledCubeInt x0 L g) ^ 2), hgt,
      ← mul_assoc, inv_mul_cancel₀ hL3, one_mul]
  have hrhs : ∀ i : Fin 3, cubeInt (fun y => (parD i gt y) ^ 2)
      = L ^ 2 * ((L ^ 3)⁻¹ * scaledCubeInt x0 L (fun x => (parD i g x) ^ 2)) := by
    intro i
    have hpt : (fun y => (parD i gt y) ^ 2)
        = fun y => L ^ 2 * ((parD i g (x0 + L • y)) ^ 2) := by
      funext y
      rw [hgt, parD_comp_scale x0 L g hg i y, mul_pow]
    have hcov := integral_scaledCube x0 hL (fun x => (parD i g x) ^ 2)
    rw [hpt, cubeInt, integral_const_mul, ← cubeInt, hcov, ← mul_assoc ((L ^ 3)⁻¹),
      inv_mul_cancel₀ hL3, one_mul]
  have hsum : ∑ i, cubeInt (fun y => (parD i gt y) ^ 2)
      = L ^ 2 * (L ^ 3)⁻¹ * ∑ i, scaledCubeInt x0 L (fun x => (parD i g x) ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrhs i]
    ring
  rw [hlhs, hsum] at hbase
  set A := scaledCubeInt x0 L (fun x => (g x - (L ^ 3)⁻¹ * scaledCubeInt x0 L g) ^ 2) with hA
  set B := ∑ i, scaledCubeInt x0 L (fun x => (parD i g x) ^ 2) with hB
  have hpos : (0:ℝ) < L ^ 3 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hbase (le_of_lt hpos)
  rw [← mul_assoc, mul_inv_cancel₀ hL3, one_mul] at hmul
  have hR : L ^ 3 * (3 * (L ^ 2 * (L ^ 3)⁻¹ * B)) = 3 * L ^ 2 * B := by
    field_simp
  rwa [hR] at hmul

end ClayNS
