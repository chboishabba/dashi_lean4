/-
# Translation invariance of the cell integral

The increment carrier `δ_h u = u(·+h) − u` pairs the field at `x` with the field
at `x + h`, so every integral estimate for the increment needs the elementary
but genuinely necessary fact that the integral of a spatially periodic function
over the periodicity cell does not change when the function is translated:

`∫_cell f(t, x + v) dx = ∫_cell f(t, x) dx`   for every `v : ℝ³`.

The proof used here is the differentiation one: the one–parameter family
`s ↦ ∫_cell f(t, x + s·v) dx` is differentiable with derivative
`∫_cell ∂_v f(t, x + s·v) dx`, which vanishes because the cell integral of a
spatial derivative of a periodic field is zero (`cellInt_dvec_eq_zero`).  A
function of one real variable with vanishing derivative is constant, and
comparing `s = 1` with `s = 0` gives the statement.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.IncrementLocalizedLevelSet

open scoped BigOperators

noncomputable section

namespace ClayNS

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The affine reparametrisation `(s, x) ↦ (t, x + s·v)` of spacetime. -/
private def shiftPath (v : E3) : STime →L[ℝ] STime :=
  (ContinuousLinearMap.inr ℝ ℝ E3).comp
    ((ContinuousLinearMap.snd ℝ ℝ E3) + (ContinuousLinearMap.smulRight
      (ContinuousLinearMap.fst ℝ ℝ E3) v))

private lemma shiftPath_apply (v : E3) (z : STime) :
    (t, (0 : E3)) + shiftPath v z = (t, z.2 + z.1 • v) := by
  simp [shiftPath]

/-- **Translation invariance of the cell integral.**  For a smooth spatially
periodic scalar field and any translation vector `v`, the integral over the
periodicity cell of the translated field agrees with that of the field. -/
theorem cellInt_shift (f : STime → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hper : SpacePeriodic f) (t : ℝ) (v : E3) :
    cellInt (fun x => f (t, x + v)) = cellInt (fun x => f (t, x)) := by
  classical
  -- the one-parameter family, packaged as a spacetime field in the "time" slot `s`
  set F : STime → ℝ := fun z => f ((t, (0 : E3)) + shiftPath v z) with hFdef
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    hf.comp (contDiff_const.add (shiftPath v).contDiff)
  -- its "time" derivative is the directional derivative of `f` along `(0, v)`
  have hdF : ∀ s : ℝ, ∀ x : E3,
      dvec (1, 0) F (s, x) = fderiv ℝ f (t, x + s • v) ((0 : ℝ), v) := by
    intro s x
    have hcomp : HasFDerivAt F
        ((fderiv ℝ f ((t, (0 : E3)) + shiftPath v (s, x))).comp (shiftPath v)) (s, x) := by
      have h1 : HasFDerivAt (fun z : STime => (t, (0 : E3)) + shiftPath v z)
          (shiftPath v) (s, x) := by
        simpa using ((shiftPath v).hasFDerivAt).const_add (t, (0 : E3))
      exact ((hf.differentiable (by simp)) _).hasFDerivAt.comp (s, x) h1
    rw [dvec, hcomp.fderiv]
    have : shiftPath v ((1 : ℝ), (0 : E3)) = ((0 : ℝ), v) := by
      simp [shiftPath]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, this]
    rw [shiftPath_apply]
  -- the derivative of the family vanishes: it is the cell integral of a spatial derivative
  have hzero : ∀ s : ℝ, cellInt (fun x => dvec (1, 0) F (s, x)) = 0 := by
    intro s
    have hg : ContDiff ℝ (⊤ : ℕ∞) (shift (s • v) f) := contDiff_shift _ hf
    have hgper : SpacePeriodic (shift (s • v) f) := spacePeriodic_shift _ hper
    have hval : ∀ x : E3,
        dvec (1, 0) F (s, x) = ∑ i, (v i) * dvec (0, ee i) (shift (s • v) f) (t, x) := by
      intro x
      rw [hdF s x]
      have hshift : ∀ i : Fin 3,
          dvec (0, ee i) (shift (s • v) f) (t, x) = dspace f i (t, x + s • v) := by
        intro i
        rw [dvec_shift]
        simp [dspace, dvec]
      have hexp := fderiv_space_vector f (t, x + s • v) v
      rw [hexp]
      simp only [hshift, smul_eq_mul]
    rw [cellInt_congr hval]
    have hsum : cellInt (fun x => ∑ i, (v i) * dvec (0, ee i) (shift (s • v) f) (t, x))
        = ∑ i, (v i) * cellInt (fun x => dvec (0, ee i) (shift (s • v) f) (t, x)) := by
      classical
      have : ∀ (S : Finset (Fin 3)),
          cellInt (fun x => ∑ i ∈ S, (v i) * dvec (0, ee i) (shift (s • v) f) (t, x))
            = ∑ i ∈ S, (v i) * cellInt (fun x => dvec (0, ee i) (shift (s • v) f) (t, x)) := by
        intro S
        induction S using Finset.induction with
        | empty => simp [cellInt]
        | insert a S ha ih =>
            have hcont1 : Continuous
                (fun x : E3 => ∑ i ∈ S, (v i) * dvec (0, ee i) (shift (s • v) f) (t, x)) := by
              refine continuous_finset_sum _ fun i _ => ?_
              exact continuous_const.mul
                ((continuous_dvec _ hg (0, ee i)).comp (continuous_const.prodMk continuous_id))
            have hcont2 : Continuous
                (fun x : E3 => (v a) * dvec (0, ee a) (shift (s • v) f) (t, x)) :=
              continuous_const.mul
                ((continuous_dvec _ hg (0, ee a)).comp (continuous_const.prodMk continuous_id))
            rw [Finset.sum_insert ha]
            rw [show (fun x : E3 => ∑ i ∈ insert a S, (v i)
                  * dvec (0, ee i) (shift (s • v) f) (t, x))
                = fun x : E3 => (v a) * dvec (0, ee a) (shift (s • v) f) (t, x)
                  + ∑ i ∈ S, (v i) * dvec (0, ee i) (shift (s • v) f) (t, x) from by
              funext x; rw [Finset.sum_insert ha]]
            rw [cellInt_add hcont2 hcont1, ih,
              cellInt_const_mul (v a) (fun x => dvec (0, ee a) (shift (s • v) f) (t, x))]
      simpa using this Finset.univ
    rw [hsum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [cellInt_dvec_eq_zero _ hg hgper i t, mul_zero]
  -- hence the family is constant
  set G : ℝ → ℝ := fun s => cellInt (fun x => F (s, x)) with hGdef
  have hderiv : ∀ s : ℝ, HasDerivAt G (cellInt (fun x => dvec (1, 0) F (s, x))) s := fun s =>
    hasDerivAt_cellInt F hF s
  have hdiff : Differentiable ℝ G := fun s => (hderiv s).differentiableAt
  have hzero' : ∀ s : ℝ, deriv G s = 0 := by
    intro s
    rw [(hderiv s).deriv, hzero s]
  have hconst := is_const_of_deriv_eq_zero hdiff hzero' 1 0
  have h1 : G 1 = cellInt (fun x => f (t, x + v)) := by
    simp [hGdef, hFdef, shiftPath_apply]
  have h0 : G 0 = cellInt (fun x => f (t, x)) := by
    simp [hGdef, hFdef, shiftPath_apply]
  rw [← h1, ← h0]
  exact hconst

/-- Translation invariance of the cell integral, in the `shift` notation. -/
theorem cellInt_shift_fun (f : STime → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hper : SpacePeriodic f) (t : ℝ) (h : E3) :
    cellInt (fun x => shift h f (t, x)) = cellInt (fun x => f (t, x)) := by
  simpa using cellInt_shift f hf hper t h

end ClayNS
