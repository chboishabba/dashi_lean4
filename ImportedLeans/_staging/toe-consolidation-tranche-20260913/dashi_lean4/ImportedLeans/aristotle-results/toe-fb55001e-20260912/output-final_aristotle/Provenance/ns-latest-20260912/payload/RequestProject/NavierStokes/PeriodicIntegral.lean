/-
# Integration over the periodicity cell, and the two analytic tools needed to
# turn the pointwise identities of this development into global balances.

The local (pointwise) energy and enstrophy identities of
`RequestProject/NavierStokes/EnergyIdentity.lean` become *a priori bounds* only
after integration over the periodicity cell `[0,1]³`.  Two genuine analytic
facts are needed for that, and both are derived here from Mathlib:

* `ClayNS.cellInt_divergence_eq_zero` — the divergence theorem on the torus:
  the cell integral of `div F` vanishes for every `C¹` spatially `ℤ³`-periodic
  family of fluxes `F`.  It is obtained from Mathlib's Bochner divergence
  theorem on a box, the face contributions cancelling in pairs by periodicity.
* `ClayNS.hasDerivAt_cellInt` — differentiation under the integral sign,
  `d/dt ∫_cell f(t,x) dx = ∫_cell ∂_t f(t,x) dx` for smooth `f`, with the
  domination supplied by compactness of the cell.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.EnergyIdentity

open scoped BigOperators
open MeasureTheory Set

noncomputable section

namespace ClayNS

/-! ## The periodicity cell -/

/-- Coordinates on `ℝ³`: the continuous linear identification of `Fin 3 → ℝ`
with the Euclidean space `E3`. -/
def coord : (Fin 3 → ℝ) ≃L[ℝ] E3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm

@[simp] lemma coord_single (i : Fin 3) : coord (Pi.single i 1) = ee i := rfl

/-- The unit periodicity cell, in coordinates. -/
def cell : Set (Fin 3 → ℝ) := Set.Icc 0 1

lemma isCompact_cell : IsCompact cell := isCompact_Icc

lemma measurableSet_cell : MeasurableSet cell := measurableSet_Icc

/-- The integral of a scalar field over the periodicity cell `[0,1]³`. -/
def cellInt (f : E3 → ℝ) : ℝ := ∫ x in cell, f (coord x)

lemma integrableOn_cell_of_continuous {f : E3 → ℝ} (hf : Continuous f) :
    IntegrableOn (fun x => f (coord x)) cell :=
  (hf.comp coord.continuous).continuousOn.integrableOn_compact isCompact_cell

lemma cellInt_add {f g : E3 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    cellInt (fun x => f x + g x) = cellInt f + cellInt g := by
  simpa [cellInt] using
    integral_add (integrableOn_cell_of_continuous hf) (integrableOn_cell_of_continuous hg)

lemma cellInt_sub {f g : E3 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    cellInt (fun x => f x - g x) = cellInt f - cellInt g := by
  simpa [cellInt] using
    integral_sub (integrableOn_cell_of_continuous hf) (integrableOn_cell_of_continuous hg)

lemma cellInt_neg (f : E3 → ℝ) : cellInt (fun x => - f x) = - cellInt f := by
  simp [cellInt, integral_neg]

lemma cellInt_const_mul (c : ℝ) (f : E3 → ℝ) :
    cellInt (fun x => c * f x) = c * cellInt f := by
  simp [cellInt, integral_const_mul]

lemma cellInt_nonneg {f : E3 → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ cellInt f :=
  setIntegral_nonneg measurableSet_cell fun x _ => hf (coord x)

lemma cellInt_congr {f g : E3 → ℝ} (h : ∀ x, f x = g x) : cellInt f = cellInt g := by
  simp only [cellInt, h]

lemma cellInt_mono {f g : E3 → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x, f x ≤ g x) : cellInt f ≤ cellInt g := by
  have h0 : 0 ≤ cellInt (fun x => g x - f x) := cellInt_nonneg fun x => sub_nonneg.mpr (h x)
  rw [cellInt_sub hg hf] at h0
  linarith

/-! ## The divergence theorem on the torus -/

lemma insertNth_one_eq (i : Fin 3) (y : Fin 2 → ℝ) :
    (Fin.insertNth i (1 : ℝ) y : Fin 3 → ℝ)
      = (Fin.insertNth i (0 : ℝ) y : Fin 3 → ℝ) + Pi.single i (1 : ℝ) := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨k, rfl⟩
  · subst h; simp
  · simp

/-- **Divergence theorem on the torus.**  For a `C¹` family of scalar fields
`F₀,F₁,F₂` which are `ℤ³`-periodic, the cell integral of the divergence
`∑ᵢ ∂ᵢ Fᵢ` vanishes: the face contributions of the box `[0,1]³` cancel in pairs
by periodicity. -/
theorem cellInt_divergence_eq_zero (F : Fin 3 → E3 → ℝ)
    (hF : ∀ i, ContDiff ℝ (1 : ℕ) (F i))
    (hper : ∀ (i j : Fin 3) (x : E3), F i (x + ee j) = F i x) :
    cellInt (fun x => ∑ i, fderiv ℝ (F i) x (ee i)) = 0 := by
  have hle : (0 : Fin 3 → ℝ) ≤ 1 := fun _ => zero_le_one
  set f : Fin 3 → (Fin 3 → ℝ) → ℝ := fun i x => F i (coord x) with hf
  set f' : Fin 3 → (Fin 3 → ℝ) → ((Fin 3 → ℝ) →L[ℝ] ℝ) :=
    fun i x => (fderiv ℝ (F i) (coord x)).comp (coord : (Fin 3 → ℝ) →L[ℝ] E3) with hf'
  have hdiff : ∀ i, Differentiable ℝ (F i) := fun i => (hF i).differentiable (by simp)
  have hcontfd : ∀ i, Continuous (fun x : E3 => fderiv ℝ (F i) x) :=
    fun i => (hF i).continuous_fderiv (by simp)
  have hHc : ∀ i, ContinuousOn (f i) (Icc (0 : Fin 3 → ℝ) 1) := fun i =>
    (((hF i).continuous).comp coord.continuous).continuousOn
  have hHd : ∀ x ∈ (Set.univ.pi fun i => Ioo ((0 : Fin 3 → ℝ) i) ((1 : Fin 3 → ℝ) i))
      \ (∅ : Set (Fin 3 → ℝ)), ∀ i, HasFDerivAt (f i) (f' i x) x := fun x _ i =>
    ((hdiff i) (coord x)).hasFDerivAt.comp x (coord : (Fin 3 → ℝ) →L[ℝ] E3).hasFDerivAt
  have hHi : IntegrableOn (fun x => ∑ i, f' i x (Pi.single i 1))
      (Icc (0 : Fin 3 → ℝ) 1) volume := by
    apply Continuous.continuousOn _ |>.integrableOn_compact isCompact_Icc
    refine continuous_finset_sum _ fun i _ => ?_
    exact ((hcontfd i).comp coord.continuous).clm_apply continuous_const
  have key := MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'
      (0 : Fin 3 → ℝ) 1 hle f f' ∅ Set.countable_empty hHc hHd hHi
  have hfaces : ∀ i : Fin 3,
      ((∫ y in Icc ((0 : Fin 3 → ℝ) ∘ i.succAbove) ((1 : Fin 3 → ℝ) ∘ i.succAbove),
          f i (i.insertNth ((1 : Fin 3 → ℝ) i) y)) -
        ∫ y in Icc ((0 : Fin 3 → ℝ) ∘ i.succAbove) ((1 : Fin 3 → ℝ) ∘ i.succAbove),
          f i (i.insertNth ((0 : Fin 3 → ℝ) i) y)) = 0 := by
    intro i
    have hpt : ∀ y : Fin 2 → ℝ,
        f i (i.insertNth ((1 : Fin 3 → ℝ) i) y) = f i (i.insertNth ((0 : Fin 3 → ℝ) i) y) := by
      intro y
      have h1 : ((1 : Fin 3 → ℝ) i) = (1 : ℝ) := rfl
      have h0 : ((0 : Fin 3 → ℝ) i) = (0 : ℝ) := rfl
      rw [h1, h0, hf]
      simp only
      rw [insertNth_one_eq i y, map_add, coord_single]
      exact hper i i _
    simp only [hpt, sub_self]
  rw [show cellInt (fun x => ∑ i, fderiv ℝ (F i) x (ee i))
      = ∫ x in Icc (0 : Fin 3 → ℝ) 1, ∑ i, f' i x (Pi.single i 1) from rfl, key]
  exact Finset.sum_eq_zero fun i _ => hfaces i

/-! ## Spatial and temporal slices of spacetime fields -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The spatial slice `y ↦ V (t, y)` of a smooth spacetime field is smooth. -/
lemma contDiff_slice (V : STime → F) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : E3 => V (t, y)) :=
  hV.comp (contDiff_const.prodMk contDiff_id)

lemma hasFDerivAt_slice (V : STime → F) (hV : Differentiable ℝ V) (t : ℝ) (x : E3) :
    HasFDerivAt (fun y : E3 => V (t, y))
      ((fderiv ℝ V (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E3)) x := by
  have hid : HasFDerivAt (fun y : E3 => y) (ContinuousLinearMap.id ℝ E3) x := hasFDerivAt_id x
  have hc : HasFDerivAt (fun _ : E3 => (t : ℝ)) (0 : E3 →L[ℝ] ℝ) x := hasFDerivAt_const _ _
  have h0 : HasFDerivAt (fun y : E3 => ((t : ℝ), y)) (ContinuousLinearMap.inr ℝ ℝ E3) x := by
    simpa using hc.prodMk hid
  exact (hV (t, x)).hasFDerivAt.comp x h0

/-- A spatial derivative of a spacetime field is the derivative of its spatial
slice. -/
lemma fderiv_slice_apply (V : STime → F) (hV : Differentiable ℝ V) (t : ℝ) (x : E3)
    (m : E3) : fderiv ℝ (fun y : E3 => V (t, y)) x m = dvec (0, m) V (t, x) := by
  rw [(hasFDerivAt_slice V hV t x).fderiv]
  rfl

/-- Along a time slice, `∂_t` is an honest one-dimensional derivative. -/
lemma hasDerivAt_time_slice (f : STime → ℝ) (hf : Differentiable ℝ f) (s : ℝ) (y : E3) :
    HasDerivAt (fun r : ℝ => f (r, y)) (dvec (1, 0) f (s, y)) s := by
  have h0 : HasDerivAt (fun r : ℝ => ((r : ℝ), y)) ((1 : ℝ), (0 : E3)) s := by
    have hid : HasDerivAt (fun r : ℝ => r) (1 : ℝ) s := hasDerivAt_id s
    have hc : HasDerivAt (fun _ : ℝ => y) (0 : E3) s := hasDerivAt_const _ _
    simpa using hid.prodMk hc
  exact (hf (s, y)).hasFDerivAt.comp_hasDerivAt s h0

lemma shift_pair (z : STime) (j : Fin 3) : z + ((0 : ℝ), ee j) = (z.1, z.2 + ee j) := by
  simp [Prod.ext_iff]

/-- Every derivative of a spatially periodic smooth field is spatially
periodic. -/
lemma spacePeriodic_dvec {V : STime → F} (hV : Differentiable ℝ V)
    (hper : SpacePeriodic V) (a : STime) : SpacePeriodic (dvec a V) := by
  intro z j
  have hfun : (fun w : STime => V (w + ((0 : ℝ), ee j))) = V := by
    funext w
    rw [shift_pair w j]
    exact hper w j
  have h1 : HasFDerivAt (fun w : STime => V (w + ((0 : ℝ), ee j)))
      (fderiv ℝ V (z + ((0 : ℝ), ee j))) z := by
    have := (hV (z + ((0 : ℝ), ee j))).hasFDerivAt.comp z
      ((hasFDerivAt_id z).add_const ((0 : ℝ), ee j))
    simpa using this
  rw [hfun] at h1
  have h2 : fderiv ℝ V (z + ((0 : ℝ), ee j)) = fderiv ℝ V z := h1.fderiv.symm
  show fderiv ℝ V (z.1, z.2 + ee j) a = fderiv ℝ V z a
  rw [← shift_pair z j, h2]

/-- **Divergence theorem on the torus, spacetime form.**  At every fixed time,
the cell integral of the spatial divergence of a smooth spatially periodic
family of fluxes vanishes. -/
theorem cellInt_dvec_divergence_eq_zero (G : Fin 3 → STime → ℝ)
    (hG : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i)) (hper : ∀ i, SpacePeriodic (G i)) (t : ℝ) :
    cellInt (fun x => ∑ i, dvec (0, ee i) (G i) (t, x)) = 0 := by
  have hGd : ∀ i, Differentiable ℝ (G i) := fun i => (hG i).differentiable (by simp)
  have hslice : ∀ i, ContDiff ℝ (1 : ℕ) (fun y : E3 => G i (t, y)) := fun i =>
    (contDiff_slice (G i) (hG i) t).of_le (by exact_mod_cast le_top)
  have hperslice : ∀ (i j : Fin 3) (x : E3),
      (fun y : E3 => G i (t, y)) (x + ee j) = (fun y : E3 => G i (t, y)) x :=
    fun i j x => hper i (t, x) j
  have h := cellInt_divergence_eq_zero (fun i y => G i (t, y)) hslice hperslice
  have hcongr : cellInt (fun x => ∑ i, dvec (0, ee i) (G i) (t, x))
      = cellInt (fun x => ∑ i, fderiv ℝ (fun y : E3 => G i (t, y)) x (ee i)) :=
    cellInt_congr fun x =>
      Finset.sum_congr rfl fun i _ => (fderiv_slice_apply (G i) (hGd i) t x (ee i)).symm
  exact hcongr.trans h

/-- **Integration by parts on the torus, one direction.**  The cell integral of
a single spatial derivative of a smooth periodic field vanishes. -/
theorem cellInt_dvec_eq_zero (f : STime → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hper : SpacePeriodic f) (a : Fin 3) (t : ℝ) :
    cellInt (fun x => dvec (0, ee a) f (t, x)) = 0 := by
  classical
  set G : Fin 3 → STime → ℝ := fun i => if i = a then f else fun _ => 0 with hG
  have hGsmooth : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i) := by
    intro i
    by_cases h : i = a <;> simp [hG, h, hf, contDiff_const]
  have hGper : ∀ i, SpacePeriodic (G i) := by
    intro i
    by_cases h : i = a
    · simpa [hG, h] using hper
    · intro z j; simp [hG, h]
  have hzero := cellInt_dvec_divergence_eq_zero G hGsmooth hGper t
  have hpt : ∀ x : E3, (∑ i, dvec (0, ee i) (G i) (t, x)) = dvec (0, ee a) f (t, x) := by
    intro x
    refine Finset.sum_eq_single a ?_ (fun h => absurd (Finset.mem_univ a) h) |>.trans ?_
    · intro i _ hne
      simp [hG, hne, dvec]
    · simp [hG]
  rw [← cellInt_congr hpt]
  exact hzero

/-! ## Differentiation under the cell integral -/

/-- **Continuity of the cell integral in a parameter.** -/
theorem continuous_cellInt (f : STime → ℝ) (hf : Continuous f) :
    Continuous (fun s => cellInt (fun x => f (s, x))) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hcont2 : Continuous fun p : ℝ × (Fin 3 → ℝ) => f (p.1, coord p.2) :=
    hf.comp (continuous_fst.prodMk (coord.continuous.comp continuous_snd))
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := t - 1) (b := t + 1)).prod isCompact_cell
      ).exists_bound_of_continuousOn hcont2.continuousOn
  have hμfin : (volume.restrict cell) Set.univ < ⊤ := by
    simpa [Measure.restrict_apply_univ] using isCompact_cell.measure_lt_top (μ := volume)
  refine MeasureTheory.continuousAt_of_dominated (bound := fun _ => C)
    (Filter.Eventually.of_forall fun _ =>
      (hf.comp (continuous_const.prodMk coord.continuous)).aestronglyMeasurable)
    ?_ (integrableOn_const (by simpa using hμfin.ne)) ?_
  · filter_upwards [Metric.ball_mem_nhds t one_pos] with s hs
    filter_upwards [ae_restrict_mem measurableSet_cell] with x hx
    have hs' : s ∈ Set.Icc (t - 1) (t + 1) := by
      have h := Metric.mem_ball.mp hs
      rw [Real.dist_eq, abs_lt] at h
      constructor <;> linarith [h.1, h.2]
    exact hC (s, x) ⟨hs', hx⟩
  · filter_upwards with x
    exact (hf.comp (continuous_id.prodMk continuous_const)).continuousAt

/-- **Differentiation under the integral sign** over the periodicity cell:
`d/dt ∫_cell f(t,x) dx = ∫_cell ∂_t f(t,x) dx`. -/
theorem hasDerivAt_cellInt (f : STime → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) :
    HasDerivAt (fun s => cellInt (fun x => f (s, x)))
      (cellInt (fun x => dvec (1, 0) f (t, x))) t := by
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hdt : Continuous (dvec (1, 0) f) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcont2 : Continuous fun p : ℝ × (Fin 3 → ℝ) => dvec (1, 0) f (p.1, coord p.2) :=
    hdt.comp (continuous_fst.prodMk (coord.continuous.comp continuous_snd))
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := t - 1) (b := t + 1)).prod isCompact_cell
      ).exists_bound_of_continuousOn hcont2.continuousOn
  have hμfin : (volume.restrict cell) Set.univ < ⊤ := by
    simpa [Measure.restrict_apply_univ] using isCompact_cell.measure_lt_top (μ := volume)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict cell) (x₀ := t)
      (F := fun s x => f (s, coord x)) (F' := fun s x => dvec (1, 0) f (s, coord x))
      (bound := fun _ => C) (s := Metric.ball t 1) (Metric.ball_mem_nhds t one_pos)
      (Filter.Eventually.of_forall fun _ =>
        ((hf.continuous.comp (continuous_const.prodMk coord.continuous)).aestronglyMeasurable))
      (((hf.continuous.comp
        (continuous_const.prodMk coord.continuous)).continuousOn).integrableOn_compact
          isCompact_cell)
      ((hdt.comp (continuous_const.prodMk coord.continuous)).aestronglyMeasurable)
      ?_ ?_ ?_
  · exact key.2
  · filter_upwards [ae_restrict_mem measurableSet_cell] with x hx s hs
    have hs' : s ∈ Set.Icc (t - 1) (t + 1) := by
      have h := Metric.mem_ball.mp hs
      rw [Real.dist_eq, abs_lt] at h
      constructor <;> linarith [h.1, h.2]
    exact hC (s, x) ⟨hs', hx⟩
  · exact integrableOn_const (by simpa using hμfin.ne)
  · filter_upwards with x s _ using hasDerivAt_time_slice f hfd s (coord x)

end ClayNS
