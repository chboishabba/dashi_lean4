/-
# The Poincaré inequality on the periodicity cell

This file proves, from scratch, the mean-zero Poincaré (Wirtinger) inequality on
the unit cube `[0,1]³`:

  `∫_cell (f - ⨍ f)² ≤ 3 ∑_i ∫_cell (∂_i f)²`

for every `C¹` scalar field `f` on `ℝ³`.  No periodicity is needed.  The proof
is the classical telescoping-average argument:

* `avgC i g` averages `g` over the `i`-th coordinate on `[0,1]`;
* one-dimensional Cauchy–Schwarz gives `(avgC i g)² ≤ avgC i (g²)`;
* the fundamental theorem of calculus gives `(g - avgC i g)² ≤ avgC i ((∂_i g)²)`
  at every point of the cube;
* averaging in the three coordinates successively produces the mean, and the
  three telescoping differences are estimated by the three partial derivatives.

The inequality is the missing analytic ingredient of the Liouville theorem for
bounded ancient periodic Navier–Stokes solutions
(`RequestProject/NavierStokes/AncientLiouville.lean`): it converts the
enstrophy into a coercive multiple of the (mean-corrected) energy.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.CellVanishing

open scoped BigOperators
open MeasureTheory Set

noncomputable section

namespace ClayNS

/-! ## Averaging one real variable over `[0,1]` -/

/-- The average of `h` over the unit interval (the interval has measure one, so
this is both the integral and the mean). -/
def avg1 (h : ℝ → ℝ) : ℝ := ∫ s in Icc (0:ℝ) 1, h s

lemma integrableOn_unitInterval {h : ℝ → ℝ} (hc : Continuous h) :
    IntegrableOn h (Icc (0:ℝ) 1) :=
  hc.continuousOn.integrableOn_compact isCompact_Icc

lemma measureReal_unitInterval : (volume.restrict (Icc (0:ℝ) 1)).real univ = 1 := by
  simp

@[simp] lemma avg1_const (c : ℝ) : avg1 (fun _ => c) = c := by
  simp [avg1]

lemma avg1_nonneg {h : ℝ → ℝ} (hh : ∀ s, 0 ≤ h s) : 0 ≤ avg1 h :=
  integral_nonneg fun s => hh s

lemma avg1_mono {h k : ℝ → ℝ} (hh : Continuous h) (hk : Continuous k)
    (hle : ∀ s ∈ Icc (0:ℝ) 1, h s ≤ k s) : avg1 h ≤ avg1 k :=
  setIntegral_mono_on (integrableOn_unitInterval hh) (integrableOn_unitInterval hk)
    measurableSet_Icc hle

lemma avg1_sub {h k : ℝ → ℝ} (hh : Continuous h) (hk : Continuous k) :
    avg1 (fun s => h s - k s) = avg1 h - avg1 k :=
  integral_sub (integrableOn_unitInterval hh) (integrableOn_unitInterval hk)

lemma abs_avg1_le {h : ℝ → ℝ} : |avg1 h| ≤ avg1 (fun s => |h s|) :=
  abs_integral_le_integral_abs

/-- **Cauchy–Schwarz on the unit interval**: the square of an average is at most
the average of the square. -/
lemma avg1_sq_le {h : ℝ → ℝ} (hc : Continuous h) : (avg1 h)^2 ≤ avg1 (fun s => (h s)^2) := by
  set c := avg1 h with hcdef
  have hint : IntegrableOn h (Icc (0:ℝ) 1) := integrableOn_unitInterval hc
  have hint2 : IntegrableOn (fun s => (h s)^2) (Icc (0:ℝ) 1) :=
    integrableOn_unitInterval (hc.pow 2)
  have hintc : IntegrableOn (fun _ : ℝ => c^2) (Icc (0:ℝ) 1) :=
    integrableOn_unitInterval continuous_const
  have hnn : 0 ≤ ∫ s in Icc (0:ℝ) 1, (h s - c)^2 := integral_nonneg fun s => sq_nonneg _
  have hadd : ∫ s in Icc (0:ℝ) 1, (((h s)^2 - 2*c*h s) + c^2)
      = (∫ s in Icc (0:ℝ) 1, ((h s)^2 - 2*c*h s)) + ∫ _s in Icc (0:ℝ) 1, c^2 :=
    integral_add (hint2.sub (hint.const_mul (2*c))) hintc
  have hsub : ∫ s in Icc (0:ℝ) 1, ((h s)^2 - 2*c*h s)
      = (∫ s in Icc (0:ℝ) 1, (h s)^2) - ∫ s in Icc (0:ℝ) 1, 2*c*h s :=
    integral_sub hint2 (hint.const_mul (2*c))
  have e1 : ∫ s in Icc (0:ℝ) 1, (h s - c)^2
      = ∫ s in Icc (0:ℝ) 1, (((h s)^2 - 2*c*h s) + c^2) := by
    apply integral_congr_ae; filter_upwards with s; ring
  rw [e1, hadd, hsub, integral_const_mul, integral_const, measureReal_unitInterval] at hnn
  simp only [smul_eq_mul, one_mul] at hnn
  have hc2 : (∫ a in Icc (0:ℝ) 1, h a) = c := hcdef.symm
  rw [hc2] at hnn
  simp only [avg1]
  nlinarith [hnn]

/-! ## Averaging one coordinate of the unit cube -/

/-- The cube integral, i.e. the cell integral written in coordinates. -/
def cubeInt (g : (Fin 3 → ℝ) → ℝ) : ℝ := ∫ x in cell, g x

lemma cellInt_eq_cubeInt (f : E3 → ℝ) : cellInt f = cubeInt (fun x => f (coord x)) := rfl

/-- The average of `g` over the `i`-th coordinate, the others being frozen. -/
def avgC (i : Fin 3) (g : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  avg1 (fun s => g (Function.update x i s))

/-- The `i`-th partial derivative in cube coordinates. -/
def parD (i : Fin 3) (g : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  fderiv ℝ g x (Pi.single i 1)

lemma continuous_update (i : Fin 3) :
    Continuous fun p : (Fin 3 → ℝ) × ℝ => Function.update p.1 i p.2 := by
  refine continuous_pi fun j => ?_
  by_cases h : j = i
  · subst h; simpa using continuous_snd
  · simpa [Function.update_of_ne h] using (continuous_apply j).comp continuous_fst

lemma continuous_avgC {g : (Fin 3 → ℝ) → ℝ} (hg : Continuous g) (i : Fin 3) :
    Continuous (avgC i g) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hcomp : Continuous fun p : (Fin 3 → ℝ) × ℝ => g (Function.update p.1 i p.2) :=
    hg.comp (continuous_update i)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x₀ 1).prod (isCompact_Icc (a := (0:ℝ)) (b := 1))
      ).exists_bound_of_continuousOn hcomp.continuousOn
  have hμfin : (volume.restrict (Icc (0:ℝ) 1)) univ < ⊤ := by
    simp
  refine MeasureTheory.continuousAt_of_dominated (bound := fun _ => C)
    (Filter.Eventually.of_forall fun x =>
      (hg.comp ((continuous_update i).comp (continuous_const.prodMk continuous_id))
        ).aestronglyMeasurable)
    ?_ (integrableOn_const (by simp)) ?_
  · filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hC (x, s) ⟨Metric.ball_subset_closedBall hx, hs⟩
  · filter_upwards with s
    exact (hg.comp ((continuous_update i).comp (continuous_id.prodMk continuous_const))).continuousAt

/-- Averaging in the `i`-th coordinate produces a field independent of that
coordinate. -/
lemma avgC_update_self (i : Fin 3) (g : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) (r : ℝ) :
    avgC i g (Function.update x i r) = avgC i g x := by
  simp [avgC, Function.update_idem]

/-- `Indep i g` records that `g` does not depend on its `i`-th coordinate. -/
def Indep (i : Fin 3) (g : (Fin 3 → ℝ) → ℝ) : Prop :=
  ∀ (x : Fin 3 → ℝ) (r : ℝ), g (Function.update x i r) = g x

lemma indep_avgC (i : Fin 3) (g : (Fin 3 → ℝ) → ℝ) : Indep i (avgC i g) :=
  fun x r => avgC_update_self i g x r

lemma Indep.avgC {i j : Fin 3} {g : (Fin 3 → ℝ) → ℝ} (h : Indep i g) (hij : j ≠ i) :
    Indep i (avgC j g) := by
  intro x r
  simp only [_root_.ClayNS.avgC]
  congr 1
  funext s
  rw [show Function.update (Function.update x i r) j s
        = Function.update (Function.update x j s) i r from
      (Function.update_comm hij s r x).symm, h]

/-- A field independent of all three coordinates is constant. -/
lemma const_of_indep_all {g : (Fin 3 → ℝ) → ℝ} (h0 : Indep 0 g) (h1 : Indep 1 g)
    (h2 : Indep 2 g) (x y : Fin 3 → ℝ) : g x = g y := by
  have e : Function.update (Function.update (Function.update x 0 (y 0)) 1 (y 1)) 2 (y 2) = y := by
    funext j
    fin_cases j <;> simp
  calc g x = g (Function.update x 0 (y 0)) := (h0 x (y 0)).symm
    _ = g (Function.update (Function.update x 0 (y 0)) 1 (y 1)) := (h1 _ (y 1)).symm
    _ = g (Function.update (Function.update (Function.update x 0 (y 0)) 1 (y 1)) 2 (y 2)) :=
        (h2 _ (y 2)).symm
    _ = g y := by rw [e]

lemma avgC_comm {i j : Fin 3} (hij : i ≠ j) (g : (Fin 3 → ℝ) → ℝ) (hg : Continuous g) :
    avgC i (avgC j g) = avgC j (avgC i g) := by
  funext x
  simp only [avgC, avg1]
  have hcont : Continuous fun p : ℝ × ℝ => g (Function.update (Function.update x i p.1) j p.2) := by
    refine hg.comp ?_
    exact (continuous_update j).comp
      (((continuous_update i).comp (continuous_const.prodMk continuous_fst)).prodMk continuous_snd)
  have hint : Integrable (Function.uncurry
      (fun s t => g (Function.update (Function.update x i s) j t)))
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict (Icc (0:ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [MeasureTheory.integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun s _ => ?_
  rw [Function.update_comm hij s t x]

lemma avgC_sub {i : Fin 3} {g h : (Fin 3 → ℝ) → ℝ} (hg : Continuous g) (hh : Continuous h)
    (x : Fin 3 → ℝ) :
    avgC i (fun y => g y - h y) x = avgC i g x - avgC i h x :=
  avg1_sub (hg.comp ((continuous_update i).comp (continuous_const.prodMk continuous_id)))
    (hh.comp ((continuous_update i).comp (continuous_const.prodMk continuous_id)))

lemma avgC_mono {i : Fin 3} {g h : (Fin 3 → ℝ) → ℝ} (hg : Continuous g) (hh : Continuous h)
    (hle : ∀ y, g y ≤ h y) (x : Fin 3 → ℝ) : avgC i g x ≤ avgC i h x :=
  avg1_mono (hg.comp ((continuous_update i).comp (continuous_const.prodMk continuous_id)))
    (hh.comp ((continuous_update i).comp (continuous_const.prodMk continuous_id)))
    (fun _ _ => hle _)

lemma avgC_sq_le {i : Fin 3} {g : (Fin 3 → ℝ) → ℝ} (hg : Continuous g) (x : Fin 3 → ℝ) :
    (avgC i g x)^2 ≤ avgC i (fun y => (g y)^2) x :=
  avg1_sq_le (hg.comp ((continuous_update i).comp (continuous_const.prodMk continuous_id)))

/-! ## Fubini for the cube -/

/-- Slicing the unit cube along the `i`-th coordinate. -/
theorem cubeInt_slice (i : Fin 3) (g : (Fin 3 → ℝ) → ℝ) (hg : Continuous g) :
    cubeInt g = ∫ a in Icc (0:ℝ) 1, ∫ y in Icc (0 : Fin 2 → ℝ) 1, g (i.insertNth a y) := by
  have hmp := (MeasureTheory.measurePreserving_piFinSuccAbove
      (fun _ : Fin 3 => (volume : Measure ℝ)) i).symm
  have hemb : MeasurableEmbedding
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i).symm) :=
    (MeasurableEquiv.measurableEmbedding _)
  have key := hmp.setIntegral_preimage_emb hemb g (Icc (0 : Fin 3 → ℝ) 1)
  have happ : ∀ p : ℝ × (Fin 2 → ℝ),
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i).symm) p = i.insertNth p.1 p.2 := by
    intro p
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have hcons : Continuous fun p : ℝ × (Fin 2 → ℝ) => i.insertNth p.1 p.2 (α := fun _ => ℝ) :=
    Continuous.finInsertNth i continuous_fst continuous_snd
  have hpre : ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i).symm) ⁻¹' (Icc 0 1)
      = (Icc (0:ℝ) 1) ×ˢ (Icc (0 : Fin 2 → ℝ) 1) := by
    ext p
    simp only [Set.mem_preimage, happ, Set.mem_prod, ← Set.pi_univ_Icc, Set.mem_univ_pi]
    constructor
    · intro h
      refine ⟨?_, fun j => ?_⟩
      · have := h i; simpa using this
      · have := h (i.succAbove j); simpa using this
    · rintro ⟨h0, hj⟩ k
      refine Fin.succAboveCases i ?_ ?_ k
      · simpa using h0
      · intro j; simpa using hj j
  rw [hpre] at key
  simp only [happ] at key
  simp only [cubeInt, cell, volume_pi] at *
  rw [← key, MeasureTheory.setIntegral_prod]
  exact ((hg.comp hcons).continuousOn).integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

lemma update_insertNth_self (i : Fin 3) (a s : ℝ) (y : Fin 2 → ℝ) :
    Function.update (i.insertNth a y : Fin 3 → ℝ) i s = i.insertNth s y := by
  funext k
  refine Fin.succAboveCases i ?_ ?_ k
  · simp
  · intro j
    have h : i.succAbove j ≠ i := Fin.succAbove_ne i j
    simp

/-- Averaging over a coordinate does not change the integral over the cube. -/
theorem cubeInt_avgC (i : Fin 3) (g : (Fin 3 → ℝ) → ℝ) (hg : Continuous g) :
    cubeInt (avgC i g) = cubeInt g := by
  have hcontA : Continuous (avgC i g) := continuous_avgC hg i
  rw [cubeInt_slice i _ hcontA, cubeInt_slice i g hg]
  have hval : ∀ (a : ℝ) (y : Fin 2 → ℝ),
      avgC i g (i.insertNth a y) = ∫ s in Icc (0:ℝ) 1, g (i.insertNth s y) := by
    intro a y
    simp only [avgC, avg1, update_insertNth_self]
  have step1 : (∫ a in Icc (0:ℝ) 1, ∫ y in Icc (0 : Fin 2 → ℝ) 1, avgC i g (i.insertNth a y))
      = ∫ _a in Icc (0:ℝ) 1,
          (∫ y in Icc (0 : Fin 2 → ℝ) 1, ∫ s in Icc (0:ℝ) 1, g (i.insertNth s y)) := by
    refine setIntegral_congr_fun measurableSet_Icc fun a _ => ?_
    refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    exact hval a y
  rw [step1]
  rw [show (∫ _a in Icc (0:ℝ) 1,
        (∫ y in Icc (0 : Fin 2 → ℝ) 1, ∫ s in Icc (0:ℝ) 1, g (i.insertNth s y)))
      = avg1 (fun _ => ∫ y in Icc (0 : Fin 2 → ℝ) 1, ∫ s in Icc (0:ℝ) 1,
          g (i.insertNth s y)) from rfl, avg1_const]
  have hcons : Continuous fun p : ℝ × (Fin 2 → ℝ) => i.insertNth p.1 p.2 (α := fun _ => ℝ) :=
    Continuous.finInsertNth i continuous_fst continuous_snd
  have hswapint : Integrable (Function.uncurry (fun (y : Fin 2 → ℝ) (s : ℝ) =>
      g (i.insertNth s y)))
      ((volume.restrict (Icc (0 : Fin 2 → ℝ) 1)).prod (volume.restrict (Icc (0:ℝ) 1))) := by
    rw [Measure.prod_restrict]
    have hc : Continuous fun p : (Fin 2 → ℝ) × ℝ => g (i.insertNth p.2 p.1) :=
      hg.comp (hcons.comp (continuous_snd.prodMk continuous_fst))
    exact hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  exact MeasureTheory.integral_integral_swap hswapint

/-! ## The one-dimensional Poincaré step -/

/-- The one-dimensional slice of `g` in the `i`-th coordinate is differentiable
with derivative the `i`-th partial derivative. -/
lemma hasDerivAt_slice_coord (i : Fin 3) (g : (Fin 3 → ℝ) → ℝ) (hg : ContDiff ℝ 1 g)
    (x : Fin 3 → ℝ) (r : ℝ) :
    HasDerivAt (fun s => g (Function.update x i s)) (parD i g (Function.update x i r)) r := by
  have hL : HasDerivAt (fun s : ℝ => Function.update x i s) (Pi.single i (1:ℝ) : Fin 3 → ℝ) r := by
    have he : (fun s : ℝ => Function.update x i s)
        = fun s : ℝ => x + (s - x i) • (Pi.single i (1:ℝ) : Fin 3 → ℝ) := by
      funext s j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [he]
    simpa using
      (((hasDerivAt_id r).sub_const (x i)).smul_const (Pi.single i (1:ℝ) : Fin 3 → ℝ)).const_add x
  exact (hg.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt r hL

lemma continuous_parD {g : (Fin 3 → ℝ) → ℝ} (hg : ContDiff ℝ 1 g) (i : Fin 3) :
    Continuous (parD i g) :=
  (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- The mean-value bound along a coordinate line inside the cube. -/
lemma abs_sub_le_avg1_abs_parD (i : Fin 3) (g : (Fin 3 → ℝ) → ℝ) (hg : ContDiff ℝ 1 g)
    (x : Fin 3 → ℝ) (u v : ℝ) (hu : u ∈ Icc (0:ℝ) 1) (hv : v ∈ Icc (0:ℝ) 1) :
    |g (Function.update x i u) - g (Function.update x i v)|
      ≤ avg1 (fun r => |parD i g (Function.update x i r)|) := by
  set G : ℝ → ℝ := fun s => g (Function.update x i s) with hGdef
  set F : ℝ → ℝ := fun s => parD i g (Function.update x i s) with hFdef
  have hcontF : Continuous F :=
    (continuous_parD hg i).comp
      ((continuous_update i).comp (continuous_const.prodMk continuous_id))
  have hd : ∀ r, HasDerivAt G (F r) r := fun r => hasDerivAt_slice_coord i g hg x r
  have habs : IntegrableOn (fun r => |F r|) (Icc (0:ℝ) 1) :=
    (hcontF.abs).continuousOn.integrableOn_compact isCompact_Icc
  have key : ∀ a b : ℝ, a ≤ b → a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      |G b - G a| ≤ avg1 (fun r => |F r|) := by
    intro a b hab ha hb
    have hint : G b - G a = ∫ r in a..b, F r :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
        (hcontF.intervalIntegrable a b)).symm
    rw [hint, intervalIntegral.integral_of_le hab]
    calc |∫ r in Ioc a b, F r| ≤ ∫ r in Ioc a b, |F r| := abs_integral_le_integral_abs
      _ ≤ avg1 (fun r => |F r|) := by
          refine setIntegral_mono_set habs (Filter.Eventually.of_forall fun r => abs_nonneg _) ?_
          exact HasSubset.Subset.eventuallyLE
            (fun r hr => ⟨le_trans ha.1 (le_of_lt hr.1), le_trans hr.2 hb.2⟩)
  rcases le_total v u with h | h
  · exact key v u h hv hu
  · rw [abs_sub_comm]; exact key u v h hu hv

/-- At every point of the cube, the deviation of `g` from its `i`-average is
controlled by the average of the squared `i`-th partial derivative. -/
theorem sq_sub_avgC_le (i : Fin 3) (g : (Fin 3 → ℝ) → ℝ) (hg : ContDiff ℝ 1 g)
    (x : Fin 3 → ℝ) (hx : x ∈ cell) :
    (g x - avgC i g x)^2 ≤ avgC i (fun y => (parD i g y)^2) x := by
  have hcontg : Continuous g := hg.continuous
  have hcontF : Continuous (fun s => parD i g (Function.update x i s)) :=
    (continuous_parD hg i).comp
      ((continuous_update i).comp (continuous_const.prodMk continuous_id))
  have hcontG : Continuous (fun s => g (Function.update x i s)) :=
    hcontg.comp ((continuous_update i).comp (continuous_const.prodMk continuous_id))
  have hxi : x i ∈ Icc (0:ℝ) 1 := ⟨hx.1 i, hx.2 i⟩
  have hxupd : Function.update x i (x i) = x := Function.update_eq_self i x
  have hbound : ∀ s ∈ Icc (0:ℝ) 1, |g x - g (Function.update x i s)|
      ≤ avg1 (fun r => |parD i g (Function.update x i r)|) := by
    intro s hs
    have := abs_sub_le_avg1_abs_parD i g hg x (x i) s hxi hs
    rwa [hxupd] at this
  have hsplit : g x - avgC i g x = avg1 (fun s => g x - g (Function.update x i s)) := by
    rw [avg1_sub continuous_const hcontG, avg1_const]
    rfl
  have h1 : |g x - avgC i g x| ≤ avg1 (fun r => |parD i g (Function.update x i r)|) := by
    rw [hsplit]
    calc |avg1 (fun s => g x - g (Function.update x i s))|
        ≤ avg1 (fun s => |g x - g (Function.update x i s)|) := abs_avg1_le
      _ ≤ avg1 (fun _ => avg1 (fun r => |parD i g (Function.update x i r)|)) :=
          avg1_mono ((continuous_const.sub hcontG).abs) continuous_const hbound
      _ = avg1 (fun r => |parD i g (Function.update x i r)|) := avg1_const _
  have h2 : (avg1 (fun r => |parD i g (Function.update x i r)|))^2
      ≤ avg1 (fun r => (parD i g (Function.update x i r))^2) := by
    simpa [sq_abs] using avg1_sq_le hcontF.abs
  have h3 : (g x - avgC i g x)^2 ≤ (avg1 (fun r => |parD i g (Function.update x i r)|))^2 := by
    rw [← sq_abs (g x - avgC i g x)]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  exact le_trans h3 h2

/-! ## Elementary properties of the cube integral -/

lemma integrableOn_cube {g : (Fin 3 → ℝ) → ℝ} (hg : Continuous g) : IntegrableOn g cell :=
  hg.continuousOn.integrableOn_compact isCompact_cell

@[simp] lemma cubeInt_const (c : ℝ) : cubeInt (fun _ => c) = c := by
  rw [cubeInt, integral_const]
  simp [measureReal_def, cell, Real.volume_Icc_pi]

lemma cubeInt_mono {g h : (Fin 3 → ℝ) → ℝ} (hg : Continuous g) (hh : Continuous h)
    (hle : ∀ x ∈ cell, g x ≤ h x) : cubeInt g ≤ cubeInt h :=
  setIntegral_mono_on (integrableOn_cube hg) (integrableOn_cube hh) measurableSet_cell hle

lemma cubeInt_add {g h : (Fin 3 → ℝ) → ℝ} (hg : Continuous g) (hh : Continuous h) :
    cubeInt (fun x => g x + h x) = cubeInt g + cubeInt h :=
  integral_add (integrableOn_cube hg) (integrableOn_cube hh)

lemma cubeInt_const_mul (c : ℝ) (g : (Fin 3 → ℝ) → ℝ) :
    cubeInt (fun x => c * g x) = c * cubeInt g :=
  integral_const_mul c g

/-! ## The Poincaré inequality -/

theorem cubeInt_sq_sub_avgC_le (i : Fin 3) (g : (Fin 3 → ℝ) → ℝ) (hg : ContDiff ℝ 1 g) :
    cubeInt (fun x => (g x - avgC i g x)^2) ≤ cubeInt (fun x => (parD i g x)^2) := by
  have hc : Continuous g := hg.continuous
  have hD : Continuous (fun x => (parD i g x)^2) := (continuous_parD hg i).pow 2
  have h1 : cubeInt (fun x => (g x - avgC i g x)^2)
      ≤ cubeInt (avgC i (fun y => (parD i g y)^2)) :=
    cubeInt_mono ((hc.sub (continuous_avgC hc i)).pow 2) (continuous_avgC hD i)
      (fun x hx => sq_sub_avgC_le i g hg x hx)
  rwa [cubeInt_avgC i _ hD] at h1

/-- The square of a sum of three reals is at most three times the sum of the
squares. -/
lemma sq_add_three_le (a b c : ℝ) : (a + b + c)^2 ≤ 3 * (a^2 + b^2 + c^2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

theorem cubeInt_poincare (g : (Fin 3 → ℝ) → ℝ) (hg : ContDiff ℝ 1 g) :
    cubeInt (fun x => (g x - cubeInt g)^2) ≤ 3 * ∑ i, cubeInt (fun x => (parD i g x)^2) := by
  have hc : Continuous g := hg.continuous
  set A0 : (Fin 3 → ℝ) → ℝ := avgC 0 g with hA0def
  set A1 : (Fin 3 → ℝ) → ℝ := avgC 1 A0 with hA1def
  set A2 : (Fin 3 → ℝ) → ℝ := avgC 2 A1 with hA2def
  have hcA0 : Continuous A0 := continuous_avgC hc 0
  have hcA1 : Continuous A1 := continuous_avgC hcA0 1
  have hcA2 : Continuous A2 := continuous_avgC hcA1 2
  -- `A2` is a constant, equal to the mean of `g`
  have hi0 : Indep 0 A2 :=
    ((indep_avgC 0 g).avgC (by decide)).avgC (by decide)
  have hi1 : Indep 1 A2 := (indep_avgC 1 A0).avgC (by decide)
  have hi2 : Indep 2 A2 := indep_avgC 2 A1
  have hA2const : ∀ x y, A2 x = A2 y := const_of_indep_all hi0 hi1 hi2
  have hmean : ∀ x, A2 x = cubeInt g := by
    intro x
    have h1 : cubeInt A2 = cubeInt g := by
      rw [hA2def, cubeInt_avgC 2 A1 hcA1, hA1def, cubeInt_avgC 1 A0 hcA0, hA0def,
        cubeInt_avgC 0 g hc]
    have h2 : cubeInt A2 = A2 x := by
      rw [show A2 = fun _ => A2 x from funext fun y => hA2const y x, cubeInt_const]
    rw [← h2, h1]
  -- pointwise telescoping bound
  have hpt : ∀ x ∈ cell, (g x - cubeInt g)^2
      ≤ 3 * ((g x - A0 x)^2 + (A0 x - A1 x)^2 + (A1 x - A2 x)^2) := by
    intro x _
    have hx : g x - cubeInt g = (g x - A0 x) + (A0 x - A1 x) + (A1 x - A2 x) := by
      rw [hmean x]; ring
    rw [hx]
    exact sq_add_three_le _ _ _
  have hsplit : cubeInt (fun x => (g x - cubeInt g)^2)
      ≤ 3 * (cubeInt (fun x => (g x - A0 x)^2) + cubeInt (fun x => (A0 x - A1 x)^2)
          + cubeInt (fun x => (A1 x - A2 x)^2)) := by
    have hmono := cubeInt_mono ((hc.sub continuous_const).pow 2)
      (continuous_const.mul ((((hc.sub hcA0).pow 2).add ((hcA0.sub hcA1).pow 2)).add
        ((hcA1.sub hcA2).pow 2))) hpt
    calc cubeInt (fun x => (g x - cubeInt g)^2)
        ≤ cubeInt (fun x => 3 * ((g x - A0 x)^2 + (A0 x - A1 x)^2 + (A1 x - A2 x)^2)) := hmono
      _ = 3 * cubeInt (fun x => ((g x - A0 x)^2 + (A0 x - A1 x)^2) + (A1 x - A2 x)^2) :=
          cubeInt_const_mul _ _
      _ = 3 * (cubeInt (fun x => (g x - A0 x)^2) + cubeInt (fun x => (A0 x - A1 x)^2)
          + cubeInt (fun x => (A1 x - A2 x)^2)) := by
          have hadd1 : cubeInt (fun x => ((g x - A0 x)^2 + (A0 x - A1 x)^2) + (A1 x - A2 x)^2)
              = cubeInt (fun x => (g x - A0 x)^2 + (A0 x - A1 x)^2)
                + cubeInt (fun x => (A1 x - A2 x)^2) :=
            cubeInt_add (((hc.sub hcA0).pow 2).add ((hcA0.sub hcA1).pow 2))
              ((hcA1.sub hcA2).pow 2)
          have hadd2 : cubeInt (fun x => (g x - A0 x)^2 + (A0 x - A1 x)^2)
              = cubeInt (fun x => (g x - A0 x)^2) + cubeInt (fun x => (A0 x - A1 x)^2) :=
            cubeInt_add ((hc.sub hcA0).pow 2) ((hcA0.sub hcA1).pow 2)
          rw [hadd1, hadd2]
  -- the three telescoping terms
  have hT0 : cubeInt (fun x => (g x - A0 x)^2) ≤ cubeInt (fun x => (parD 0 g x)^2) :=
    cubeInt_sq_sub_avgC_le 0 g hg
  have hT1 : cubeInt (fun x => (A0 x - A1 x)^2) ≤ cubeInt (fun x => (parD 1 g x)^2) := by
    have hcomm : A1 = avgC 0 (avgC 1 g) := by
      rw [hA1def, hA0def, avgC_comm (by decide : (1 : Fin 3) ≠ 0) g hc]
    have hstep : ∀ x, A0 x - A1 x = avgC 0 (fun y => g y - avgC 1 g y) x := by
      intro x
      rw [avgC_sub hc (continuous_avgC hc 1) x, hA0def, hcomm]
    have hsq : ∀ x, (A0 x - A1 x)^2 ≤ avgC 0 (fun y => (g y - avgC 1 g y)^2) x := by
      intro x
      rw [hstep x]
      exact avgC_sq_le (hc.sub (continuous_avgC hc 1)) x
    calc cubeInt (fun x => (A0 x - A1 x)^2)
        ≤ cubeInt (avgC 0 (fun y => (g y - avgC 1 g y)^2)) :=
          cubeInt_mono ((hcA0.sub hcA1).pow 2)
            (continuous_avgC ((hc.sub (continuous_avgC hc 1)).pow 2) 0) (fun x _ => hsq x)
      _ = cubeInt (fun y => (g y - avgC 1 g y)^2) :=
          cubeInt_avgC 0 _ ((hc.sub (continuous_avgC hc 1)).pow 2)
      _ ≤ cubeInt (fun x => (parD 1 g x)^2) := cubeInt_sq_sub_avgC_le 1 g hg
  have hT2 : cubeInt (fun x => (A1 x - A2 x)^2) ≤ cubeInt (fun x => (parD 2 g x)^2) := by
    have hk : Continuous (fun y => g y - avgC 2 g y) := hc.sub (continuous_avgC hc 2)
    have hcomm : A2 = avgC 1 (avgC 0 (avgC 2 g)) := by
      rw [hA2def, hA1def, hA0def, avgC_comm (by decide : (2 : Fin 3) ≠ 1) (avgC 0 g)
        (continuous_avgC hc 0), avgC_comm (by decide : (2 : Fin 3) ≠ 0) g hc]
    have hstep : ∀ x, A1 x - A2 x = avgC 1 (avgC 0 (fun y => g y - avgC 2 g y)) x := by
      intro x
      have hfun : avgC 0 (fun y => g y - avgC 2 g y)
          = fun y => A0 y - avgC 0 (avgC 2 g) y := by
        funext y
        exact avgC_sub hc (continuous_avgC hc 2) y
      symm
      rw [hfun, avgC_sub hcA0 (continuous_avgC (continuous_avgC hc 2) 0) x, ← hA1def, ← hcomm]
    have hsq : ∀ x, (A1 x - A2 x)^2
        ≤ avgC 1 (avgC 0 (fun y => (g y - avgC 2 g y)^2)) x := by
      intro x
      rw [hstep x]
      calc (avgC 1 (avgC 0 (fun y => g y - avgC 2 g y)) x)^2
          ≤ avgC 1 (fun z => (avgC 0 (fun y => g y - avgC 2 g y) z)^2) x :=
            avgC_sq_le (continuous_avgC hk 0) x
        _ ≤ avgC 1 (avgC 0 (fun y => (g y - avgC 2 g y)^2)) x := by
            refine avgC_mono ((continuous_avgC hk 0).pow 2)
              (continuous_avgC (hk.pow 2) 0) (fun z => ?_) x
            exact avgC_sq_le hk z
    calc cubeInt (fun x => (A1 x - A2 x)^2)
        ≤ cubeInt (avgC 1 (avgC 0 (fun y => (g y - avgC 2 g y)^2))) :=
          cubeInt_mono ((hcA1.sub hcA2).pow 2)
            (continuous_avgC (continuous_avgC (hk.pow 2) 0) 1) (fun x _ => hsq x)
      _ = cubeInt (avgC 0 (fun y => (g y - avgC 2 g y)^2)) :=
          cubeInt_avgC 1 _ (continuous_avgC (hk.pow 2) 0)
      _ = cubeInt (fun y => (g y - avgC 2 g y)^2) := cubeInt_avgC 0 _ (hk.pow 2)
      _ ≤ cubeInt (fun x => (parD 2 g x)^2) := cubeInt_sq_sub_avgC_le 2 g hg
  have hsum : ∑ i, cubeInt (fun x => (parD i g x)^2)
      = cubeInt (fun x => (parD 0 g x)^2) + cubeInt (fun x => (parD 1 g x)^2)
        + cubeInt (fun x => (parD 2 g x)^2) := by
    rw [Fin.sum_univ_three]
  rw [hsum]
  linarith [hsplit, hT0, hT1, hT2]

/-- **The Poincaré inequality on the periodicity cell.** -/
theorem cellInt_poincare (f : E3 → ℝ) (hf : ContDiff ℝ 1 f) :
    cellInt (fun x => (f x - cellInt f)^2)
      ≤ 3 * ∑ i, cellInt (fun x => (fderiv ℝ f x (ee i))^2) := by
  have hg : ContDiff ℝ 1 (fun x : Fin 3 → ℝ => f (coord x)) :=
    hf.comp (coord : (Fin 3 → ℝ) ≃L[ℝ] E3).contDiff
  have hparD : ∀ (i : Fin 3) (x : Fin 3 → ℝ),
      parD i (fun y : Fin 3 → ℝ => f (coord y)) x = fderiv ℝ f (coord x) (ee i) := by
    intro i x
    have hcomp : HasFDerivAt (fun y : Fin 3 → ℝ => f (coord y))
        ((fderiv ℝ f (coord x)).comp (coord : (Fin 3 → ℝ) →L[ℝ] E3)) x :=
      ((hf.differentiable (by norm_num)) (coord x)).hasFDerivAt.comp x
        (coord : (Fin 3 → ℝ) ≃L[ℝ] E3).hasFDerivAt
    rw [parD, hcomp.fderiv]
    simp
  have key := cubeInt_poincare (fun x => f (coord x)) hg
  simp only [hparD] at key
  exact key

end ClayNS
