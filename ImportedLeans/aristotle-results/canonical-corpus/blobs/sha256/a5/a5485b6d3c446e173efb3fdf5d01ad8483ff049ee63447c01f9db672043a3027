/-
# The positive parabolic energy scale probe

`ParabolicProbeExistence.lean` produces a cut-off parabolic probe whose residual
against the scaling generator is arbitrarily small and whose anchor is the
**signed** dilation mass `m = ∫ ⟪x,U⟫/s^{5/4}`.  Positivity of `m` had to be
*assumed*: the integrand changes sign and can cancel, so `m > 0` does not follow
from the profile being nonzero.

This file removes that hypothesis, using the quadratic probe of
`QuadraticParabolicProbe.lean`.  Its anchor density is

  `q(z)/s(z)^{3/4} = ½|U(z)|² / (‖x‖⁴+t²)^{3/4}`,     (`ClayNS.parEnergyMass`)

which is **nonnegative**, and strictly positive wherever `U` is.  So:

* `ClayNS.parEnergyMass_nonneg` — no cancellation is possible;
* `ClayNS.parEnergyMass_integral_pos` — the total mass is strictly positive as
  soon as `U` is nonzero at a single point away from the spacetime origin;
* `ClayNS.exists_small_residual_quadratic_parabolic_probe` — **the probe**: for
  every `ε > 0` there is a compactly supported `C¹` cut-off `χ`, `0 ≤ χ ≤ 1`,
  with

    `|∫ (χ(s)/s^{3/4})·⟪U,ΛU⟫| ≤ ε`   and   `∫ (χ(s)/s^{3/4})·q ≥ ∫ q/s^{3/4} − ε`.

The mechanism is the same as in the linear case: by
`ClayNS.quadratic_parabolic_cutoff_probe_adjoint` the residual integrand is
exactly `4·(χ'(s)·s)·(q/s^{3/4})` (`ClayNS.quadratic_residual_eq`), and on a
dyadic transition band `|χ'(s)|·s ≤ C` with `C` universal, so the residual
carries **no net power of the parabolic scale** and is controlled by the mass
of the two tails alone.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.QuadraticParabolicProbe
import RequestProject.NavierStokes.ParabolicProbeExistence

open scoped BigOperators
open MeasureTheory Filter Topology Set

noncomputable section

namespace ClayNS

/-! ## The dimensionless parabolic energy density -/

/-- The **dimensionless parabolic energy density** `q(z)/s(z)^{3/4}`, the
density whose integral the quadratic scale probe of `U` measures.  Unlike the
linear dilation mass it is nonnegative. -/
def parEnergyMass (U : STime → E3) (z : STime) : ℝ :=
  parEnergy U z / parScale z ^ ((3 : ℝ) / 4)

lemma parEnergyMass_nonneg (U : STime → E3) (z : STime) : 0 ≤ parEnergyMass U z := by
  refine div_nonneg (parEnergy_nonneg U z) ?_
  exact Real.rpow_nonneg (parScale_nonneg z) _

lemma continuous_rpow_three_quarters : Continuous fun s : ℝ => s ^ ((3 : ℝ) / 4) := by
  rw [continuous_iff_continuousAt]
  intro s
  exact Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))

lemma continuous_parScale_rpow3 : Continuous fun z : STime => parScale z ^ ((3 : ℝ) / 4) :=
  continuous_rpow_three_quarters.comp continuous_parScale

lemma continuous_parEnergy {U : STime → E3} (hU : Continuous U) : Continuous (parEnergy U) :=
  continuous_const.mul (continuous_finset_sum (Finset.univ : Finset (Fin 3)) fun a _ =>
    (((EuclideanSpace.proj (𝕜 := ℝ) a).continuous.comp hU)).pow 2)

lemma measurable_parEnergyMass {U : STime → E3} (hU : Continuous U) :
    Measurable (parEnergyMass U) :=
  (continuous_parEnergy hU).measurable.div continuous_parScale_rpow3.measurable

/-- The quadratic probe, written through the energy mass density. -/
lemma quadProbe_cut (chi : ℝ → ℝ) (U : STime → E3) (z : STime) :
    parWeightOf (parCutProfile3 chi) z * parEnergy U z
      = chi (parScale z) * parEnergyMass U z := by
  have hrp : parScale z ^ (-(3 : ℝ) / 4) = (parScale z ^ ((3 : ℝ) / 4))⁻¹ := by
    rw [show (-(3 : ℝ) / 4) = -((3 : ℝ) / 4) by ring, Real.rpow_neg (parScale_nonneg z)]
  show chi (parScale z) * parScale z ^ (-(3 : ℝ) / 4) * parEnergy U z
      = chi (parScale z) * (parEnergy U z / parScale z ^ ((3 : ℝ) / 4))
  rw [hrp, div_eq_mul_inv]
  ring

/-- **The quadratic residual integrand carries no net power of the parabolic
scale.** -/
lemma quadratic_residual_eq (chi' : ℝ → ℝ) (U : STime → E3) (z : STime) :
    4 * chi' (parScale z) * parScale z ^ ((1 : ℝ) / 4) * parEnergy U z
      = 4 * (chi' (parScale z) * parScale z) * parEnergyMass U z := by
  rcases eq_or_lt_of_le (parScale_nonneg z) with h0 | hpos
  · have h1 : parScale z ^ ((1 : ℝ) / 4) = 0 := by
      rw [← h0, Real.zero_rpow (by norm_num)]
    rw [h1, ← h0]
    ring
  · have hkey : parScale z ^ ((1 : ℝ) / 4)
        = parScale z * (parScale z ^ ((3 : ℝ) / 4))⁻¹ := by
      rw [← Real.rpow_neg (parScale_nonneg z)]
      nth_rewrite 2 [show parScale z = parScale z ^ (1 : ℝ) from (Real.rpow_one _).symm]
      rw [← Real.rpow_add hpos]
      norm_num
    rw [hkey]
    simp only [parEnergyMass, div_eq_mul_inv]
    ring

/-! ## Strict positivity of the anchor -/

lemma parEnergy_pos_of_ne_zero {U : STime → E3} {z : STime} (h : U z ≠ 0) :
    0 < parEnergy U z := by
  rcases lt_or_eq_of_le (parEnergy_nonneg U z) with hlt | heq
  · exact hlt
  · exfalso
    have hsum : ∑ a, (U z a) ^ 2 = 0 := by
      have : (1 / 2 : ℝ) * ∑ a, (U z a) ^ 2 = 0 := heq.symm
      linarith
    have hz : ∀ a : Fin 3, U z a = 0 := by
      intro a
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun b (_ : b ∈ Finset.univ) =>
        sq_nonneg (U z b))).1 hsum a (Finset.mem_univ a)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    exact h (by ext a; simpa using hz a)

lemma parEnergyMass_pos {U : STime → E3} {z : STime} (hz : z ≠ 0) (h : U z ≠ 0) :
    0 < parEnergyMass U z :=
  div_pos (parEnergy_pos_of_ne_zero h)
    (Real.rpow_pos_of_pos (parScale_pos_of_ne hz) _)

/-- **The quadratic anchor is strictly positive.**  If the dimensionless
parabolic energy density is integrable and `U` is nonzero at one spacetime point
away from the origin, then its total mass is `> 0`.  No cancellation can occur:
the density is nonnegative. -/
theorem parEnergyMass_integral_pos {U : STime → E3} (hU : Continuous U)
    (hint : Integrable (parEnergyMass U)) {z0 : STime} (hz0 : z0 ≠ 0) (hUz0 : U z0 ≠ 0) :
    0 < ∫ z : STime, parEnergyMass U z := by
  classical
  have hV : IsOpen {z : STime | z ≠ 0 ∧ U z ≠ 0} := by
    have h1 : IsOpen {z : STime | z ≠ 0} := isOpen_ne
    have h2 : IsOpen {z : STime | U z ≠ 0} := by
      have : {z : STime | U z ≠ 0} = U ⁻¹' {y : E3 | y ≠ 0} := rfl
      rw [this]
      exact isOpen_ne.preimage hU
    exact h1.inter h2
  have hsub : {z : STime | z ≠ 0 ∧ U z ≠ 0} ⊆ Function.support (parEnergyMass U) := by
    rintro z ⟨hz1, hz2⟩
    exact ne_of_gt (parEnergyMass_pos hz1 hz2)
  have hne : ({z : STime | z ≠ 0 ∧ U z ≠ 0}).Nonempty := ⟨z0, hz0, hUz0⟩
  have hpos : 0 < volume (Function.support (parEnergyMass U)) :=
    lt_of_lt_of_le (hV.measure_pos volume hne) (measure_mono hsub)
  exact (integral_pos_iff_support_of_nonneg (parEnergyMass_nonneg U) hint).2 hpos

/-! ## The probe -/

/-- **The positive parabolic energy scale probe.**  Let `U` be a `C¹` spacetime
field whose dimensionless parabolic energy density
`q/s^{3/4} = ½|U|²/(‖x‖⁴+t²)^{3/4}` is integrable.  For every `ε > 0` there is a
compactly supported `C¹` cut-off `χ`, `0 ≤ χ ≤ 1`, in the gauge variable such
that the weight `Φ = χ(s)/s^{3/4}` satisfies

* `|∫ Φ·⟪U, ΛU⟫| ≤ ε` — it is blind to the parabolic scaling direction to
  within `ε`;
* `∫ Φ·½|U|² ≥ ∫ q/s^{3/4} − ε` — it retains essentially all of the profile's
  parabolic **energy**.

Unlike the linear probe, the anchor `∫ q/s^{3/4}` is an integral of a
nonnegative density, so `ClayNS.parEnergyMass_integral_pos` makes it positive
without any extra hypothesis. -/
theorem exists_small_residual_quadratic_parabolic_probe
    {U : STime → E3} (hU : ContDiff ℝ (1 : ℕ) U) (hint : Integrable (parEnergyMass U))
    {eps : ℝ} (heps : 0 < eps) :
    ∃ chi chi' : ℝ → ℝ, ∃ a1 b2 : ℝ, 0 < a1 ∧ a1 < b2 ∧
      (∀ s, HasDerivAt chi (chi' s) s) ∧
      (∀ s, s ≤ a1 ∨ b2 ≤ s → chi s = 0) ∧ (∀ s, 0 ≤ chi s) ∧ (∀ s, chi s ≤ 1) ∧
      |∫ z : STime, parWeightOf (parCutProfile3 chi) z * parEnergyPair U z| ≤ eps ∧
      (∫ z : STime, parEnergyMass U z) - eps
        ≤ ∫ z : STime, parWeightOf (parCutProfile3 chi) z * parEnergy U z := by
  classical
  have hintabs : Integrable (fun z : STime => |parEnergyMass U z|) := hint.abs
  have hmunn : ∀ z : STime, 0 ≤ |parEnergyMass U z| := fun z => abs_nonneg _
  obtain ⟨K, hK0, hK⟩ := exists_smoothTransition_deriv_bound
  set Cc : ℝ := 8 * K with hCc
  have hCc0 : 0 < Cc := by positivity
  have heta : 0 < eps / (Cc + 1) := by positivity
  obtain ⟨n, hn⟩ := exists_par_tail_mass_le hintabs heta
  have hrho0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hrhoR : (1 : ℝ) / ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  obtain ⟨chi, chi', hchi, hchi'c, hchinn, hchi1, hz0, hzb, hone, hz'0, hz'b, hz'mid, hCb⟩ :=
    exists_dyadic_plateau_cutoff (rho := 1 / ((n : ℝ) + 1)) (R := (n : ℝ) + 1) hrho0 hrhoR hK
  have ha1pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) / 2 := by positivity
  have ha1b2 : (1 : ℝ) / ((n : ℝ) + 1) / 2 < 2 * ((n : ℝ) + 1) := by
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    linarith [hrhoR]
  have hchiz : ∀ s, s ≤ 1 / ((n : ℝ) + 1) / 2 ∨ 2 * ((n : ℝ) + 1) ≤ s → chi s = 0 := by
    intro s hs
    rcases hs with hs | hs
    · exact hz0 s hs
    · exact hzb s hs
  -- the adjoint identity
  have hadj := quadratic_parabolic_cutoff_probe_adjoint (chi := chi) (chi' := chi') (U := U)
    hchi hchi'c ha1pos (fun s hs => hz0 s hs) (fun s hs => hz'0 s hs)
    (fun s hs => hzb s hs) hU
  -- the residual integrand, in mass form
  set G : STime → ℝ := fun z => 4 * (chi' (parScale z) * parScale z) * parEnergyMass U z with hG
  have hresform : (fun z : STime =>
      4 * chi' (parScale z) * parScale z ^ ((1 : ℝ) / 4) * parEnergy U z) = G :=
    funext fun z => quadratic_residual_eq chi' U z
  -- pointwise bound on the residual integrand
  have hbound : ∀ z : STime,
      |G z| ≤ Cc * Set.indicator (parTailSet n) (fun w : STime => |parEnergyMass U w|) z := by
    intro z
    have hnn : 0 ≤ Set.indicator (parTailSet n) (fun w : STime => |parEnergyMass U w|) z :=
      Set.indicator_nonneg (fun w _ => hmunn w) z
    by_cases hmid : 1 / ((n : ℝ) + 1) ≤ parScale z ∧ parScale z ≤ (n : ℝ) + 1
    · have : chi' (parScale z) = 0 := hz'mid _ hmid.1 hmid.2
      simp only [hG, this]
      simpa using mul_nonneg hCc0.le hnn
    · have hmem : z ∈ parTailSet n := by
        simp only [parTailSet, Set.mem_union, Set.mem_setOf_eq]
        by_contra hcon
        push_neg at hcon
        exact hmid ⟨le_of_lt hcon.1, le_of_lt hcon.2⟩
      rw [Set.indicator_of_mem hmem]
      have hs0 : 0 ≤ parScale z := parScale_nonneg z
      have habs : |chi' (parScale z) * parScale z| ≤ 2 * K := by
        rw [abs_mul, abs_of_nonneg hs0]
        exact hCb _ hs0
      have hkey : |G z| = 4 * |chi' (parScale z) * parScale z| * |parEnergyMass U z| := by
        simp only [hG, abs_mul]
        norm_num
      rw [hkey, hCc]
      nlinarith [hmunn z, abs_nonneg (chi' (parScale z) * parScale z)]
  -- integrability of the residual
  have hindint : Integrable (fun z : STime =>
      Cc * Set.indicator (parTailSet n) (fun w : STime => |parEnergyMass U w|) z) :=
    (hintabs.indicator (measurableSet_parTailSet n)).const_mul Cc
  have hGmeas : AEStronglyMeasurable G :=
    Measurable.aestronglyMeasurable
      ((measurable_const.mul
        (((hchi'c.comp continuous_parScale).measurable).mul
          continuous_parScale.measurable)).mul (measurable_parEnergyMass hU.continuous))
  have hGint : Integrable G :=
    Integrable.mono' hindint hGmeas (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hbound z)
  have htailint : (∫ z : STime, Set.indicator (parTailSet n)
        (fun w : STime => |parEnergyMass U w|) z)
      = ∫ z in parTailSet n, |parEnergyMass U z| :=
    integral_indicator (measurableSet_parTailSet n)
  have htail_le : (∫ z : STime, Set.indicator (parTailSet n)
      (fun w : STime => |parEnergyMass U w|) z) ≤ eps / (Cc + 1) := by
    rw [htailint]; exact hn
  -- the residual is small
  have hres : |∫ z : STime, G z| ≤ eps := by
    have h1 : |∫ z : STime, G z| ≤ ∫ z : STime, |G z| := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ := (volume : Measure STime)) (f := G)
    have h2 : (∫ z : STime, |G z|)
        ≤ ∫ z : STime, Cc * Set.indicator (parTailSet n)
            (fun w : STime => |parEnergyMass U w|) z :=
      integral_mono hGint.abs hindint hbound
    have h3 : (∫ z : STime, Cc * Set.indicator (parTailSet n)
        (fun w : STime => |parEnergyMass U w|) z)
        = Cc * ∫ z : STime, Set.indicator (parTailSet n)
            (fun w : STime => |parEnergyMass U w|) z := integral_const_mul _ _
    have h4 : Cc * (∫ z : STime, Set.indicator (parTailSet n)
        (fun w : STime => |parEnergyMass U w|) z) ≤ Cc * (eps / (Cc + 1)) :=
      mul_le_mul_of_nonneg_left htail_le hCc0.le
    have h5 : Cc * (eps / (Cc + 1)) ≤ eps := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [heps.le, hCc0.le]
    linarith
  -- the probe of `U` keeps its energy
  have hgmeas : Measurable (fun z : STime =>
      parWeightOf (parCutProfile3 chi) z * parEnergy U z) := by
    have hfun : (fun z : STime => parWeightOf (parCutProfile3 chi) z * parEnergy U z)
        = fun z : STime => chi (parScale z) * parEnergyMass U z :=
      funext fun z => quadProbe_cut chi U z
    rw [hfun]
    have hchic : Continuous chi := continuous_iff_continuousAt.2 fun s => (hchi s).continuousAt
    exact ((hchic.comp continuous_parScale).measurable).mul
      (measurable_parEnergyMass hU.continuous)
  have hdiffbound : ∀ z : STime,
      |parWeightOf (parCutProfile3 chi) z * parEnergy U z - parEnergyMass U z|
        ≤ Set.indicator (parTailSet n) (fun w : STime => |parEnergyMass U w|) z := by
    intro z
    have hval : parWeightOf (parCutProfile3 chi) z * parEnergy U z - parEnergyMass U z
        = (chi (parScale z) - 1) * parEnergyMass U z := by
      rw [quadProbe_cut]
      ring
    rw [hval, abs_mul]
    by_cases hmem : z ∈ parTailSet n
    · rw [Set.indicator_of_mem hmem]
      have h1 : |chi (parScale z) - 1| ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith [hchi1 (parScale z), hchinn (parScale z)],
          by linarith [hchinn (parScale z), hchi1 (parScale z)]⟩
      nlinarith [hmunn z, abs_nonneg (chi (parScale z) - 1)]
    · have hone' : chi (parScale z) = 1 := by
        simp only [parTailSet, Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hmem
        exact hone _ hmem.1.le hmem.2.le
      rw [hone']
      simp only [sub_self, abs_zero, zero_mul]
      exact Set.indicator_nonneg (fun w _ => hmunn w) z
  have hgint : Integrable (fun z : STime =>
      parWeightOf (parCutProfile3 chi) z * parEnergy U z) := by
    refine Integrable.mono' ((hintabs.indicator (measurableSet_parTailSet n)).add hintabs)
      hgmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    have hd := hdiffbound z
    have htri := abs_sub_abs_le_abs_sub
      (parWeightOf (parCutProfile3 chi) z * parEnergy U z) (parEnergyMass U z)
    show |parWeightOf (parCutProfile3 chi) z * parEnergy U z|
        ≤ Set.indicator (parTailSet n) (fun w : STime => |parEnergyMass U w|) z
          + |parEnergyMass U z|
    linarith
  have hcore : (∫ z : STime, parEnergyMass U z) - eps
      ≤ ∫ z : STime, parWeightOf (parCutProfile3 chi) z * parEnergy U z := by
    have hdiff : |(∫ z : STime, parWeightOf (parCutProfile3 chi) z * parEnergy U z)
        - ∫ z : STime, parEnergyMass U z| ≤ eps := by
      rw [← integral_sub hgint hint]
      have h1 : |∫ z : STime, (parWeightOf (parCutProfile3 chi) z * parEnergy U z
            - parEnergyMass U z)|
          ≤ ∫ z : STime, |parWeightOf (parCutProfile3 chi) z * parEnergy U z
            - parEnergyMass U z| := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := (volume : Measure STime))
            (f := fun z : STime => parWeightOf (parCutProfile3 chi) z * parEnergy U z
              - parEnergyMass U z)
      have h2 : (∫ z : STime, |parWeightOf (parCutProfile3 chi) z * parEnergy U z
            - parEnergyMass U z|)
          ≤ ∫ z : STime, Set.indicator (parTailSet n)
              (fun w : STime => |parEnergyMass U w|) z :=
        integral_mono (hgint.sub hint).abs
          (hintabs.indicator (measurableSet_parTailSet n)) hdiffbound
      have h3 : (∫ z : STime, Set.indicator (parTailSet n)
          (fun w : STime => |parEnergyMass U w|) z) ≤ eps := by
        refine htail_le.trans ?_
        rw [div_le_iff₀ (by positivity)]
        nlinarith [heps.le, hCc0.le]
      linarith
    have hab := abs_le.1 hdiff
    linarith [hab.1]
  refine ⟨chi, chi', 1 / ((n : ℝ) + 1) / 2, 2 * ((n : ℝ) + 1), ha1pos, ha1b2, hchi, hchiz,
    hchinn, hchi1, ?_, hcore⟩
  rw [hadj, abs_neg, hresform]
  exact hres

end ClayNS
