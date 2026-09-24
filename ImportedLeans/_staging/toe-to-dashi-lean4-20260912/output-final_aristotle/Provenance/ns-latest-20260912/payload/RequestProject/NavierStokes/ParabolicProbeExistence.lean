/-
# Existence of a separating parabolic scale probe for an arbitrary spacetime field

`ParabolicCutoffProbe.lean` proves, for every `C¹` spacetime field `U` — not
assumed radial, not assumed self-similar, not assumed time-independent — and
every `C¹` cut-off `χ` in the parabolic gauge `s = ‖x‖⁴ + t²`,

  `∫ (χ(s)/s^{5/4})·⟪x, ΛU⟫ = − ∫ 4χ'(s)·s^{-1/4}·⟪x, U⟫`,

with `Λ` the parabolic scaling generator `ClayNS.scaleGen` based at the
spacetime origin.  This file discharges the remaining step: *choosing* the
cut-off so that the residual is as small as one likes while the probe of `U`
itself keeps essentially all of its mass.

The mechanism is the parabolic scaling dimension of the residual.  Write

  `m(z) = ⟪x, U z⟫ / s(z)^{5/4}`                            (`ClayNS.parMass`)

for the dimensionless mass density of the probe — the density whose integral the
probe of `U` is.  The residual integrand is exactly `4·(χ'(s)·s)·m(z)`
(`ClayNS.parabolic_residual_eq`), and on a dyadic transition band `[a,2a]` of the
gauge the cut-off derivative obeys `|χ'(s)|·s ≤ C` with `C` universal: the
residual carries **no net power of the parabolic scale**.  Hence, whenever `m`
is integrable, putting both transitions in the tails `{s ≤ ρ}`, `{s ≥ R}` — whose
mass tends to `0` — makes the residual arbitrarily small, while the plateau
covers all but that same vanishing mass.

* `ClayNS.parTailSet`, `ClayNS.exists_par_tail_mass_le` — the tail regions in the
  parabolic gauge and the vanishing of their mass;
* `ClayNS.exists_small_residual_parabolic_probe` — **the theorem**: for every
  tolerance `ε > 0` there is a compactly supported cut-off `χ` with

    `|∫ (χ(s)/s^{5/4})·⟪x, ΛU⟫| ≤ ε`  and  `∫ (χ(s)/s^{5/4})·⟪x,U⟫ ≥ ∫ m − ε`.

  This is the pair `(δ, a₀)` required by
  `ClayNS.gram_anchor_lower_bound_approx`, now for the genuine parabolic
  generator acting on a genuine spacetime field.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.ParabolicCutoffProbe
import RequestProject.NavierStokes.DilationProbeExistence

open scoped BigOperators
open MeasureTheory Filter Topology Set

noncomputable section

namespace ClayNS

/-! ## The dimensionless mass density -/

/-- The **dimensionless parabolic mass density** `m(z) = ⟪x, U z⟫ / s(z)^{5/4}`,
the density whose integral the scale probe of `U` measures. -/
def parMass (U : STime → E3) (z : STime) : ℝ := parRadPair U z / parScale z ^ ((5 : ℝ) / 4)

lemma continuous_parScale : Continuous parScale := contDiff_parScale.continuous

lemma continuous_rpow_five_quarters : Continuous fun s : ℝ => s ^ ((5 : ℝ) / 4) := by
  rw [continuous_iff_continuousAt]
  intro s
  exact Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))

lemma continuous_parScale_rpow : Continuous fun z : STime => parScale z ^ ((5 : ℝ) / 4) :=
  continuous_rpow_five_quarters.comp continuous_parScale

lemma continuous_parRadPair {U : STime → E3} (hU : Continuous U) : Continuous (parRadPair U) :=
  continuous_finset_sum (Finset.univ : Finset (Fin 3)) fun a _ =>
    ((EuclideanSpace.proj (𝕜 := ℝ) a).continuous.comp continuous_snd).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) a).continuous.comp hU)

lemma measurable_parMass {U : STime → E3} (hU : Continuous U) : Measurable (parMass U) :=
  (continuous_parRadPair hU).measurable.div continuous_parScale_rpow.measurable

/-- The probe by the cut-off parabolic weight, written through the mass
density. -/
lemma parProbe_cut (chi : ℝ → ℝ) (W : STime → E3) (z : STime) :
    parProbe (parWeightOf (parCutProfile chi)) W z = chi (parScale z) * parMass W z := by
  have hrp : parScale z ^ (-(5 : ℝ) / 4) = (parScale z ^ ((5 : ℝ) / 4))⁻¹ := by
    rw [show (-(5 : ℝ) / 4) = -((5 : ℝ) / 4) by ring, Real.rpow_neg (parScale_nonneg z)]
  simp only [parProbe, parWeightOf_apply, parCutProfile, parMass, parRadPair, hrp]
  field_simp

/-- **The residual integrand carries no net power of the parabolic scale.** -/
lemma parabolic_residual_eq (chi' : ℝ → ℝ) (U : STime → E3) (z : STime) :
    4 * chi' (parScale z) * parScale z ^ (-(1 : ℝ) / 4) * parRadPair U z
      = 4 * (chi' (parScale z) * parScale z) * parMass U z := by
  rcases eq_or_lt_of_le (parScale_nonneg z) with h0 | hpos
  · have h1 : parScale z ^ (-(1 : ℝ) / 4) = 0 := by
      rw [← h0, Real.zero_rpow (by norm_num)]
    rw [h1, ← h0]
    ring
  · have hkey : parScale z ^ (-(1 : ℝ) / 4)
        = parScale z * (parScale z ^ ((5 : ℝ) / 4))⁻¹ := by
      rw [← Real.rpow_neg (parScale_nonneg z)]
      nth_rewrite 2 [show parScale z = parScale z ^ (1 : ℝ) from (Real.rpow_one _).symm]
      rw [← Real.rpow_add hpos]
      norm_num
    rw [hkey]
    simp only [parMass, div_eq_mul_inv]
    ring

/-! ## The tail regions in the parabolic gauge -/

/-- The tail region of the parabolic gauge outside the band `[1/(n+1), n+1]`. -/
def parTailSet (n : ℕ) : Set STime :=
  {z : STime | parScale z ≤ 1 / (n + 1)} ∪ {z : STime | (n + 1 : ℝ) ≤ parScale z}

lemma measurableSet_parTailSet (n : ℕ) : MeasurableSet (parTailSet n) :=
  ((isClosed_le continuous_parScale continuous_const).measurableSet).union
    ((isClosed_le continuous_const continuous_parScale).measurableSet)

lemma antitone_parTailSet : Antitone parTailSet := by
  intro m n hmn z hz
  simp only [parTailSet, Set.mem_union, Set.mem_setOf_eq] at hz ⊢
  have hstep : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmn
  rcases hz with h | h
  · exact Or.inl (h.trans (div_le_div_of_nonneg_left one_pos.le (by positivity) hstep))
  · exact Or.inr (by linarith)

lemma iInter_parTailSet_subset : (⋂ n, parTailSet n) ⊆ {0} := by
  intro z hz
  simp only [mem_iInter] at hz
  by_contra hne
  have hpos : 0 < parScale z := parScale_pos_of_ne (by simpa using hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (max (parScale z) (1 / parScale z))
  have h1 : parScale z < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have h2 : 1 / parScale z < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hz' := hz n
  simp only [parTailSet, Set.mem_union, Set.mem_setOf_eq] at hz'
  rcases hz' with h | h
  · rw [le_div_iff₀ (by positivity)] at h
    rw [div_lt_iff₀ hpos] at h2
    nlinarith
  · linarith

lemma volume_singleton_zero : (volume : Measure STime) {0} = 0 := by
  have h : ({0} : Set STime) = ({(0 : ℝ)} ×ˢ ({0} : Set E3)) := by
    simp [Prod.ext_iff, Set.ext_iff]
  rw [h, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
  simp

/-- **The tail mass vanishes.**  For an integrable density the mass carried by
the parabolic tails `{s ≤ 1/(n+1)} ∪ {s ≥ n+1}` tends to zero. -/
theorem exists_par_tail_mass_le {mu : STime → ℝ} (hmu : Integrable mu) {eta : ℝ}
    (heta : 0 < eta) : ∃ n : ℕ, ∫ z in parTailSet n, mu z ≤ eta := by
  have htend := tendsto_setIntegral_of_antitone (f := mu) (μ := volume)
    measurableSet_parTailSet antitone_parTailSet ⟨0, hmu.integrableOn⟩
  have hzero : ∫ z in (⋂ n, parTailSet n), mu z = 0 :=
    setIntegral_measure_zero _ (measure_mono_null iInter_parTailSet_subset volume_singleton_zero)
  rw [hzero] at htend
  obtain ⟨n, hn⟩ := (htend.eventually (eventually_le_nhds heta)).exists
  exact ⟨n, hn⟩

/-! ## The existence theorem -/

/-- **A separating parabolic scale probe for an arbitrary spacetime field.**  Let
`U` be a `C¹` field on spacetime whose dimensionless parabolic mass density
`m(z) = ⟪x, U z⟫/s(z)^{5/4}`, `s = ‖x‖⁴+t²`, is integrable.  For every `ε > 0`
there is a compactly supported `C¹` cut-off `χ`, `0 ≤ χ ≤ 1`, in the gauge
variable, such that the probe weight `Φ = χ(s)/s^{5/4}` satisfies

* `|∫ Φ·⟪x, ΛU⟫| ≤ ε` — it is blind to the parabolic scaling direction to
  within `ε`;
* `∫ Φ·⟪x, U⟫ ≥ ∫ m − ε` — it still sees essentially all of the profile's
  parabolic dilation mass.

Here `Λ` is the genuine parabolic scaling generator based at the spacetime
origin.  No radiality, self-similarity, or time-independence of `U` is used. -/
theorem exists_small_residual_parabolic_probe
    {U : STime → E3} (hU : ContDiff ℝ (1 : ℕ) U) (hint : Integrable (parMass U))
    {eps : ℝ} (heps : 0 < eps) :
    ∃ chi chi' : ℝ → ℝ, ∃ a1 b2 : ℝ, 0 < a1 ∧ a1 < b2 ∧
      (∀ s, HasDerivAt chi (chi' s) s) ∧
      (∀ s, s ≤ a1 ∨ b2 ≤ s → chi s = 0) ∧ (∀ s, 0 ≤ chi s) ∧ (∀ s, chi s ≤ 1) ∧
      |∫ z : STime, parProbe (parWeightOf (parCutProfile chi)) (parGen U) z| ≤ eps ∧
      (∫ z : STime, parMass U z) - eps
        ≤ ∫ z : STime, parProbe (parWeightOf (parCutProfile chi)) U z := by
  classical
  have hintabs : Integrable (fun z : STime => |parMass U z|) := hint.abs
  have hmunn : ∀ z : STime, 0 ≤ |parMass U z| := fun z => abs_nonneg _
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
  have hadj := parabolic_cutoff_probe_adjoint (chi := chi) (chi' := chi') (U := U)
    hchi hchi'c ha1pos (fun s hs => hz0 s hs) (fun s hs => hz'0 s hs)
    (fun s hs => hzb s hs) hU
  -- the residual integrand, in mass form
  set G : STime → ℝ := fun z => 4 * (chi' (parScale z) * parScale z) * parMass U z with hG
  have hresform : (fun z : STime =>
      4 * chi' (parScale z) * parScale z ^ (-(1 : ℝ) / 4) * parRadPair U z) = G :=
    funext fun z => parabolic_residual_eq chi' U z
  -- pointwise bound on the residual integrand
  have hbound : ∀ z : STime,
      |G z| ≤ Cc * Set.indicator (parTailSet n) (fun w : STime => |parMass U w|) z := by
    intro z
    have hnn : 0 ≤ Set.indicator (parTailSet n) (fun w : STime => |parMass U w|) z :=
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
      have hkey : |G z| = 4 * |chi' (parScale z) * parScale z| * |parMass U z| := by
        simp only [hG, abs_mul]
        norm_num
      rw [hkey, hCc]
      nlinarith [hmunn z, abs_nonneg (chi' (parScale z) * parScale z)]
  -- integrability of the residual
  have hindint : Integrable (fun z : STime =>
      Cc * Set.indicator (parTailSet n) (fun w : STime => |parMass U w|) z) :=
    (hintabs.indicator (measurableSet_parTailSet n)).const_mul Cc
  have hGmeas : AEStronglyMeasurable G :=
    Measurable.aestronglyMeasurable
      ((measurable_const.mul
        (((hchi'c.comp continuous_parScale).measurable).mul
          continuous_parScale.measurable)).mul (measurable_parMass hU.continuous))
  have hGint : Integrable G :=
    Integrable.mono' hindint hGmeas (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hbound z)
  have htailint : (∫ z : STime, Set.indicator (parTailSet n)
        (fun w : STime => |parMass U w|) z)
      = ∫ z in parTailSet n, |parMass U z| :=
    integral_indicator (measurableSet_parTailSet n)
  have htail_le : (∫ z : STime, Set.indicator (parTailSet n)
      (fun w : STime => |parMass U w|) z) ≤ eps / (Cc + 1) := by
    rw [htailint]; exact hn
  -- the residual is small
  have hres : |∫ z : STime, G z| ≤ eps := by
    have h1 : |∫ z : STime, G z| ≤ ∫ z : STime, |G z| := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ := (volume : Measure STime)) (f := G)
    have h2 : (∫ z : STime, |G z|)
        ≤ ∫ z : STime, Cc * Set.indicator (parTailSet n)
            (fun w : STime => |parMass U w|) z :=
      integral_mono hGint.abs hindint hbound
    have h3 : (∫ z : STime, Cc * Set.indicator (parTailSet n)
        (fun w : STime => |parMass U w|) z)
        = Cc * ∫ z : STime, Set.indicator (parTailSet n)
            (fun w : STime => |parMass U w|) z := integral_const_mul _ _
    have h4 : Cc * (∫ z : STime, Set.indicator (parTailSet n)
        (fun w : STime => |parMass U w|) z) ≤ Cc * (eps / (Cc + 1)) :=
      mul_le_mul_of_nonneg_left htail_le hCc0.le
    have h5 : Cc * (eps / (Cc + 1)) ≤ eps := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [heps.le, hCc0.le]
    linarith
  -- the probe of `U` keeps its mass
  have hgmeas : Measurable (fun z : STime =>
      parProbe (parWeightOf (parCutProfile chi)) U z) := by
    have hfun : (fun z : STime => parProbe (parWeightOf (parCutProfile chi)) U z)
        = fun z : STime => chi (parScale z) * parMass U z :=
      funext fun z => parProbe_cut chi U z
    rw [hfun]
    have hchic : Continuous chi := continuous_iff_continuousAt.2 fun s => (hchi s).continuousAt
    exact ((hchic.comp continuous_parScale).measurable).mul (measurable_parMass hU.continuous)
  have hdiffbound : ∀ z : STime,
      |parProbe (parWeightOf (parCutProfile chi)) U z - parMass U z|
        ≤ Set.indicator (parTailSet n) (fun w : STime => |parMass U w|) z := by
    intro z
    have hval : parProbe (parWeightOf (parCutProfile chi)) U z - parMass U z
        = (chi (parScale z) - 1) * parMass U z := by
      rw [parProbe_cut]
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
  have hgint : Integrable (fun z : STime => parProbe (parWeightOf (parCutProfile chi)) U z) := by
    refine Integrable.mono' ((hintabs.indicator (measurableSet_parTailSet n)).add hintabs)
      hgmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    have hd := hdiffbound z
    have htri := abs_sub_abs_le_abs_sub
      (parProbe (parWeightOf (parCutProfile chi)) U z) (parMass U z)
    show |parProbe (parWeightOf (parCutProfile chi)) U z|
        ≤ Set.indicator (parTailSet n) (fun w : STime => |parMass U w|) z + |parMass U z|
    linarith
  have hcore : (∫ z : STime, parMass U z) - eps
      ≤ ∫ z : STime, parProbe (parWeightOf (parCutProfile chi)) U z := by
    have hdiff : |(∫ z : STime, parProbe (parWeightOf (parCutProfile chi)) U z)
        - ∫ z : STime, parMass U z| ≤ eps := by
      rw [← integral_sub hgint hint]
      have h1 : |∫ z : STime, (parProbe (parWeightOf (parCutProfile chi)) U z - parMass U z)|
          ≤ ∫ z : STime, |parProbe (parWeightOf (parCutProfile chi)) U z - parMass U z| := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := (volume : Measure STime))
            (f := fun z : STime => parProbe (parWeightOf (parCutProfile chi)) U z - parMass U z)
      have h2 : (∫ z : STime, |parProbe (parWeightOf (parCutProfile chi)) U z - parMass U z|)
          ≤ ∫ z : STime, Set.indicator (parTailSet n)
              (fun w : STime => |parMass U w|) z :=
        integral_mono (hgint.sub hint).abs
          (hintabs.indicator (measurableSet_parTailSet n)) hdiffbound
      have h3 : (∫ z : STime, Set.indicator (parTailSet n)
          (fun w : STime => |parMass U w|) z) ≤ eps := by
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
