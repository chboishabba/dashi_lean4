/-
# Existence of a separating dilation probe for an arbitrary field

`CutoffDilationProbe.lean` proves, for every `C¹` field `U` on `ℝ³` — not
assumed radial, not assumed self-similar — and every `C¹` cut-off `χ` supported
in a compact annulus,

  `∫ (χ(‖x‖)/‖x‖³)·⟪x, ΛU⟫ = − ∫ (χ'(‖x‖)/‖x‖²)·⟪x, U⟫`,   `ΛU = U + (DU)x`.

This file discharges the remaining step: *choosing* the cut-off so that the
right-hand side is as small as one likes while the pairing with `U` itself keeps
essentially all of its mass.

The mechanism is the scaling dimension of the residual.  Write

  `μ(x) = |⟪x,U x⟫|/‖x‖³`

for the dimensionless mass density of the probe — the density whose integral the
probe of `U` is.  On a dyadic transition annulus `[a,2a]` the derivative of the
cut-off is `O(1/a)` while `‖x‖ ≤ 2a` there, so the whole residual carried by that
annulus is at most a universal constant times the `μ`-mass of the annulus: the
residual carries no net power of the radius (`exists_dyadic_plateau_cutoff`,
item `hCbound`).  Hence, whenever `μ` is integrable, putting both transitions in
the tails `{‖x‖ ≤ ρ}`, `{‖x‖ ≥ R}` — whose `μ`-mass tends to `0` as `ρ → 0`,
`R → ∞` — makes the residual arbitrarily small, while the plateau covers all but
that same vanishing mass.

* `ClayNS.tailSet`, `ClayNS.exists_tail_mass_le` — the tail regions and the
  vanishing of their mass.
* `ClayNS.exists_dyadic_plateau_cutoff` — the cut-off, with the scale-invariant
  derivative bound `|χ'(r)|·r ≤ C` for a constant `C` independent of the two
  transition scales.
* `ClayNS.exists_small_residual_dilation_probe` — **the theorem**: for every
  tolerance `ε > 0` there is a compactly supported cut-off `χ` with

    `|∫ (χ/‖x‖³)·⟪x, ΛU⟫| ≤ ε`   and   `∫ (χ/‖x‖³)·⟪x,U⟫ ≥ ∫ ⟪x,U⟫/‖x‖³ − ε`.

  This is exactly the pair `(δ, a₀)` required by
  `ClayNS.gram_anchor_lower_bound_approx`, now for a *general* field.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.CutoffDilationProbe
import RequestProject.NavierStokes.ScaleProbeExistence

open scoped BigOperators
open MeasureTheory Filter Topology Set

noncomputable section

namespace ClayNS

/-! ## The tail regions -/

/-- The tail region outside the window `[1/(n+1), n+1]`. -/
def tailSet (n : ℕ) : Set E3 := {x : E3 | ‖x‖ ≤ 1 / (n + 1)} ∪ {x : E3 | (n + 1 : ℝ) ≤ ‖x‖}

lemma measurableSet_tailSet (n : ℕ) : MeasurableSet (tailSet n) :=
  ((isClosed_le continuous_norm continuous_const).measurableSet).union
    ((isClosed_le continuous_const continuous_norm).measurableSet)

lemma antitone_tailSet : Antitone tailSet := by
  intro m n hmn x hx
  simp only [tailSet, Set.mem_union, Set.mem_setOf_eq] at hx ⊢
  have hstep : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmn
  rcases hx with h | h
  · exact Or.inl (h.trans (div_le_div_of_nonneg_left one_pos.le (by positivity) hstep))
  · exact Or.inr (by linarith)

lemma iInter_tailSet_subset : (⋂ n, tailSet n) ⊆ {0} := by
  intro x hx
  simp only [mem_iInter] at hx
  by_contra hne
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 (by simpa using hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (max ‖x‖ (1 / ‖x‖))
  have h1 : ‖x‖ < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have h2 : 1 / ‖x‖ < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hx' := hx n
  simp only [tailSet, Set.mem_union, Set.mem_setOf_eq] at hx'
  rcases hx' with h | h
  · rw [le_div_iff₀ (by positivity)] at h
    rw [div_lt_iff₀ hpos] at h2
    nlinarith
  · linarith

/-- **The tail mass vanishes.**  For an integrable density the mass carried by
the tails `{‖x‖ ≤ 1/(n+1)} ∪ {‖x‖ ≥ n+1}` tends to zero. -/
theorem exists_tail_mass_le {mu : E3 → ℝ} (hmu : Integrable mu) {eta : ℝ} (heta : 0 < eta) :
    ∃ n : ℕ, ∫ x in tailSet n, mu x ≤ eta := by
  have htend := tendsto_setIntegral_of_antitone (f := mu) (μ := volume)
    measurableSet_tailSet antitone_tailSet ⟨0, hmu.integrableOn⟩
  have hzero : ∫ x in (⋂ n, tailSet n), mu x = 0 :=
    setIntegral_measure_zero _ (measure_mono_null iInter_tailSet_subset (by simp))
  rw [hzero] at htend
  obtain ⟨n, hn⟩ := (htend.eventually (eventually_le_nhds heta)).exists
  exact ⟨n, hn⟩

/-! ## The cut-off, with a scale-invariant derivative bound -/

lemma plateauCut'_eq_zero_left {a1 a2 b1 b2 : ℝ} (h1 : a1 < a2) {r : ℝ} (hr : r ≤ a1) :
    plateauCut' a1 a2 b1 b2 r = 0 := by
  have hq : (r - a1) / (a2 - a1) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg <;> linarith
  simp [plateauCut', sTrans'_eq_zero_of_nonpos hq, Real.smoothTransition.zero_of_nonpos hq]

lemma plateauCut'_eq_zero_right {a1 a2 b1 b2 : ℝ} (h2 : b1 < b2) {r : ℝ} (hr : b2 ≤ r) :
    plateauCut' a1 a2 b1 b2 r = 0 := by
  have hq : (b2 - r) / (b2 - b1) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg <;> linarith
  simp [plateauCut', sTrans'_eq_zero_of_nonpos hq, Real.smoothTransition.zero_of_nonpos hq]

/-- **The two-scale plateau cut-off.**  For `0 < ρ ≤ R` there is a `C¹` cut-off
which is `1` on `[ρ,R]`, vanishes outside `[ρ/2, 2R]`, and whose derivative obeys
the *scale-invariant* bound `|χ'(r)|·r ≤ C` with `C` independent of `ρ` and `R`:
the transition annuli are dyadic, so the width of each equals its radius. -/
theorem exists_dyadic_plateau_cutoff {rho R K : ℝ} (hrho : 0 < rho) (hle : rho ≤ R)
    (hK : ∀ x, |sTrans' x| ≤ K) :
    ∃ (chi chi' : ℝ → ℝ),
      (∀ r, HasDerivAt chi (chi' r) r) ∧ Continuous chi' ∧
      (∀ r, 0 ≤ chi r) ∧ (∀ r, chi r ≤ 1) ∧
      (∀ r, r ≤ rho / 2 → chi r = 0) ∧ (∀ r, 2 * R ≤ r → chi r = 0) ∧
      (∀ r, rho ≤ r → r ≤ R → chi r = 1) ∧
      (∀ r, r ≤ rho / 2 → chi' r = 0) ∧ (∀ r, 2 * R ≤ r → chi' r = 0) ∧
      (∀ r, rho ≤ r → r ≤ R → chi' r = 0) ∧
      (∀ r, 0 ≤ r → |chi' r| * r ≤ 2 * K) := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK 0)
  have hR0 : 0 < R := lt_of_lt_of_le hrho hle
  have h12 : rho / 2 < rho := by linarith
  have h34 : R < 2 * R := by linarith
  have hab : rho ≤ R := hle
  refine ⟨plateauCut (rho / 2) rho R (2 * R), plateauCut' (rho / 2) rho R (2 * R),
    hasDerivAt_plateauCut h12 h34, continuous_plateauCut' _ _ _ _,
    fun r => plateauCut_nonneg _ _ _ _ r, fun r => plateauCut_le_one _ _ _ _ r,
    fun r hr => plateauCut_eq_zero_outside h12 h34 (Or.inl hr),
    fun r hr => plateauCut_eq_zero_outside h12 h34 (Or.inr hr),
    fun r hr1 hr2 => plateauCut_eq_one h12 h34 hr1 hr2,
    fun r hr => plateauCut'_eq_zero_left h12 hr,
    fun r hr => plateauCut'_eq_zero_right h34 hr,
    fun r hr1 hr2 => plateauCut'_eq_zero_middle h12 h34 hr1 hr2, ?_⟩
  intro r hr
  rcases le_or_gt r rho with hin | hin
  · have hd : |plateauCut' (rho / 2) rho R (2 * R) r| ≤ K / (rho - rho / 2) :=
      plateauCut'_inner_bound h12 h34 hab hK hin
    have hK2 : K / (rho - rho / 2) = 2 * K / rho := by field_simp; ring
    rw [hK2] at hd
    calc |plateauCut' (rho / 2) rho R (2 * R) r| * r ≤ (2 * K / rho) * rho :=
          mul_le_mul hd hin hr (by positivity)
      _ = 2 * K := by field_simp
  · rcases le_or_gt r R with hmid | hmid
    · rw [plateauCut'_eq_zero_middle h12 h34 hin.le hmid]
      simpa using hK0
    · rcases le_or_gt r (2 * R) with hout | hout
      · have hd : |plateauCut' (rho / 2) rho R (2 * R) r| ≤ K / (2 * R - R) :=
          plateauCut'_outer_bound h12 h34 hab hK hmid.le
        have hKb : K / (2 * R - R) = K / R := by ring_nf
        rw [hKb] at hd
        calc |plateauCut' (rho / 2) rho R (2 * R) r| * r ≤ (K / R) * (2 * R) :=
              mul_le_mul hd hout hr (by positivity)
          _ = 2 * K := by field_simp
      · rw [plateauCut'_eq_zero_right h34 hout.le]
        simpa using hK0

/-! ## Measurability of the mass density -/

lemma continuous_radPair {U : E3 → E3} (hU : Continuous U) : Continuous (radPair U) :=
  continuous_finset_sum (Finset.univ : Finset (Fin 3)) fun a _ =>
    (EuclideanSpace.proj (𝕜 := ℝ) a).continuous.mul
      ((EuclideanSpace.proj (𝕜 := ℝ) a).continuous.comp hU)

lemma measurable_massDensity {U : E3 → E3} (hU : Continuous U) :
    Measurable (fun x : E3 => radPair U x / ‖x‖ ^ 3) :=
  (continuous_radPair hU).measurable.div ((continuous_norm.pow 3).measurable)

/-- The probe of a field by the cut-off scale-invariant weight, written out. -/
lemma dilProbe_cutProfile (chi : ℝ → ℝ) (W : E3 → E3) (x : E3) :
    dilProbe (radWeight (cutProfile chi)) W x = chi ‖x‖ / ‖x‖ ^ 3 * radPair W x := rfl

/-! ## The existence theorem -/

/-- **A separating dilation probe for an arbitrary `C¹` field.**  Let `U` be a
`C¹` field on `ℝ³` whose dimensionless dilation mass `μ(x) = |⟪x,U x⟫|/‖x‖³` is
integrable.  For every `ε > 0` there is a compactly supported `C¹` cut-off `χ`,
`0 ≤ χ ≤ 1`, such that the probe weight `w(x) = (χ(‖x‖)/‖x‖³)·x` satisfies

* `|∫ ⟪w, ΛU⟫| ≤ ε` — it is blind to the scaling direction to within `ε`;
* `∫ ⟪w, U⟫ ≥ ∫ ⟪x,U x⟫/‖x‖³ − ε` — it still sees essentially all of the
  profile's dilation mass.

No radiality, self-similarity, or time-independence of `U` is used. -/
theorem exists_small_residual_dilation_probe
    {U : E3 → E3} (hU : ContDiff ℝ (1 : ℕ) U)
    (hint : Integrable (fun x : E3 => |radPair U x| / ‖x‖ ^ 3))
    {eps : ℝ} (heps : 0 < eps) :
    ∃ chi chi' : ℝ → ℝ, ∃ a1 b2 : ℝ, 0 < a1 ∧ a1 < b2 ∧
      (∀ r, HasDerivAt chi (chi' r) r) ∧
      (∀ r, r ≤ a1 ∨ b2 ≤ r → chi r = 0) ∧ (∀ r, 0 ≤ chi r) ∧ (∀ r, chi r ≤ 1) ∧
      |∫ x : E3, dilProbe (radWeight (cutProfile chi)) (dilGen U) x| ≤ eps ∧
      (∫ x : E3, radPair U x / ‖x‖ ^ 3) - eps
        ≤ ∫ x : E3, dilProbe (radWeight (cutProfile chi)) U x := by
  classical
  -- the mass density
  have hmunn : ∀ x : E3, 0 ≤ |radPair U x| / ‖x‖ ^ 3 := fun x => by positivity
  obtain ⟨K, hK0, hK⟩ := exists_smoothTransition_deriv_bound
  set Cc : ℝ := 2 * K with hCc
  have hCc0 : 0 < Cc := by positivity
  have heta : 0 < eps / (Cc + 1) := by positivity
  obtain ⟨n, hn⟩ := exists_tail_mass_le hint heta
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
  have hchiz : ∀ r, r ≤ 1 / ((n : ℝ) + 1) / 2 ∨ 2 * ((n : ℝ) + 1) ≤ r → chi r = 0 := by
    intro r hr
    rcases hr with hr | hr
    · exact hz0 r hr
    · exact hzb r hr
  -- the adjoint identity
  have hadj := cutoff_dilation_probe_adjoint (chi := chi) (chi' := chi') (U := U)
    hchi hchi'c ha1pos ha1b2 (fun r hr => hz0 r hr) (fun r hr => hz'0 r hr)
    (fun r hr => hzb r hr) hU
  -- pointwise bound on the residual integrand
  have hbound : ∀ x : E3, |chi' ‖x‖ / ‖x‖ ^ 2 * radPair U x|
      ≤ Cc * Set.indicator (tailSet n) (fun y : E3 => |radPair U y| / ‖y‖ ^ 3) x := by
    intro x
    have hnn : 0 ≤ Set.indicator (tailSet n) (fun y : E3 => |radPair U y| / ‖y‖ ^ 3) x :=
      Set.indicator_nonneg (fun y _ => hmunn y) x
    rcases eq_or_ne x 0 with rfl | hx
    · rw [hz'0 _ (by simpa using ha1pos.le)]
      simpa using mul_nonneg hCc0.le hnn
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    by_cases hmid : 1 / ((n : ℝ) + 1) ≤ ‖x‖ ∧ ‖x‖ ≤ (n : ℝ) + 1
    · rw [hz'mid _ hmid.1 hmid.2]
      simpa using mul_nonneg hCc0.le hnn
    · -- off the plateau: the point lies in the tail region
      have hmem : x ∈ tailSet n := by
        simp only [tailSet, Set.mem_union, Set.mem_setOf_eq]
        by_contra hcon
        push_neg at hcon
        exact hmid ⟨le_of_lt (by simpa using hcon.1), le_of_lt hcon.2⟩
      rw [Set.indicator_of_mem hmem]
      have hkey : |chi' ‖x‖ / ‖x‖ ^ 2 * radPair U x|
          = (|chi' ‖x‖| * ‖x‖) * (|radPair U x| / ‖x‖ ^ 3) := by
        rw [abs_mul, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖x‖ ^ 2)]
        field_simp
      rw [hkey]
      exact mul_le_mul_of_nonneg_right (hCb ‖x‖ hxpos.le) (by positivity)
  -- integrability
  have hindint : Integrable (fun x : E3 =>
      Cc * Set.indicator (tailSet n) (fun y : E3 => |radPair U y| / ‖y‖ ^ 3) x) :=
    (hint.indicator (measurableSet_tailSet n)).const_mul Cc
  have hresmeas : AEStronglyMeasurable (fun x : E3 => chi' ‖x‖ / ‖x‖ ^ 2 * radPair U x) :=
    Measurable.aestronglyMeasurable
      ((((hchi'c.comp continuous_norm).measurable).div
        ((continuous_norm.pow 2).measurable)).mul (continuous_radPair hU.continuous).measurable)
  have hresint : Integrable (fun x : E3 => chi' ‖x‖ / ‖x‖ ^ 2 * radPair U x) :=
    Integrable.mono' hindint hresmeas (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hbound x)
  have htailint : (∫ x : E3, Set.indicator (tailSet n)
        (fun y : E3 => |radPair U y| / ‖y‖ ^ 3) x)
      = ∫ x in tailSet n, |radPair U x| / ‖x‖ ^ 3 :=
    integral_indicator (measurableSet_tailSet n)
  have htail_le : (∫ x : E3, Set.indicator (tailSet n)
      (fun y : E3 => |radPair U y| / ‖y‖ ^ 3) x) ≤ eps / (Cc + 1) := by
    rw [htailint]; exact hn
  -- the residual is small
  have hres : |∫ x : E3, chi' ‖x‖ / ‖x‖ ^ 2 * radPair U x| ≤ eps := by
    have h1 : |∫ x : E3, chi' ‖x‖ / ‖x‖ ^ 2 * radPair U x|
        ≤ ∫ x : E3, |chi' ‖x‖ / ‖x‖ ^ 2 * radPair U x| := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ := (volume : Measure E3))
          (f := fun x : E3 => chi' ‖x‖ / ‖x‖ ^ 2 * radPair U x)
    have h2 : (∫ x : E3, |chi' ‖x‖ / ‖x‖ ^ 2 * radPair U x|)
        ≤ ∫ x : E3, Cc * Set.indicator (tailSet n)
            (fun y : E3 => |radPair U y| / ‖y‖ ^ 3) x :=
      integral_mono hresint.abs hindint hbound
    have h3 : (∫ x : E3, Cc * Set.indicator (tailSet n)
        (fun y : E3 => |radPair U y| / ‖y‖ ^ 3) x)
        = Cc * ∫ x : E3, Set.indicator (tailSet n)
            (fun y : E3 => |radPair U y| / ‖y‖ ^ 3) x := integral_const_mul _ _
    have h4 : Cc * (∫ x : E3, Set.indicator (tailSet n)
        (fun y : E3 => |radPair U y| / ‖y‖ ^ 3) x) ≤ Cc * (eps / (Cc + 1)) :=
      mul_le_mul_of_nonneg_left htail_le hCc0.le
    have h5 : Cc * (eps / (Cc + 1)) ≤ eps := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [heps.le, hCc0.le]
    calc |∫ x : E3, chi' ‖x‖ / ‖x‖ ^ 2 * radPair U x|
        ≤ ∫ x : E3, |chi' ‖x‖ / ‖x‖ ^ 2 * radPair U x| := h1
      _ ≤ ∫ x : E3, Cc * Set.indicator (tailSet n)
            (fun y : E3 => |radPair U y| / ‖y‖ ^ 3) x := h2
      _ = Cc * ∫ x : E3, Set.indicator (tailSet n)
            (fun y : E3 => |radPair U y| / ‖y‖ ^ 3) x := h3
      _ ≤ Cc * (eps / (Cc + 1)) := h4
      _ ≤ eps := h5
  -- the probe of `U` keeps its mass
  have hcmeas : Measurable (fun x : E3 => radPair U x / ‖x‖ ^ 3) :=
    measurable_massDensity hU.continuous
  have hcint : Integrable (fun x : E3 => radPair U x / ‖x‖ ^ 3) :=
    Integrable.mono' hint hcmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simp [Real.norm_eq_abs])
  have hgmeas : Measurable (fun x : E3 => dilProbe (radWeight (cutProfile chi)) U x) := by
    have hfun : (fun x : E3 => dilProbe (radWeight (cutProfile chi)) U x)
        = fun x : E3 => chi ‖x‖ / ‖x‖ ^ 3 * radPair U x := funext fun x => rfl
    rw [hfun]
    have hchic : Continuous chi := continuous_iff_continuousAt.2 fun r => (hchi r).continuousAt
    exact (((hchic.comp continuous_norm).measurable).div
      ((continuous_norm.pow 3).measurable)).mul (continuous_radPair hU.continuous).measurable
  have hdiffbound : ∀ x : E3,
      |dilProbe (radWeight (cutProfile chi)) U x - radPair U x / ‖x‖ ^ 3|
        ≤ Set.indicator (tailSet n) (fun y : E3 => |radPair U y| / ‖y‖ ^ 3) x := by
    intro x
    have hval : dilProbe (radWeight (cutProfile chi)) U x - radPair U x / ‖x‖ ^ 3
        = (chi ‖x‖ - 1) * (radPair U x / ‖x‖ ^ 3) := by
      rw [dilProbe_cutProfile]
      ring
    rw [hval, abs_mul]
    by_cases hmem : x ∈ tailSet n
    · rw [Set.indicator_of_mem hmem]
      have h1 : |chi ‖x‖ - 1| ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith [hchi1 ‖x‖, hchinn ‖x‖], by linarith [hchinn ‖x‖, hchi1 ‖x‖]⟩
      have h2 : |radPair U x / ‖x‖ ^ 3| = |radPair U x| / ‖x‖ ^ 3 := by
        rw [abs_div, abs_pow, abs_norm]
      rw [h2]
      nlinarith [hmunn x, abs_nonneg (chi ‖x‖ - 1)]
    · have hone' : chi ‖x‖ = 1 := by
        simp only [tailSet, Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hmem
        exact hone ‖x‖ hmem.1.le hmem.2.le
      rw [hone']
      simp only [sub_self, abs_zero, zero_mul]
      exact Set.indicator_nonneg (fun y _ => hmunn y) x
  have hgint : Integrable (fun x : E3 => dilProbe (radWeight (cutProfile chi)) U x) := by
    refine Integrable.mono' ((hint.indicator (measurableSet_tailSet n)).add hint)
      hgmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    have hd := hdiffbound x
    have h2 : |radPair U x / ‖x‖ ^ 3| = |radPair U x| / ‖x‖ ^ 3 := by
      rw [abs_div, abs_pow, abs_norm]
    have htri := abs_sub_abs_le_abs_sub (dilProbe (radWeight (cutProfile chi)) U x)
      (radPair U x / ‖x‖ ^ 3)
    rw [h2] at htri
    show |dilProbe (radWeight (cutProfile chi)) U x|
        ≤ Set.indicator (tailSet n) (fun y : E3 => |radPair U y| / ‖y‖ ^ 3) x
          + |radPair U x| / ‖x‖ ^ 3
    linarith
  have hcore : (∫ x : E3, radPair U x / ‖x‖ ^ 3) - eps
      ≤ ∫ x : E3, dilProbe (radWeight (cutProfile chi)) U x := by
    have hdiff : |(∫ x : E3, dilProbe (radWeight (cutProfile chi)) U x)
        - ∫ x : E3, radPair U x / ‖x‖ ^ 3| ≤ eps := by
      rw [← integral_sub hgint hcint]
      have h1 : |∫ x : E3, (dilProbe (radWeight (cutProfile chi)) U x
            - radPair U x / ‖x‖ ^ 3)|
          ≤ ∫ x : E3, |dilProbe (radWeight (cutProfile chi)) U x
            - radPair U x / ‖x‖ ^ 3| := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := (volume : Measure E3))
            (f := fun x : E3 => dilProbe (radWeight (cutProfile chi)) U x
              - radPair U x / ‖x‖ ^ 3)
      have h2 : (∫ x : E3, |dilProbe (radWeight (cutProfile chi)) U x
            - radPair U x / ‖x‖ ^ 3|)
          ≤ ∫ x : E3, Set.indicator (tailSet n)
              (fun y : E3 => |radPair U y| / ‖y‖ ^ 3) x :=
        integral_mono (hgint.sub hcint).abs (hint.indicator (measurableSet_tailSet n))
          hdiffbound
      have h3 : (∫ x : E3, Set.indicator (tailSet n)
          (fun y : E3 => |radPair U y| / ‖y‖ ^ 3) x) ≤ eps := by
        refine htail_le.trans ?_
        rw [div_le_iff₀ (by positivity)]
        nlinarith [heps.le, hCc0.le]
      linarith
    have hab := abs_le.1 hdiff
    linarith [hab.1]
  refine ⟨chi, chi', 1 / ((n : ℝ) + 1) / 2, 2 * ((n : ℝ) + 1), ha1pos, ha1b2, hchi, hchiz,
    hchinn, hchi1, ?_, hcore⟩
  rw [hadj, abs_neg]
  exact hres

end ClayNS
