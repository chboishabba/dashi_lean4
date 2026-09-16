/-
# Row B — the activity decay rate `μ`, derived from the Mayer product structure

`RowBLatticePolymerEnergy` reduced Row B to a *single* scalar: an exponential
activity majorant

    |K(X)| ≤ A e^{−μ|X|},   μ > ν = 1 + 2 log 8,

for the cluster-expansion polymer activities, the entropy rate `ν` having been
discharged unconditionally by `LatticeAnimalEntropy`.  The obstruction recorded
there was that the source states its activity estimates with unspecified `O(1)`
constants, so `μ` cannot be transcribed.

This file removes the need to transcribe it.  The rate is not an independent
input at all: it is *manufactured* by the product structure of the activity.  A
Mayer/cluster activity of a polymer `X` is a product over the constituents of
`X` of factors `e^{−V_p} − 1`, averaged over the remaining field degrees of
freedom.  Each factor is small when the per-constituent interaction is small,
and a product of `|X|` factors each bounded by `ε` is bounded by `ε^{|X|}`,
which *is* an exponential majorant with the explicit rate

    μ = activityDecayRate ε = −log ε,

a rate that tends to `+∞` as `ε → 0`.  So the competition `μ > ν` is not a
delicate coincidence: it is the statement `ε < e^{−ν}`, i.e. a smallness
threshold on the per-constituent interaction, and for the four-dimensional
lattice that threshold is the fully explicit number `e^{−1}/64`, for which
`1/200` is a valid and easily checked sufficient bound.

Contents.

* `activityDecayRate`, `pow_eq_exp_neg_activityDecayRate`,
  `activityDecayRate_gt_of_lt_exp_neg` — the dictionary between a geometric
  majorant `ε^n` and an exponential one `e^{−μn}`.
* `mayerFactor`, `abs_mayerFactor_le` — `|e^{−V} − 1| ≤ 2|V|` for `|V| ≤ 1`, so
  the per-constituent smallness is inherited from the interaction.
* `mayerActivity`, `abs_mayerActivity_le`, `mayerActivity_exp_decay` — the
  product bound and its exponential form.
* `integratedMayerActivity`, `abs_integratedMayerActivity_le` — the same bound
  survives averaging the activity over a probability measure on the field, which
  is the form the activity actually takes in a cluster expansion.
* `lattice4_mayer_rate_exceeds_entropy` — the explicit threshold
  `2v < e^{−1}/64`, and the cruder sufficient bound `v ≤ 1/400`.
* `lattice4_mayer_shell_energy_geometric`, `lattice4_mayer_shell_energy_tsum_le`
  — Row B's geometric shell energy and finite total energy for the literal
  four-dimensional lattice Mayer activities, with **no** hypothesis on a decay
  rate: the only input is per-plaquette smallness of the interaction.
* `smallCoupling_mayer_threshold` — the smallness threshold expressed in the
  coupling: if the per-constituent interaction is `g²·W` with `|W| ≤ w`, then
  `g² ≤ 1/(400 w)` suffices.

**Honest status.**  What is proved here is that the Row-B decay rate follows
from per-constituent smallness of the polymer interaction together with the
product/Mayer form of the activity, with completely explicit constants — no
`O(1)` is transcribed and no rate is assumed.  What is *not* proved here is that
the literal Bałaban cluster-expansion activities have exactly this product form
after all the small-field/large-field surgery of CMP 116; that identification
remains outstanding, and Row B is therefore still not closed.
-/
import RequestProject.YangMills.RowBLatticePolymerEnergy

namespace YangMills

open Finset MeasureTheory

variable {ι : Type*}

/-! ## 1. Geometric majorant ↔ exponential majorant -/

/-- The decay rate produced by a per-constituent smallness `ε`: `μ = −log ε`. -/
noncomputable def activityDecayRate (eps : ℝ) : ℝ := -Real.log eps

/-- A geometric majorant `ε^n` *is* an exponential majorant `e^{−μn}`. -/
theorem pow_eq_exp_neg_activityDecayRate {eps : ℝ} (heps : 0 < eps) (n : ℕ) :
    eps ^ n = Real.exp (-(activityDecayRate eps * n)) := by
  rw [activityDecayRate]
  have : -(-Real.log eps * (n : ℝ)) = (n : ℝ) * Real.log eps := by ring
  rw [this, Real.exp_nat_mul, Real.exp_log heps]

/-- **The rate beats any prescribed entropy once the constituents are small
enough.**  `ε < e^{−ν}` is exactly `ν < μ`. -/
theorem activityDecayRate_gt_of_lt_exp_neg {eps nu : ℝ} (heps : 0 < eps)
    (h : eps < Real.exp (-nu)) : nu < activityDecayRate eps := by
  have hlog : Real.log eps < Real.log (Real.exp (-nu)) :=
    Real.log_lt_log heps h
  rw [Real.log_exp] at hlog
  rw [activityDecayRate]
  linarith

/-! ## 2. The Mayer factor is small when the interaction is small -/

/-- The Mayer factor of a single constituent with interaction `V`. -/
noncomputable def mayerFactor (V : ℝ) : ℝ := Real.exp (-V) - 1

/-- `|e^{−V} − 1| ≤ 2|V|` for `|V| ≤ 1`: the per-constituent smallness of the
activity is inherited, with an explicit factor `2`, from the interaction. -/
theorem abs_mayerFactor_le {V : ℝ} (h : |V| ≤ 1) : |mayerFactor V| ≤ 2 * |V| := by
  have hV : |(-V)| ≤ 1 := by rwa [abs_neg]
  have := Real.abs_exp_sub_one_le hV
  rwa [abs_neg] at this

/-! ## 3. The polymer activity and its exponential majorant -/

/-- The Mayer activity of a polymer: the product of the Mayer factors of its
constituents. -/
noncomputable def mayerActivity (V : ι → ℝ) (S : Finset ι) : ℝ :=
  ∏ p ∈ S, mayerFactor (V p)

/-- A product of `|S|` factors each bounded by `2v` is bounded by `(2v)^{|S|}`. -/
theorem abs_mayerActivity_le {V : ι → ℝ} {v : ℝ} {S : Finset ι}
    (hV : ∀ p, |V p| ≤ v) (hv1 : v ≤ 1) :
    |mayerActivity V S| ≤ (2 * v) ^ S.card := by
  rw [mayerActivity, Finset.abs_prod]
  calc ∏ p ∈ S, |mayerFactor (V p)| ≤ ∏ _p ∈ S, 2 * v := by
        refine Finset.prod_le_prod (fun p _ => abs_nonneg _) (fun p _ => ?_)
        exact le_trans (abs_mayerFactor_le (le_trans (hV p) hv1))
          (by linarith [hV p])
    _ = (2 * v) ^ S.card := by rw [Finset.prod_const]

/-- **The exponential activity majorant, with a derived rate.**  With
`μ = −log(2v)` one has `|K(S)| ≤ e^{−μ|S|}`, and `μ → ∞` as `v → 0`. -/
theorem mayerActivity_exp_decay {V : ι → ℝ} {v : ℝ} {S : Finset ι}
    (hV : ∀ p, |V p| ≤ v) (hv0 : 0 < v) (hv1 : v ≤ 1) :
    |mayerActivity V S| ≤ Real.exp (-(activityDecayRate (2 * v) * S.card)) := by
  have h2v : (0 : ℝ) < 2 * v := by linarith
  rw [← pow_eq_exp_neg_activityDecayRate h2v]
  exact abs_mayerActivity_le hV hv1

/-! ## 4. Averaging over the field does not spoil the bound -/

/-- The activity of a cluster expansion is the Mayer product averaged over the
remaining field degrees of freedom. -/
noncomputable def integratedMayerActivity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (V : Ω → ι → ℝ) (S : Finset ι) : ℝ :=
  ∫ w, mayerActivity (V w) S ∂P

/-- **The exponential majorant survives the field average.**  A probability
measure cannot increase a uniform bound, so the averaged activity obeys the same
rate `μ = −log(2v)`. -/
theorem abs_integratedMayerActivity_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {V : Ω → ι → ℝ} {v : ℝ} {S : Finset ι}
    (hV : ∀ w p, |V w p| ≤ v) (hv0 : 0 < v) (hv1 : v ≤ 1) :
    |integratedMayerActivity P V S| ≤ Real.exp (-(activityDecayRate (2 * v) * S.card)) := by
  have hbnd : ∀ w, ‖mayerActivity (V w) S‖
      ≤ Real.exp (-(activityDecayRate (2 * v) * S.card)) := by
    intro w
    simpa [Real.norm_eq_abs] using mayerActivity_exp_decay (hV w) hv0 hv1
  have := norm_integral_le_of_norm_le_const (μ := P)
    (C := Real.exp (-(activityDecayRate (2 * v) * S.card)))
    (f := fun w => mayerActivity (V w) S)
    (Filter.Eventually.of_forall hbnd)
  simpa [integratedMayerActivity, Real.norm_eq_abs, MeasureTheory.probReal_univ] using this

/-! ## 5. The explicit four-dimensional threshold -/

/-- The entropy rate of `ℤ⁴` in closed form: `e^{−ν} = e^{−1}/64`. -/
theorem exp_neg_lattice4EntropyRate :
    Real.exp (-lattice4EntropyRate) = Real.exp (-1) / 64 := by
  have h8' : Real.exp (2 * Real.log 8) = 64 := by
    rw [show (2 : ℝ) * Real.log 8 = ((2 : ℕ) : ℝ) * Real.log 8 by norm_num,
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 8)]
    norm_num
  rw [lattice4EntropyRate, show -(1 + 2 * Real.log 8) = -1 + -(2 * Real.log 8) by ring,
    Real.exp_add, Real.exp_neg (2 * Real.log 8), h8']
  ring

/-- `1/200` is below the four-dimensional threshold `e^{−1}/64`. -/
theorem lattice4_threshold_lower : (1 : ℝ) / 200 < Real.exp (-lattice4EntropyRate) := by
  rw [exp_neg_lattice4EntropyRate, Real.exp_neg]
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hinv : 1 / 2.7182818286 < (Real.exp 1)⁻¹ := by
    rw [inv_eq_one_div]
    exact one_div_lt_one_div_of_lt hpos he
  linarith

/-- **The derived rate beats the proved entropy** as soon as the per-constituent
interaction satisfies `v ≤ 1/400`. -/
theorem lattice4_mayer_rate_exceeds_entropy {v : ℝ} (hv0 : 0 < v) (hv : v ≤ 1 / 400) :
    lattice4EntropyRate < activityDecayRate (2 * v) := by
  refine activityDecayRate_gt_of_lt_exp_neg (by linarith) ?_
  have h1 : 2 * v ≤ 1 / 200 := by linarith
  exact lt_of_le_of_lt h1 lattice4_threshold_lower

/-! ## 6. Row B's shell energy for the literal lattice Mayer activities -/

/-- **Geometric shell energy for four-dimensional lattice Mayer polymers, with
no assumed decay rate.**  The only input is per-plaquette smallness of the
interaction; the decay rate is `−log(2v)` and the entropy rate is the proved
lattice-animal constant. -/
theorem lattice4_mayer_shell_energy_geometric
    {shell : ℕ → Finset (Finset (Fin 4 → ℤ))} {V : (Fin 4 → ℤ) → ℝ} {v : ℝ} {vtx : Fin 4 → ℤ}
    (hshell : ∀ n, ∀ S ∈ shell n, IsAnimal (nbFromE latticeStep) vtx S ∧ S.card = n)
    (hV : ∀ p, |V p| ≤ v) (hv0 : 0 < v) (hv : v ≤ 1 / 400) (n : ℕ) :
    ∑ S ∈ shell n, |mayerActivity V S|
      ≤ ((1 * markCost 0 (activityDecayRate (2 * v)) lattice4EntropyRate) * 2)
          * shellRatio lattice4EntropyRate
              (markedRate (activityDecayRate (2 * v)) lattice4EntropyRate) ^ n := by
  refine lattice4_marked_shell_energy_geometric (A := 1) (m := 0) (v := vtx) hshell ?_
    zero_le_one (lattice4_mayer_rate_exceeds_entropy hv0 hv) n
  intro k S hS
  have hcard : S.card = k := (hshell k S hS).2
  have := mayerActivity_exp_decay (V := V) (v := v) (S := S) hV hv0 (by linarith)
  rw [hcard] at this
  simpa using this

/-- **The total polymer energy of the four-dimensional lattice Mayer expansion is
finite**, with an explicit bound, under per-plaquette smallness alone. -/
theorem lattice4_mayer_shell_energy_tsum_le
    {shell : ℕ → Finset (Finset (Fin 4 → ℤ))} {V : (Fin 4 → ℤ) → ℝ} {v : ℝ} {vtx : Fin 4 → ℤ}
    (hshell : ∀ n, ∀ S ∈ shell n, IsAnimal (nbFromE latticeStep) vtx S ∧ S.card = n)
    (hV : ∀ p, |V p| ≤ v) (hv0 : 0 < v) (hv : v ≤ 1 / 400) :
    ∑' n : ℕ, (∑ S ∈ shell n, |mayerActivity V S|)
      ≤ ((1 * markCost 0 (activityDecayRate (2 * v)) lattice4EntropyRate) * 2)
          / (1 - shellRatio lattice4EntropyRate
              (markedRate (activityDecayRate (2 * v)) lattice4EntropyRate)) := by
  refine lattice4_marked_shell_energy_tsum_le (A := 1) (m := 0) (v := vtx) hshell ?_
    zero_le_one (lattice4_mayer_rate_exceeds_entropy hv0 hv)
  intro k S hS
  have hcard : S.card = k := (hshell k S hS).2
  have := mayerActivity_exp_decay (V := V) (v := v) (S := S) hV hv0 (by linarith)
  rw [hcard] at this
  simpa using this

/-! ## 7. The threshold in the coupling -/

/-- **Smallness of the bare coupling suffices.**  If the per-constituent
interaction is `g²·W` with `|W| ≤ w`, then `g² ≤ 1/(400 w)` puts the interaction
below the four-dimensional threshold, hence produces a decay rate strictly above
the proved lattice entropy rate. -/
theorem smallCoupling_mayer_threshold {W : ι → ℝ} {g w : ℝ}
    (hW : ∀ p, |W p| ≤ w) (hw : 0 < w) (hg : 0 < g) (hgw : g ^ 2 ≤ 1 / (400 * w)) :
    (∀ p, |g ^ 2 * W p| ≤ g ^ 2 * w) ∧ g ^ 2 * w ≤ 1 / 400 := by
  refine ⟨fun p => ?_, ?_⟩
  · rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < g ^ 2)]
    exact mul_le_mul_of_nonneg_left (hW p) (by positivity)
  · have h : g ^ 2 * w ≤ (1 / (400 * w)) * w :=
      mul_le_mul_of_nonneg_right hgw hw.le
    have : (1 / (400 * w)) * w = 1 / 400 := by field_simp
    linarith [h, this.le, this.ge]

end YangMills
