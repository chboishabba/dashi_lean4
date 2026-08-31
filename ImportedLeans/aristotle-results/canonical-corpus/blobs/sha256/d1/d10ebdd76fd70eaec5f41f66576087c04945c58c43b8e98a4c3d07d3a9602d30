import Mathlib
import Integration.Variation.Pairing
import Integration.Variation.CommonLanguage
import Integration.Variation.Weld

/-!
# QFT/GR reconciliation — the Agda boundary ledgers as Lean propositions

Two modules of the Agda snapshot carry the QFT/GR common-action frontier as
`Bool` **boundary records**, each field pinned by a propositional equality:

* `DASHI.Physics.Foundations.EinsteinCommonActionVariationFrontierExact`
  (`EinsteinVariationBoundary`) pins
  `fieldEquationAloneDerivesCommonAction ≡ false`,
  `tensorNameAloneDeterminesMetricVariationFunctional ≡ false`,
  `equalityOfPairingsImpliesTensorEqualityWithoutSeparationTheorem ≡ false`,
  `commonMetricVariationEqualsEinsteinPairingIsStillPhysicalTheorem ≡ true`,
  `einsteinVariationPlusSeparationPlusFieldEquationBuildsGRSource ≡ true`;
* `DASHI.Physics.Foundations.CommonEffectiveActionVariationExact`
  (`CommonActionVariationBoundary`) pins
  `finiteAdditiveNatActionDefinesMetricFunctionalDerivative ≡ false`,
  `actionPhaseLiftDefinesStressTensor ≡ false`,
  `separatelyNamedGRAndQFTActionsAreOneCommonAction ≡ false`,
  `commonVariationPlusLiteralIdentificationsClosesStressWeld ≡ true`.

A `Bool` field pinned by `refl` is a **ledger entry**, not a theorem: it records
an intended reading, but the claim it names is not stated as a proposition about
any variational machinery, so nothing is proved or refuted by the pinning.

The same Agda development also carries an `EinsteinTensorVariationReceipt`
record whose field

```
pairingSeparatesStressOnAdmittedDomain :
  ∀ candidate regime left right →
  (∀ perturbation → AdmissibleMetricPerturbation … →
     stressMetricPairing left perturbation ≡ stressMetricPairing right perturbation) →
  left ≡ right
```

is *assumed*.  On the Lean side that exact hypothesis is a theorem with a sharp
characterisation: over a complete inner-product space it holds for an admitted
fibre `K` if and only if `K` is dense (`Pairing.separates_iff_dense`).  This is
the single most load-bearing reconciliation point between the two languages.

## What this module does

Each ledger entry that has a faithful rendering against the Lean variational
model is written out as a proposition:

* `falseClaim` — the six `false`-pinned entries, each **refuted**
  (`pinned_false_entries_are_refuted`);
* `trueContent` — the three `true`-pinned entries, each given a **proved**
  generic Lean statement (`pinned_true_entries_have_generic_content`).

Two of the six negatives are new here (`finiteAdditiveNatAction…`, via
`natValued_hasDerivAt_eq_zero`, and `actionPhaseLift…`); the other four are
discharged from the existing variation lanes.

## Reading discipline

This is a statement about the Lean development only.  No Agda module is
typechecked, no Agda proof term is transported, and nothing here asserts that
the physical hypotheses (a genuine common action, a genuine dense admitted
fibre of symmetric metric perturbations, genuine sector convergence) hold for
any physical theory.  What is shown is that the Agda ledger's intended readings
are, in the Lean model, theorems rather than declarations.
-/

namespace Integration.Reconciliation.QFTGRBoundary

open scoped InnerProductSpace RealInnerProductSpace
open Filter
open Integration.Variation
open Integration.Variation.Pairing

/-! ### A discrete action has no functional derivative -/

/-- **A `ℕ`-valued action has no nonzero derivative.**  If a real function that
only takes natural-number values is differentiable at a point, its derivative
there is `0`.  So a finite additive counting action cannot, by itself, define a
nonzero metric functional derivative: the pairing it would represent is the zero
tensor. -/
theorem natValued_hasDerivAt_eq_zero (A : ℝ → ℕ) (T t : ℝ)
    (h : HasDerivAt (fun s => (A s : ℝ)) T t) : T = 0 := by
  by_contra hT
  have hTpos : 0 < |T| := abs_pos.mpr hT
  have hev := h.isLittleO.def (c := |T| / 2) (by positivity)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  set r := min (δ / 2) (1 / (2 * |T|)) with hr
  have hrpos : 0 < r := by apply lt_min <;> positivity
  have hrδ : r < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hdist : dist (t + r) t < δ := by simp [abs_of_pos hrpos, hrδ]
  have hkey := hball hdist
  simp only [Real.norm_eq_abs, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
    add_sub_cancel_left, abs_of_pos hrpos] at hkey
  have h3 : |r * T| = r * |T| := by rw [abs_mul, abs_of_pos hrpos]
  have h2 : |(A (t + r) : ℝ) - (A t : ℝ)| - |r * T| ≤ |(A (t + r) : ℝ) - (A t : ℝ) - r * T| :=
    abs_sub_abs_le_abs_sub _ _
  have hbound : |(A (t + r) : ℝ) - (A t : ℝ)| ≤ |T| * r + (|T| / 2) * r := by
    nlinarith [hkey, h3, h2]
  have hlt1 : |(A (t + r) : ℝ) - (A t : ℝ)| < 1 := by
    have hrle : r ≤ 1 / (2 * |T|) := min_le_right _ _
    have hmul : (3 / 2) * |T| * r ≤ (3 / 2) * |T| * (1 / (2 * |T|)) :=
      mul_le_mul_of_nonneg_left hrle (by positivity)
    have hcalc : (3 / 2) * |T| * (1 / (2 * |T|)) = 3 / 4 := by field_simp; ring
    nlinarith [hbound]
  have hstrict := abs_lt.mp hlt1
  have heq : A (t + r) = A t := by
    by_contra hne
    rcases Nat.lt_or_ge (A (t + r)) (A t) with hlt | hge
    · have hc : (A (t + r) : ℝ) + 1 ≤ (A t : ℝ) := by exact_mod_cast hlt
      linarith [hstrict.1]
    · have hgt : A t < A (t + r) := lt_of_le_of_ne hge (Ne.symm hne)
      have hc : (A t : ℝ) + 1 ≤ (A (t + r) : ℝ) := by exact_mod_cast hgt
      linarith [hstrict.2]
  rw [heq] at hkey
  simp only [sub_self, zero_sub, abs_neg, h3] at hkey
  nlinarith [hkey, hrpos, hTpos]

/-- **The phase lift does not determine the action.**  `S ↦ exp(i S)` is not
injective, so an action recovered from its phase lift is only determined modulo
`2π`: the lift alone names no functional to vary. -/
theorem phaseLift_not_injective :
    ∃ A B : ℝ → ℝ,
      (∀ x, Complex.exp (Complex.I * (A x : ℂ)) = Complex.exp (Complex.I * (B x : ℂ))) ∧
        A ≠ B := by
  refine ⟨fun _ => 0, fun _ => 2 * Real.pi, fun x => ?_, ?_⟩
  · have : (Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 2 * Real.pi * Complex.I := by
      push_cast; ring
    rw [this]
    simp [Complex.exp_two_pi_mul_I]
  · intro hc
    have := congrFun hc 0
    simp only at this
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    linarith

/-! ### The `false`-pinned entries -/

/-- The six `false`-pinned boundary entries of the two Agda records. -/
inductive PinnedFalse
  /-- `EinsteinVariationBoundary.fieldEquationAloneDerivesCommonAction`. -/
  | fieldEquationAloneDerivesCommonAction
  /-- `EinsteinVariationBoundary.tensorNameAloneDeterminesMetricVariationFunctional`. -/
  | tensorNameAloneDeterminesMetricVariationFunctional
  /-- `EinsteinVariationBoundary.equalityOfPairingsImpliesTensorEqualityWithoutSeparationTheorem`. -/
  | equalityOfPairingsImpliesTensorEqualityWithoutSeparationTheorem
  /-- `CommonActionVariationBoundary.finiteAdditiveNatActionDefinesMetricFunctionalDerivative`. -/
  | finiteAdditiveNatActionDefinesMetricFunctionalDerivative
  /-- `CommonActionVariationBoundary.actionPhaseLiftDefinesStressTensor`. -/
  | actionPhaseLiftDefinesStressTensor
  /-- `CommonActionVariationBoundary.separatelyNamedGRAndQFTActionsAreOneCommonAction`. -/
  | separatelyNamedGRAndQFTActionsAreOneCommonAction
  deriving DecidableEq, Repr

/-- Each `false`-pinned entry, written out as a proposition about the Lean
variational model rather than as a `Bool`. -/
def falseClaim : PinnedFalse → Prop
  | .fieldEquationAloneDerivesCommonAction =>
      ∀ (iotaGR iotaQFT dGR dQFT : ℝ →ₗ[ℝ] ℝ) (G T : ℝ),
        (∀ h : ℝ, dGR h = pair G (iotaGR h)) →
        (∀ h : ℝ, dQFT h = pair T (iotaQFT h)) →
        G = T → dGR = dQFT
  | .tensorNameAloneDeterminesMetricVariationFunctional =>
      ∀ (iotaGR iotaQFT : ℝ →ₗ[ℝ] ℝ) (K : Submodule ℝ ℝ) (d : ℝ →ₗ[ℝ] ℝ) (G T : ℝ),
        K = ⊤ →
        (∀ h ∈ K, d h = pair G (iotaGR h)) →
        (∀ h ∈ K, d h = pair T (iotaQFT h)) →
        Submodule.span ℝ (iotaGR '' K) = ⊤ → G = T
  | .equalityOfPairingsImpliesTensorEqualityWithoutSeparationTheorem =>
      ∀ (A B : EuclideanSpace ℝ (Fin 2)) (S : Set (EuclideanSpace ℝ (Fin 2))),
        (∀ v ∈ S, pair A v = pair B v) → A = B
  | .finiteAdditiveNatActionDefinesMetricFunctionalDerivative =>
      ∃ (A : ℝ → ℕ) (T t : ℝ), T ≠ 0 ∧ HasDerivAt (fun s => (A s : ℝ)) T t
  | .actionPhaseLiftDefinesStressTensor =>
      ∀ A B : ℝ → ℝ,
        (∀ x, Complex.exp (Complex.I * (A x : ℂ)) = Complex.exp (Complex.I * (B x : ℂ))) →
        A = B
  | .separatelyNamedGRAndQFTActionsAreOneCommonAction =>
      ∀ (dGR dQFT : ℝ →ₗ[ℝ] ℝ) (G T : ℝ),
        (∀ h : ℝ, dGR h = pair G h) → (∀ h : ℝ, dQFT h = pair T h) → G = T

/-- **All six `false`-pinned entries are refuted.**  The Agda records pin each
of them to `false` by `refl`; here each is stated against the variational model
and shown to fail. -/
theorem pinned_false_entries_are_refuted : ∀ c : PinnedFalse, ¬ falseClaim c := by
  intro c
  cases c with
  | fieldEquationAloneDerivesCommonAction =>
      intro hall
      simp only [falseClaim] at hall
      have hbad := hall LinearMap.id ((2 : ℝ) • LinearMap.id) LinearMap.id
        ((2 : ℝ) • LinearMap.id) 1 1
        (fun h => by simp [pair, RCLike.inner_apply])
        (fun h => by simp [pair, RCLike.inner_apply]) rfl
      have := congrArg (fun f : ℝ →ₗ[ℝ] ℝ => f 1) hbad
      norm_num at this
  | tensorNameAloneDeterminesMetricVariationFunctional =>
      intro hall
      simp only [falseClaim] at hall
      obtain ⟨iGR, iQFT, K, d, G, T, hK, hG, hT, hspan, hne⟩ :=
        CommonLanguage.mismatched_carrier_maps_do_not_weld
      exact hne (hall iGR iQFT K d G T hK hG hT hspan)
  | equalityOfPairingsImpliesTensorEqualityWithoutSeparationTheorem =>
      intro hall
      simp only [falseClaim] at hall
      obtain ⟨A, B, hAB, hagree⟩ := Pairing.plane_pairing_does_not_separate
      exact hAB (hall A B _ hagree)
  | finiteAdditiveNatActionDefinesMetricFunctionalDerivative =>
      intro hex
      simp only [falseClaim] at hex
      obtain ⟨A, T, t, hT, hderiv⟩ := hex
      exact hT (natValued_hasDerivAt_eq_zero A T t hderiv)
  | actionPhaseLiftDefinesStressTensor =>
      intro hall
      simp only [falseClaim] at hall
      obtain ⟨A, B, hphase, hne⟩ := phaseLift_not_injective
      exact hne (hall A B hphase)
  | separatelyNamedGRAndQFTActionsAreOneCommonAction =>
      intro hall
      simp only [falseClaim] at hall
      obtain ⟨dGR, dQFT, G, T, hG, hT, hne⟩ :=
        CommonLanguage.separate_actions_do_not_weld
      exact hne (hall dGR dQFT G T hG hT)

/-! ### The `true`-pinned entries -/

/-- The three `true`-pinned boundary entries of the two Agda records. -/
inductive PinnedTrue
  /-- `EinsteinVariationBoundary.commonMetricVariationEqualsEinsteinPairingIsStillPhysicalTheorem`. -/
  | commonMetricVariationEqualsEinsteinPairingIsStillPhysicalTheorem
  /-- `EinsteinVariationBoundary.einsteinVariationPlusSeparationPlusFieldEquationBuildsGRSource`. -/
  | einsteinVariationPlusSeparationPlusFieldEquationBuildsGRSource
  /-- `CommonActionVariationBoundary.commonVariationPlusLiteralIdentificationsClosesStressWeld`. -/
  | commonVariationPlusLiteralIdentificationsClosesStressWeld
  deriving DecidableEq, Repr

/-- For each `true`-pinned entry, the generic statement the Lean development
actually proves.

The first is the reconciliation point for the Agda receipt's *assumed* field
`pairingSeparatesStressOnAdmittedDomain`: in Lean the separation property is not
assumed but characterised — it holds exactly for a dense admitted fibre.  So the
Agda assumption is a genuine physical hypothesis about the admitted
perturbations, and the Lean side says precisely which one. -/
def trueContent : PinnedTrue → Prop
  | .commonMetricVariationEqualsEinsteinPairingIsStillPhysicalTheorem =>
      ∀ K : Submodule ℝ (EuclideanSpace ℝ (Fin 2)),
        (∀ A B : EuclideanSpace ℝ (Fin 2), (∀ v ∈ K, pair A v = pair B v) → A = B)
          ↔ Dense (K : Set (EuclideanSpace ℝ (Fin 2)))
  | .einsteinVariationPlusSeparationPlusFieldEquationBuildsGRSource =>
      ∀ (iota : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
        (K : Submodule ℝ (EuclideanSpace ℝ (Fin 2)))
        (d : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ) (G T : EuclideanSpace ℝ (Fin 2)),
        (∀ h ∈ K, d h = pair G (iota h)) →
        (∀ h ∈ K, d h = pair T (iota h)) →
        Dense (Submodule.span ℝ (iota '' K) : Set (EuclideanSpace ℝ (Fin 2))) →
        G = T
  | .commonVariationPlusLiteralIdentificationsClosesStressWeld =>
      ∀ (s : Finset ℕ) (K : Submodule ℝ (EuclideanSpace ℝ (Fin 2))),
        Dense (K : Set (EuclideanSpace ℝ (Fin 2))) →
        ∀ (deltaCommon : EuclideanSpace ℝ (Fin 2) → ℝ) (G : EuclideanSpace ℝ (Fin 2)),
        (∀ h ∈ K, deltaCommon h = pair G h) →
        ∀ (deltaSecK : ℕ → ℕ → EuclideanSpace ℝ (Fin 2) → ℝ)
          (T : ℕ → ℕ → EuclideanSpace ℝ (Fin 2)),
          (∀ i ∈ s, ∀ k h, deltaSecK i k h = pair (T i k) h) →
          ∀ deltaSecInf : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ,
            (∀ i ∈ s, ∀ h, Tendsto (fun k => deltaSecK i k h) atTop (nhds (deltaSecInf i h))) →
            (∀ h ∈ K, deltaCommon h = ∑ i ∈ s, deltaSecInf i h) →
            ∃ Tc : ℕ → EuclideanSpace ℝ (Fin 2),
              (∀ i ∈ s, ∀ h, deltaSecInf i h = pair (Tc i) h) ∧
                (∀ h ∈ K, deltaCommon h = pair (∑ i ∈ s, Tc i) h) ∧
                  G = ∑ i ∈ s, Tc i

/-- **Every `true`-pinned entry has a proved generic Lean statement.** -/
theorem pinned_true_entries_have_generic_content :
    ∀ e : PinnedTrue, trueContent e := by
  intro e
  cases e with
  | commonMetricVariationEqualsEinsteinPairingIsStillPhysicalTheorem =>
      simp only [trueContent]
      exact fun K => Pairing.separates_iff_dense K
  | einsteinVariationPlusSeparationPlusFieldEquationBuildsGRSource =>
      simp only [trueContent]
      exact fun iota K d G T hG hT hdense =>
        CommonLanguage.stress_weld_of_dense_carrier iota K d G T hG hT hdense
  | commonVariationPlusLiteralIdentificationsClosesStressWeld =>
      simp only [trueContent]
      exact fun s K hdense deltaCommon G hGR deltaSecK T hfin deltaSecInf hconv hagg =>
        Weld.qftgr_stress_weld_of_cutset s K hdense deltaCommon G hGR deltaSecK T hfin
          deltaSecInf hconv hagg

/-- **The QFT/GR ledger is discharged on the Lean side.**  Every `false`-pinned
entry is refuted and every `true`-pinned entry has proved generic content, so
each entry of the two Agda boundary records has, in the Lean model, a theorem
behind it rather than a `Bool`.

This says nothing about the *physical* frontier, which is untouched: the
Einstein–Hilbert curvature variation, the density of the physical fibre of
symmetric metric perturbations, and concrete cutoff estimates all remain
hypotheses here. -/
theorem qftgr_boundary_ledger_has_theorem_content :
    (∀ c : PinnedFalse, ¬ falseClaim c) ∧ (∀ e : PinnedTrue, trueContent e) :=
  ⟨pinned_false_entries_are_refuted, pinned_true_entries_have_generic_content⟩

end Integration.Reconciliation.QFTGRBoundary
