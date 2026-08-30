/-
**G9.1 / G9.2 evaluated on the actual centred grid family — a negative verdict.**

`TransverseDerivative.lean` proves that the anchored determinant only sees the
displacement *modulo the anchor line*, and that the ledger of
`AnchoredShiftLedger.lean` may therefore be driven by the transverse constant
`M⊥` rather than the raw shift constant `M`.  G9 asks whether that substitution
buys a power of `L`: is `k⊥ ≤ 1` even though `k = 2`?

This file answers that for the family the source actually uses — translates of a
*real even* profile sampled on a *centred* grid `{-mh, …, -h, 0, h, …, mh}` — and
the answer is **no**:

* `sum_odd_centredGrid` — an odd function summed over a centred grid vanishes;
* `inner_centredGrid_deriv_eq_zero` — hence for an even profile with odd
  derivative the anchor is already orthogonal to its own derivative,

      `⟪V(0), V'(0)⟫ = 0`;

* `transverseComp_eq_self_of_inner_zero`, `centredGrid_transverse_eq_full` —
  therefore the transverse projection removes *nothing*:

      `‖P_{V(0)^⊥} V'(0)‖ = ‖V'(0)‖`,   `wedgeSq (V 0) (V' 0) = ‖V 0‖²‖V' 0‖²`.

  So `k⊥ = k` exactly: the hoped-for extra power of `L` is not there for the
  centred even family.  (This is not a defect of an estimate; it is an identity.)

* `transverseLipschitz_ge_transverseDerivative` — and the ledger consequence,
  proved from the differential anchored minor: *any* admissible transverse
  constant `M` in `‖v_s − v₀‖`-type budgets is at least the transverse derivative
  norm.  Combined with the previous item, `M ≥ ‖V'(0)‖`.

* `transverse_lane_closed_of_relative_derivative` — the source-scale reading: if
  the anchor energy is `≍ L²` and the family moves at relative rate `≍ L`
  (spacing and profile width both `≍ 1/L`), then every admissible constant obeys
  `M ≥ c·L²`, i.e. `k ≥ 2`, and the `k ≤ 1` branch of the ledger — the only
  branch that produced `o(L⁶)` — is unavailable for this family.

The Gaussian model of the profile is carried along explicitly
(`gaussProfile`, `hasDerivAt_gaussProfile`, `gaussGrid_wedge_eq_weightedVariance`)
so that the identities above are exhibited on a family for which every quantity
is computable: the transverse energy is exactly `σ^{-4}` times the *weighted
variance of the node positions*, and it degenerates only when that variance
does — i.e. only when the taper sees a single grid node.

Nothing here refers to `ζ`; nothing here is assumed.
-/
import RiemannAnalytic.TransverseDerivative

namespace RiemannAnalytic

open Finset

open scoped InnerProductSpace

/-! ### Coordinate vectors as elements of a Euclidean space -/

/-- A coordinate vector, read in the Euclidean inner-product space. -/
noncomputable def euc {d : ℕ} (x : Fin d → ℝ) : EuclideanSpace ℝ (Fin d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm x

theorem inner_euc {d : ℕ} (x y : Fin d → ℝ) : ⟪euc x, euc y⟫_ℝ = ∑ i, x i * y i := by
  rw [PiLp.inner_apply]
  simp [euc, RCLike.inner_apply, mul_comm]

theorem norm_euc_sq {d : ℕ} (x : Fin d → ℝ) : ‖euc x‖ ^ 2 = ∑ i, x i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_euc]
  exact Finset.sum_congr rfl fun i _ => (sq (x i)).symm

/-- The wedge of two coordinate vectors, in coordinates. -/
theorem wedgeSq_euc {d : ℕ} (x y : Fin d → ℝ) :
    wedgeSq (euc x) (euc y)
      = (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 := by
  unfold wedgeSq
  rw [norm_euc_sq, norm_euc_sq, inner_euc]

/-! ### The centred grid, and odd sums over it -/

/-- The signed index of the centred grid `{-m, …, m}` of `2m+1` nodes. -/
def centredIndex (m : ℕ) (i : Fin (2 * m + 1)) : ℝ := ((i : ℕ) : ℝ) - (m : ℝ)

theorem centredIndex_rev (m : ℕ) (i : Fin (2 * m + 1)) :
    centredIndex m i.rev = -centredIndex m i := by
  unfold centredIndex
  have hi : (i : ℕ) < 2 * m + 1 := i.isLt
  have hrev : ((i.rev : ℕ) : ℝ) = (2 * m : ℝ) - ((i : ℕ) : ℝ) := by
    have : (i.rev : ℕ) = 2 * m - (i : ℕ) := by
      simp [Fin.val_rev]
    rw [this]
    have hle : (i : ℕ) ≤ 2 * m := by omega
    rw [Nat.cast_sub hle]
    push_cast
    ring
  rw [hrev]
  ring

/-- **An odd function of the node position sums to zero over a centred grid.** -/
theorem sum_odd_centredGrid (m : ℕ) (g : ℝ → ℝ) (hg : ∀ x, g (-x) = -g x) :
    ∑ i : Fin (2 * m + 1), g (centredIndex m i) = 0 := by
  have hbij : ∑ i : Fin (2 * m + 1), g (centredIndex m i)
      = ∑ i : Fin (2 * m + 1), g (centredIndex m i.rev) :=
    (Fintype.sum_bijective Fin.rev Fin.rev_bijective _ _ fun i => rfl).symm
  have hneg : ∑ i : Fin (2 * m + 1), g (centredIndex m i.rev)
      = -∑ i : Fin (2 * m + 1), g (centredIndex m i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [centredIndex_rev, hg]
  have := hbij.trans hneg
  linarith

/-! ### The centred grid family of translates of an even profile -/

/-- The window vector of the centred grid: coordinate `i` is the profile
evaluated at the node `τ − (i−m)h`. -/
noncomputable def centredGridVec (F : ℝ → ℝ) (h τ : ℝ) (m : ℕ) :
    EuclideanSpace ℝ (Fin (2 * m + 1)) :=
  euc fun i => F (τ - centredIndex m i * h)

/-- Its coordinatewise derivative in `τ`. -/
noncomputable def centredGridDeriv (F' : ℝ → ℝ) (h τ : ℝ) (m : ℕ) :
    EuclideanSpace ℝ (Fin (2 * m + 1)) :=
  euc fun i => F' (τ - centredIndex m i * h)

/-- **The anchor of a centred even family is orthogonal to its own derivative.**
At the anchor `τ = 0`, with `F` even and `F'` odd, `⟪V(0), V'(0)⟫ = 0`. -/
theorem inner_centredGrid_deriv_eq_zero (F F' : ℝ → ℝ) (h : ℝ) (m : ℕ)
    (hFe : ∀ x, F (-x) = F x) (hFo : ∀ x, F' (-x) = -F' x) :
    ⟪centredGridVec F h 0 m, centredGridDeriv F' h 0 m⟫_ℝ = 0 := by
  unfold centredGridVec centredGridDeriv
  rw [inner_euc]
  have hg : ∀ x : ℝ, (fun y : ℝ => F (0 - y * h) * F' (0 - y * h)) (-x)
      = -(fun y : ℝ => F (0 - y * h) * F' (0 - y * h)) x := by
    intro x
    have h1 : (0 : ℝ) - (-x) * h = -(0 - x * h) := by ring
    simp only [h1]
    rw [hFe, hFo]
    ring
  exact sum_odd_centredGrid m (fun y => F (0 - y * h) * F' (0 - y * h)) hg

/-! ### Orthogonality kills the transverse gain -/

/-- If the motion is already orthogonal to the anchor, the transverse projection
is the identity. -/
theorem transverseComp_eq_self_of_inner_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x w : E) (h : ⟪x, w⟫_ℝ = 0) : transverseComp x w = w := by
  unfold transverseComp
  rw [h]
  simp

/-- **`k⊥ = k` for the centred even family.**  The transverse derivative is the
full derivative: passing from the raw shift constant to the transverse one saves
nothing at all. -/
theorem centredGrid_transverse_eq_full (F F' : ℝ → ℝ) (h : ℝ) (m : ℕ)
    (hFe : ∀ x, F (-x) = F x) (hFo : ∀ x, F' (-x) = -F' x) :
    ‖transverseComp (centredGridVec F h 0 m) (centredGridDeriv F' h 0 m)‖
      = ‖centredGridDeriv F' h 0 m‖ := by
  rw [transverseComp_eq_self_of_inner_zero _ _ (inner_centredGrid_deriv_eq_zero F F' h m hFe hFo)]

/-- … equivalently, the anchored determinant of the differential is the *full*
product of energies, with no Cauchy–Schwarz defect to exploit. -/
theorem centredGrid_wedge_eq_full (F F' : ℝ → ℝ) (h : ℝ) (m : ℕ)
    (hFe : ∀ x, F (-x) = F x) (hFo : ∀ x, F' (-x) = -F' x) :
    wedgeSq (centredGridVec F h 0 m) (centredGridDeriv F' h 0 m)
      = ‖centredGridVec F h 0 m‖ ^ 2 * ‖centredGridDeriv F' h 0 m‖ ^ 2 := by
  unfold wedgeSq
  rw [inner_centredGrid_deriv_eq_zero F F' h m hFe hFo]
  ring

/-! ### The ledger consequence -/

/-- **Any admissible transverse constant dominates the transverse derivative.**
If the anchored minors of a differentiable family obey the ledger hypothesis
`Δ(s) ≤ ‖V 0‖²M²s²` for all small `s ≠ 0`, then `M ≥ ‖P_{V0^⊥}V'(0)‖`.  So the
exponent in the ledger cannot be smaller than the transverse derivative scale. -/
theorem transverseLipschitz_ge_transverseDerivative {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (V : ℝ → E) (w : E) (M : ℝ) (hM : 0 ≤ M)
    (hV : HasDerivAt V w 0) (h0 : V 0 ≠ 0)
    (hbudget : ∀ᶠ s in nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ,
      ‖V 0‖ ^ 2 * ‖V s‖ ^ 2 - ⟪V 0, V s⟫_ℝ ^ 2 ≤ ‖V 0‖ ^ 2 * (M ^ 2 * s ^ 2)) :
    ‖transverseComp (V 0) w‖ ≤ M := by
  have hlim := differentialAnchorMinor V w hV
  have hbound : wedgeSq (V 0) w ≤ ‖V 0‖ ^ 2 * M ^ 2 := by
    refine le_of_tendsto hlim ?_
    filter_upwards [hbudget, self_mem_nhdsWithin] with s hs hs0
    have hs2 : (0 : ℝ) < s ^ 2 := by
      have : s ≠ 0 := by simpa using hs0
      positivity
    rw [div_le_iff₀ hs2]
    calc ‖V 0‖ ^ 2 * ‖V s‖ ^ 2 - ⟪V 0, V s⟫_ℝ ^ 2
        ≤ ‖V 0‖ ^ 2 * (M ^ 2 * s ^ 2) := hs
      _ = ‖V 0‖ ^ 2 * M ^ 2 * s ^ 2 := by ring
  rw [wedgeSq_eq_normSq_mul_transverseSq _ _ h0] at hbound
  have hx2 : (0 : ℝ) < ‖V 0‖ ^ 2 := by
    have : (0 : ℝ) < ‖V 0‖ := norm_pos_iff.2 h0
    positivity
  have hsq : ‖transverseComp (V 0) w‖ ^ 2 ≤ M ^ 2 :=
    le_of_mul_le_mul_left (by linarith : ‖V 0‖ ^ 2 * ‖transverseComp (V 0) w‖ ^ 2
      ≤ ‖V 0‖ ^ 2 * M ^ 2) hx2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hM two_ne_zero).1 hsq

/-- **The source-scale verdict.**  For a family whose anchor is orthogonal to its
derivative (the centred even case), whose anchor energy is at least `cv·L` in
norm and which moves at relative rate at least `c·L`, every admissible ledger
constant satisfies `M ≥ c·cv·L²`.  The `k ≤ 1` branch of
`AnchoredShiftLedger.anchored_shift_gain_of_short_window` — the only branch that
produced `o(L⁶)` — is therefore unavailable for this family. -/
theorem transverse_lane_closed_of_relative_derivative {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (V : ℝ → E) (w : E) {M c cv L : ℝ}
    (hM : 0 ≤ M) (hc : 0 ≤ c) (hL : 0 ≤ L)
    (hV : HasDerivAt V w 0) (h0 : V 0 ≠ 0)
    (hperp : ⟪V 0, w⟫_ℝ = 0)
    (hanchor : cv * L ≤ ‖V 0‖) (hrate : c * L * ‖V 0‖ ≤ ‖w‖)
    (hbudget : ∀ᶠ s in nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ,
      ‖V 0‖ ^ 2 * ‖V s‖ ^ 2 - ⟪V 0, V s⟫_ℝ ^ 2 ≤ ‖V 0‖ ^ 2 * (M ^ 2 * s ^ 2)) :
    c * cv * L ^ 2 ≤ M := by
  have hT := transverseLipschitz_ge_transverseDerivative V w M hM hV h0 hbudget
  rw [transverseComp_eq_self_of_inner_zero _ _ hperp] at hT
  have h1 : c * L * (cv * L) ≤ c * L * ‖V 0‖ :=
    mul_le_mul_of_nonneg_left hanchor (by positivity)
  have h2 : c * cv * L ^ 2 = c * L * (cv * L) := by ring
  linarith [hrate.trans hT]

/-! ### The Gaussian model: every quantity computable -/

/-- The Gaussian profile of width `σ`. -/
noncomputable def gaussProfile (σ x : ℝ) : ℝ := Real.exp (-(x ^ 2) / (2 * σ ^ 2))

theorem gaussProfile_even (σ x : ℝ) : gaussProfile σ (-x) = gaussProfile σ x := by
  unfold gaussProfile
  congr 1
  ring

theorem gaussProfile_pos (σ x : ℝ) : 0 < gaussProfile σ x := Real.exp_pos _

/-- Its derivative profile `−(x/σ²)·e^{−x²/2σ²}`, which is odd. -/
noncomputable def gaussDerivProfile (σ x : ℝ) : ℝ := -(x / σ ^ 2) * gaussProfile σ x

theorem gaussDerivProfile_odd (σ x : ℝ) :
    gaussDerivProfile σ (-x) = -gaussDerivProfile σ x := by
  unfold gaussDerivProfile
  rw [gaussProfile_even]
  ring

theorem hasDerivAt_gaussProfile (σ : ℝ) (hσ : σ ≠ 0) (x : ℝ) :
    HasDerivAt (gaussProfile σ) (gaussDerivProfile σ x) x := by
  have hbase : HasDerivAt (fun y : ℝ => -(y ^ 2) / (2 * σ ^ 2))
      (-(2 * x) / (2 * σ ^ 2)) x := by
    have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2)) (-(2 * x)) x := by
      simpa using ((hasDerivAt_pow 2 x).neg)
    simpa using h1.div_const (2 * σ ^ 2)
  have hcomp := (Real.hasDerivAt_exp (-(x ^ 2) / (2 * σ ^ 2))).comp x hbase
  have heq : Real.exp (-(x ^ 2) / (2 * σ ^ 2)) * (-(2 * x) / (2 * σ ^ 2))
      = gaussDerivProfile σ x := by
    unfold gaussDerivProfile gaussProfile
    field_simp
  rw [heq] at hcomp
  simpa [gaussProfile, Function.comp] using hcomp

/-- **The exact transverse energy of the Gaussian grid family: a weighted
variance of the node positions.**  With weights `w_i = F(a_i)²` and positions
`a_i`,

    `wedgeSq V V' = σ^{-4}·((∑ w)(∑ a²w) − (∑ a w)²)`,

the (unnormalised) variance of the node positions under the taper weights.  It
degenerates only when that variance does — i.e. only when the taper effectively
sees a single grid node. -/
theorem gaussGrid_wedge_eq_weightedVariance (σ h τ : ℝ) (m : ℕ) :
    wedgeSq (euc fun i : Fin (2 * m + 1) => gaussProfile σ (τ - centredIndex m i * h))
        (euc fun i : Fin (2 * m + 1) => gaussDerivProfile σ (τ - centredIndex m i * h))
      = (1 / σ ^ 4) *
          ((∑ i : Fin (2 * m + 1), gaussProfile σ (τ - centredIndex m i * h) ^ 2) *
            (∑ i : Fin (2 * m + 1), (τ - centredIndex m i * h) ^ 2 *
              gaussProfile σ (τ - centredIndex m i * h) ^ 2)
          - (∑ i : Fin (2 * m + 1), (τ - centredIndex m i * h) *
              gaussProfile σ (τ - centredIndex m i * h) ^ 2) ^ 2) := by
  rw [wedgeSq_euc]
  set a : Fin (2 * m + 1) → ℝ := fun i => τ - centredIndex m i * h with ha
  have hderiv : ∀ i, gaussDerivProfile σ (a i) ^ 2
      = (1 / σ ^ 4) * ((a i) ^ 2 * gaussProfile σ (a i) ^ 2) := by
    intro i
    unfold gaussDerivProfile
    rw [mul_pow, neg_pow]
    field_simp
  have hcross : ∀ i, gaussProfile σ (a i) * gaussDerivProfile σ (a i)
      = -(1 / σ ^ 2) * ((a i) * gaussProfile σ (a i) ^ 2) := by
    intro i
    unfold gaussDerivProfile
    field_simp
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hderiv i,
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hcross i,
    ← Finset.mul_sum, ← Finset.mul_sum]
  ring

end RiemannAnalytic
