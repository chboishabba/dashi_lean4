/-
**Q6 — the multiplicity lift: removing the factor `M` from the Gram budget.**

`GramBudgetTransport.lean` compares the zero-pair-indexed total with the
exterior observable of the assembled family and pays a worst-case factor:

    ∑_ρ m_ρ² Δ_ρ  ≤  M · e₂(G),      m_ρ² ≤ M.

That factor is an artefact of the indexing, not of the geometry.  Instead of
entering each zero's pair `(a_ρ, b_ρ)` once, enter it `m_ρ` times — put `m_ρ`
copies of `a_ρ` and `m_ρ` copies of `b_ρ` into the evaluation family.  Every one
of the `m_ρ²` cross pairs `(a_{ρ,i}, b_{ρ,j})` has *exactly* the same Gram
defect `Δ_ρ`, the same-type duplicate pairs contribute `0`, and all remaining
pairs contribute something nonnegative.  Hence, with no maximum-multiplicity
hypothesis whatever,

    ∑_ρ m_ρ² Δ_ρ  ≤  e₂(G^mult).

This is `sum_mult_sq_pairDefect_le_e2`, the main theorem of this file, together
with its consequences `weightedGramSum_le_e2_mult` (the same statement in the
`weightedGramSum` notation of `WeightedGramTarget.lean`, for a sub-family) and
`abs_offset_le_of_e2_mult_budget` (budget → tube, again with no `M`).

The lifted family is indexed by `MultIndex mult = Σ ρ, Fin (m ρ) × Bool`, whose
cardinality is `2 ∑_ρ m_ρ` — that is, twice the number of zeros *counted with
multiplicity*, which is exactly what Riemann–von Mangoldt counts.  So the
multiplicity ceases to be an external penalty and becomes ordinary cardinality
of the lifted family: `card_multIndex`.

Nothing here refers to `ζ`; the vectors, multiplicities and defects are
arbitrary.
-/
import RiemannAnalytic.GramBudgetTransport

namespace RiemannAnalytic

open Finset

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The lifted family -/

/-- The index type of the multiplicity-lifted evaluation family: for each zero
`ρ`, `m ρ` copies of each of its two vectors. -/
abbrev MultIndex {ι : Type*} (mult : ι → ℕ) := Σ _ρ : ι, Fin (mult _ρ) × Bool

/-- The multiplicity-lifted family: `m ρ` copies of `a ρ` and `m ρ` copies of
`b ρ`, for every `ρ`. -/
def multPairFamily {ι : Type*} (a b : ι → E) (mult : ι → ℕ) : MultIndex mult → E :=
  fun p => if p.2.2 then b p.1 else a p.1

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp] theorem multPairFamily_false {ι : Type*} (a b : ι → E) (mult : ι → ℕ) (ρ : ι)
    (i : Fin (mult ρ)) : multPairFamily a b mult ⟨ρ, (i, false)⟩ = a ρ := rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp] theorem multPairFamily_true {ι : Type*} (a b : ι → E) (mult : ι → ℕ) (ρ : ι)
    (i : Fin (mult ρ)) : multPairFamily a b mult ⟨ρ, (i, true)⟩ = b ρ := rfl

/-- The lifted family has `2 ∑_ρ m_ρ` members: twice the number of zeros counted
*with multiplicity*.  Multiplicity is cardinality of the lifted family, not an
external weight. -/
theorem card_multIndex {ι : Type*} [Fintype ι] (mult : ι → ℕ) :
    Fintype.card (MultIndex mult) = 2 * ∑ ρ : ι, mult ρ := by
  classical
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun ρ _ => by ring

/-! ### The lift theorem -/

/-- The pairwise defect of the lifted family at one zero: every cross pair
carries the full `Δ_ρ`. -/
private theorem fibre_double_sum_ge {ι : Type*} (a b : ι → E) (mult : ι → ℕ) (ρ : ι) :
    2 * (mult ρ : ℝ) ^ 2 * pairDefect a b ρ
      ≤ ∑ x : Fin (mult ρ) × Bool, ∑ y : Fin (mult ρ) × Bool,
          (‖multPairFamily a b mult ⟨ρ, x⟩‖ ^ 2 * ‖multPairFamily a b mult ⟨ρ, y⟩‖ ^ 2
            - ⟪multPairFamily a b mult ⟨ρ, x⟩, multPairFamily a b mult ⟨ρ, y⟩⟫_ℝ ^ 2) := by
  classical
  set v := multPairFamily a b mult with hv
  set D : MultIndex mult → MultIndex mult → ℝ :=
    fun p q => ‖v p‖ ^ 2 * ‖v q‖ ^ 2 - ⟪v p, v q⟫_ℝ ^ 2 with hD
  have hDnn : ∀ p q, 0 ≤ D p q := by
    intro p q
    have := sq_real_inner_le (v p) (v q)
    simp only [hD]
    linarith
  have hstep : ∀ i j : Fin (mult ρ),
      2 * pairDefect a b ρ
        ≤ ∑ ε : Bool, ∑ δ : Bool, D ⟨ρ, (i, ε)⟩ ⟨ρ, (j, δ)⟩ := by
    intro i j
    have hft : D ⟨ρ, (i, false)⟩ ⟨ρ, (j, true)⟩ = pairDefect a b ρ := by
      simp [hD, hv, pairDefect]
    have htf : D ⟨ρ, (i, true)⟩ ⟨ρ, (j, false)⟩ = pairDefect a b ρ := by
      simp only [hD, hv, multPairFamily_true, multPairFamily_false, pairDefect]
      rw [real_inner_comm (b ρ) (a ρ)]
      ring
    rw [Fintype.sum_bool (fun ε => ∑ δ : Bool, D ⟨ρ, (i, ε)⟩ ⟨ρ, (j, δ)⟩)]
    rw [Fintype.sum_bool (fun δ => D ⟨ρ, (i, true)⟩ ⟨ρ, (j, δ)⟩),
      Fintype.sum_bool (fun δ => D ⟨ρ, (i, false)⟩ ⟨ρ, (j, δ)⟩)]
    have h1 := hDnn ⟨ρ, (i, true)⟩ ⟨ρ, (j, true)⟩
    have h2 := hDnn ⟨ρ, (i, false)⟩ ⟨ρ, (j, false)⟩
    rw [hft] at *
    rw [htf] at *
    linarith
  have hij : ∑ i : Fin (mult ρ), ∑ j : Fin (mult ρ), (2 * pairDefect a b ρ)
      ≤ ∑ i : Fin (mult ρ), ∑ j : Fin (mult ρ), ∑ ε : Bool, ∑ δ : Bool,
          D ⟨ρ, (i, ε)⟩ ⟨ρ, (j, δ)⟩ :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hstep i j
  have hcount : ∑ i : Fin (mult ρ), ∑ j : Fin (mult ρ), (2 * pairDefect a b ρ)
      = 2 * (mult ρ : ℝ) ^ 2 * pairDefect a b ρ := by
    simp [Finset.sum_const, sq]
    ring
  -- reassociate the four-fold sum into the two `Fin × Bool` sums
  have hreassoc : ∑ x : Fin (mult ρ) × Bool, ∑ y : Fin (mult ρ) × Bool, D ⟨ρ, x⟩ ⟨ρ, y⟩
      = ∑ i : Fin (mult ρ), ∑ ε : Bool, ∑ j : Fin (mult ρ), ∑ δ : Bool,
          D ⟨ρ, (i, ε)⟩ ⟨ρ, (j, δ)⟩ := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun ε _ => ?_
    rw [Fintype.sum_prod_type]
  have hswap : ∑ i : Fin (mult ρ), ∑ ε : Bool, ∑ j : Fin (mult ρ), ∑ δ : Bool,
        D ⟨ρ, (i, ε)⟩ ⟨ρ, (j, δ)⟩
      = ∑ i : Fin (mult ρ), ∑ j : Fin (mult ρ), ∑ ε : Bool, ∑ δ : Bool,
          D ⟨ρ, (i, ε)⟩ ⟨ρ, (j, δ)⟩ := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  calc 2 * (mult ρ : ℝ) ^ 2 * pairDefect a b ρ
      = ∑ i : Fin (mult ρ), ∑ j : Fin (mult ρ), (2 * pairDefect a b ρ) := hcount.symm
    _ ≤ _ := hij
    _ = ∑ x : Fin (mult ρ) × Bool, ∑ y : Fin (mult ρ) × Bool, D ⟨ρ, x⟩ ⟨ρ, y⟩ := by
        rw [hreassoc, hswap]

/-- **The multiplicity lift (Q6).**  With `m_ρ` copies of each of the two
vectors of the zero `ρ` in the evaluation family, the weighted transverse-area
total is dominated by the exterior observable of the lifted family, with **no
maximum-multiplicity factor**:

    ∑_ρ m_ρ² Δ_ρ  ≤  e₂(G^mult).

Compare `weightedGramSum_le_e2`, which pays a factor `M ≥ max m_ρ²`. -/
theorem sum_mult_sq_pairDefect_le_e2 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → E) (mult : ι → ℕ) :
    ∑ ρ : ι, (mult ρ : ℝ) ^ 2 * pairDefect a b ρ
      ≤ e2OfTraces (Matrix.gram ℝ (multPairFamily a b mult)).trace
          ((Matrix.gram ℝ (multPairFamily a b mult)
            * Matrix.gram ℝ (multPairFamily a b mult)).trace) := by
  classical
  set v := multPairFamily a b mult with hv
  set D : MultIndex mult → MultIndex mult → ℝ :=
    fun p q => ‖v p‖ ^ 2 * ‖v q‖ ^ 2 - ⟪v p, v q⟫_ℝ ^ 2 with hD
  have hDnn : ∀ p q, 0 ≤ D p q := by
    intro p q
    have := sq_real_inner_le (v p) (v q)
    simp only [hD]
    linarith
  rw [e2OfTraces_gram_eq v]
  have hsigma : ∑ p : MultIndex mult, ∑ q : MultIndex mult, D p q
      = ∑ ρ : ι, ∑ x : Fin (mult ρ) × Bool, ∑ σ : ι, ∑ y : Fin (mult σ) × Bool,
          D ⟨ρ, x⟩ ⟨σ, y⟩ := by
    rw [Fintype.sum_sigma (fun p => ∑ q : MultIndex mult, D p q)]
    refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun x _ => ?_
    exact Fintype.sum_sigma (fun q => D ⟨ρ, x⟩ q)
  have hdrop : ∀ ρ : ι, ∀ x : Fin (mult ρ) × Bool,
      ∑ y : Fin (mult ρ) × Bool, D ⟨ρ, x⟩ ⟨ρ, y⟩
        ≤ ∑ σ : ι, ∑ y : Fin (mult σ) × Bool, D ⟨ρ, x⟩ ⟨σ, y⟩ := by
    intro ρ x
    refine Finset.single_le_sum
      (f := fun σ : ι => ∑ y : Fin (mult σ) × Bool, D ⟨ρ, x⟩ ⟨σ, y⟩) ?_ (Finset.mem_univ ρ)
    intro σ _
    exact Finset.sum_nonneg fun y _ => hDnn _ _
  have hkey : ∑ ρ : ι, (2 * (mult ρ : ℝ) ^ 2 * pairDefect a b ρ)
      ≤ ∑ p : MultIndex mult, ∑ q : MultIndex mult, D p q := by
    rw [hsigma]
    refine Finset.sum_le_sum fun ρ _ => ?_
    refine le_trans (fibre_double_sum_ge a b mult ρ) ?_
    exact Finset.sum_le_sum fun x _ => hdrop ρ x
  have hlhs : ∑ ρ : ι, (2 * (mult ρ : ℝ) ^ 2 * pairDefect a b ρ)
      = 2 * ∑ ρ : ι, (mult ρ : ℝ) ^ 2 * pairDefect a b ρ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ρ _ => by ring
  rw [hlhs] at hkey
  have hDsum : ∑ p : MultIndex mult, ∑ q : MultIndex mult, D p q
      = ∑ p : MultIndex mult, ∑ q : MultIndex mult, (‖v p‖ ^ 2 * ‖v q‖ ^ 2 - ⟪v p, v q⟫_ℝ ^ 2) :=
    rfl
  rw [hDsum] at hkey
  linarith

/-! ### Consequences -/

/-- **The weighted Gram sum against the lifted exterior observable.**  For a
sub-family `s` of zeros with natural-number multiplicities, the weighted budget
of `WeightedGramTarget.lean` is at most the exterior observable of the lifted
family — no factor `M`. -/
theorem weightedGramSum_le_e2_mult {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → E) (mult : ι → ℕ) (s : Finset ι) :
    weightedGramSum s (fun ρ => (mult ρ : ℝ)) (pairDefect a b)
      ≤ e2OfTraces (Matrix.gram ℝ (multPairFamily a b mult)).trace
          ((Matrix.gram ℝ (multPairFamily a b mult)
            * Matrix.gram ℝ (multPairFamily a b mult)).trace) := by
  classical
  refine le_trans ?_ (sum_mult_sq_pairDefect_le_e2 a b mult)
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun ρ _ _ => ?_
  exact mul_nonneg (sq_nonneg _) (pairDefect_nonneg a b ρ)

/-- **Budget to tube, without a multiplicity ceiling.**  If every zero pair obeys
the quadratic floor `c α_ρ² ≤ Δ_ρ`, every multiplicity is at least one, and the
*lifted* exterior observable obeys the budget `E`, then every transverse offset
lies in the tube `|α_ρ| ≤ √(E/c)`. -/
theorem abs_offset_le_of_e2_mult_budget {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → E) {s : Finset ι} {mult : ι → ℕ} {offset : ι → ℝ} {c Ebudget : ℝ} (hc : 0 < c)
    (hfloor : ∀ ρ ∈ s, c * offset ρ ^ 2 ≤ pairDefect a b ρ)
    (hm1 : ∀ ρ ∈ s, 1 ≤ mult ρ)
    (hbudget : e2OfTraces (Matrix.gram ℝ (multPairFamily a b mult)).trace
        ((Matrix.gram ℝ (multPairFamily a b mult)
          * Matrix.gram ℝ (multPairFamily a b mult)).trace) ≤ Ebudget)
    {ρ : ι} (hρ : ρ ∈ s) :
    |offset ρ| ≤ Real.sqrt (Ebudget / c) := by
  classical
  have hle : weightedGramSum s (fun σ => (mult σ : ℝ)) (pairDefect a b) ≤ Ebudget :=
    le_trans (weightedGramSum_le_e2_mult a b mult s) hbudget
  refine abs_offset_le_of_budget hc hfloor ?_ hle hρ
  intro σ hσ
  have h1 : (1 : ℝ) ≤ (mult σ : ℝ) := by exact_mod_cast hm1 σ hσ
  nlinarith

end RiemannAnalytic
