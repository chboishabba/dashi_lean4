/-
# Row A1a — the compiler from literal symbol data to the shell floor

Everything in the Row A1a lane now meets in one statement.  The producer's
obligation is stated purely in terms of the objects the Bałaban source defines:

* the substitution `C(q)` and its background derivative `C'(q)`,
* the Wilson Hessian `A(q)` and its background derivative `A'(q) = D³S`
  (`WilsonHessianFamily`),
* the pivot data `(E, P⁻¹, Q')` that *produces* `C'` (`ConnectionBudget`),

and the conclusion is the Row A1 shell floor `β_j ≥ b_patch/2 > 0`.

* `A1_halfFloor_from_symbolData` : Wilson-component floor `c` on the quarter
  slab plus a uniform connection entry bound `e`, history-uniform five-channel
  quartic control and the constructive coupling `γ_*` give
  `β_j ≥ ((δ/4)(c − 2e))/2 > 0`, uniformly in the shell index.
* `A1_halfFloor_from_pivotData` : the same with `e` *not* assumed but computed
  from the pivot solve, i.e. from `(‖C‖, ‖A‖, ‖E‖, ‖P⁻¹‖, ‖Q'‖)`.
* `candidatePatch_source_criterion` : at the project's candidate patch
  (half-width `1/8`, Wilson floor `√2/2`) the whole chain reduces to the single
  numerical inequality

      #c² · #n³ · b_C² · b_A · b_E · b_{P⁻¹} · b_{Q'}  <  √2/4.

**Honest status.**  The five source constants are still not computed for
Bałaban's construction, and neither is the Wilson floor, so the hypotheses of
these theorems are not discharged.  Row A1 does not close, and the frozen
research count is unchanged.  What is closed is that *nothing else* is needed:
one Wilson floor and five uniform source bounds suffice.
-/
import RequestProject.YangMills.WilsonHessianFamily

namespace YangMills

open Matrix Set MeasureTheory

variable {n m : Type*} [Fintype n]

/-- **The Row A1 floor from literal restricted-symbol data.**  The Gaussian
coefficient is the cell integral of the diagonal entry of the restricted symbol
`V = W + Q + R`; a Wilson floor `c` on a quarter slab, a uniform connection
budget `e`, and history-uniform quartic control give `β_j ≥ ((δ/4)(c−2e))/2`. -/
theorem A1_halfFloor_from_symbolData
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ} {Adm : (ℕ → ℝ) → Prop}
    {cch : BetaChannel → ℝ} {g : ℕ → ℝ}
    {I : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → ℝ}
    {Cf C'f : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → Matrix n m ℝ}
    {Af A'f : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → Matrix n n ℝ}
    (i : m) {cpatch e delta : ℝ}
    (rho : Fin 4) (hd0 : 0 < delta) (hd1 : delta < 1 / 4)
    (hpos : 0 < (delta / 4) * (cpatch - 2 * e))
    (hident : ∀ j h, Adm h → betaZ j h = cellGaussianCoefficient (I j h))
    (hI : ∀ j h q, I j h q =
      restrictedSymbol (Cf j h) (C'f j h) (Af j h) (A'f j h) q i i)
    (hsym : ∀ j h q, (Af j h q)ᵀ = Af j h q)
    (hint : ∀ j h, IntegrableOn (I j h) puncturedCell)
    (hnonneg : ∀ j h, ∀ q ∈ puncturedCell, 0 ≤ I j h q)
    (hW : ∀ j h, ∀ q ∈ quarterSlab rho delta,
      cpatch ≤ opVariation (Cf j h q) (A'f j h q) i i)
    (hconn : ∀ j h, ∀ q ∈ quarterSlab rho delta,
      |connectionRight (Cf j h q) (C'f j h q) (Af j h q) i i| ≤ e)
    (hsplit : ∀ j h, beta j h = betaZ j h + betaInt j h)
    (hquart : HistoryUniformQuartic betaInt Adm cch)
    (hc : ∀ k, 0 ≤ cch k) (hadm : Adm g) (hg0 : ∀ j, 0 ≤ g j)
    (hgg : ∀ j, g j ≤ criticalCoupling ((delta / 4) * (cpatch - 2 * e)) (Cbeta cch))
    (j : ℕ) :
    ((delta / 4) * (cpatch - 2 * e)) / 2 ≤ beta j g := by
  have hpatchI : ∀ j' h, ∀ q ∈ quarterSlab rho delta, cpatch - 2 * e ≤ I j' h q := by
    intro j' h q hq
    rw [hI j' h q]
    exact restrictedVariation_entry_lower_bound (Cf j' h q) (C'f j' h q) (hsym j' h q)
      (A'f j' h q) i (hW j' h q hq) (hconn j' h q hq)
  exact A1_halfFloor_from_restrictedPatch rho hd0 hd1 hpos hident hint hnonneg hpatchI
    hsplit hquart hc hadm hg0 hgg j

/-- **The Row A1 floor with the connection budget produced, not assumed.**  The
substitution derivative is the one the pivot solve computes from `Q'`, and its
contribution is bounded by the composite source budget. -/
theorem A1_halfFloor_from_pivotData
    {c : Type*} [Fintype c] [DecidableEq c]
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ} {Adm : (ℕ → ℝ) → Prop}
    {cch : BetaChannel → ℝ} {g : ℕ → ℝ}
    {I : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → ℝ}
    {Cfam : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → ℝ → Matrix n m ℝ}
    {Qfam : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → ℝ → Matrix c n ℝ}
    {C'f : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → Matrix n m ℝ}
    {Q'f : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → Matrix c n ℝ}
    {Ef : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → Matrix n c ℝ}
    {Xf : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → Matrix c m ℝ}
    {Pf Pinvf : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → Matrix c c ℝ}
    {Af A'f : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → Matrix n n ℝ}
    (i : m) {cpatch delta bC bA bE bPinv bQ' : ℝ}
    (rho : Fin 4) (hd0 : 0 < delta) (hd1 : delta < 1 / 4)
    (hpos : 0 < (delta / 4) *
      (cpatch - 2 * sourceConnectionBudget (Fintype.card c) (Fintype.card n)
        bC bA bE bPinv bQ'))
    (hident : ∀ j h, Adm h → betaZ j h = cellGaussianCoefficient (I j h))
    (hI : ∀ j h q, I j h q =
      restrictedSymbol (fun q' => Cfam j h q' 0) (C'f j h) (Af j h) (A'f j h) q i i)
    (hsym : ∀ j h q, (Af j h q)ᵀ = Af j h q)
    (hint : ∀ j h, IntegrableOn (I j h) puncturedCell)
    (hnonneg : ∀ j h, ∀ q ∈ puncturedCell, 0 ≤ I j h q)
    (hW : ∀ j h, ∀ q ∈ quarterSlab rho delta,
      cpatch ≤ opVariation (Cfam j h q 0) (A'f j h q) i i)
    -- the pivot solve, uniformly over shells, histories and momenta
    (hQd : ∀ j h q, HasMatDerivAt (Qfam j h q) (Q'f j h q) 0)
    (hCd : ∀ j h q, HasMatDerivAt (Cfam j h q) (C'f j h q) 0)
    (hconstr : ∀ j h q s, Qfam j h q s * Cfam j h q s = 0)
    (hsupp : ∀ j h q, C'f j h q = Ef j h q * Xf j h q)
    (hP : ∀ j h q, Qfam j h q 0 * Ef j h q = Pf j h q)
    (hPinv : ∀ j h q, Pinvf j h q * Pf j h q = 1)
    (hbC : ∀ j h q, EntryBound (Cfam j h q 0) bC)
    (hbA : ∀ j h q, EntryBound (Af j h q) bA)
    (hbE : ∀ j h q, EntryBound (Ef j h q) bE)
    (hbPi : ∀ j h q, EntryBound (Pinvf j h q) bPinv)
    (hbQ' : ∀ j h q, EntryBound (Q'f j h q) bQ')
    (h0 : 0 ≤ bC) (h1 : 0 ≤ bA) (h2 : 0 ≤ bE) (h3 : 0 ≤ bPinv) (h4 : 0 ≤ bQ')
    (hsplit : ∀ j h, beta j h = betaZ j h + betaInt j h)
    (hquart : HistoryUniformQuartic betaInt Adm cch)
    (hcc : ∀ k, 0 ≤ cch k) (hadm : Adm g) (hg0 : ∀ j, 0 ≤ g j)
    (hgg : ∀ j, g j ≤ criticalCoupling ((delta / 4) *
      (cpatch - 2 * sourceConnectionBudget (Fintype.card c) (Fintype.card n)
        bC bA bE bPinv bQ')) (Cbeta cch))
    (j : ℕ) :
    ((delta / 4) * (cpatch - 2 * sourceConnectionBudget (Fintype.card c) (Fintype.card n)
      bC bA bE bPinv bQ')) / 2 ≤ beta j g := by
  have hconn : ∀ j' h, ∀ q ∈ quarterSlab rho delta,
      |connectionRight (Cfam j' h q 0) (C'f j' h q) (Af j' h q) i i|
        ≤ sourceConnectionBudget (Fintype.card c) (Fintype.card n) bC bA bE bPinv bQ' := by
    intro j' h q _
    exact entryBound_connectionRight_of_source (hQd j' h q) (hCd j' h q) (hconstr j' h q)
      (hsupp j' h q) (hP j' h q) (hPinv j' h q) (hbC j' h q) (hbA j' h q) (hbE j' h q)
      (hbPi j' h q) (hbQ' j' h q) h0 h1 h2 h3 h4 i i
  exact A1_halfFloor_from_symbolData i rho hd0 hd1 hpos hident hI hsym hint hnonneg hW
    hconn hsplit hquart hcc hadm hg0 hgg j

/-- **The candidate-patch criterion in source data.**  With the candidate Wilson
floor `√2/2` on the slab of half-width `1/8`, the entire Row A1a Gaussian
obligation is the single inequality
`#c²·#n³·b_C²·b_A·b_E·b_{P⁻¹}·b_{Q'} < √2/4`. -/
theorem candidatePatch_source_criterion (cardc cardn : ℕ) (bC bA bE bPinv bQ' : ℝ)
    (h : sourceConnectionBudget cardc cardn bC bA bE bPinv bQ' < Real.sqrt 2 / 4) :
    0 < ((1 : ℝ) / 8) / 4 *
      (Real.sqrt 2 / 2 - 2 * sourceConnectionBudget cardc cardn bC bA bE bPinv bQ') :=
  (restricted_patch_survives_iff _).2 h

/-- The composite budget written out: the criterion is a bound on
`#c²·#n³·b_C²·b_A·b_E·b_{P⁻¹}·b_{Q'}`. -/
theorem sourceConnectionBudget_expand (cardc cardn : ℕ) (bC bA bE bPinv bQ' : ℝ) :
    sourceConnectionBudget cardc cardn bC bA bE bPinv bQ'
      = (cardc : ℝ) ^ 2 * (cardn : ℝ) ^ 3 * bC ^ 2 * bA * bE * bPinv * bQ' := by
  unfold sourceConnectionBudget connectionBudget pivotBudget
  ring

end YangMills
