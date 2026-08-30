/-
# The C lane with its rigidity input discharged

`FiniteProjectiveExpenditure.lean` reduces the C lane to two obligations:

1. compactness together with passage of the equation to the limit, and
2. rigidity for the stationary similarity limit.

`StationarySimilarityRigidity.lean` **proves** the second one for compactly
supported profiles under the Reynolds-type threshold `L·K < 2ν`.  This file
plugs it in: what remains of the C lane in that regime is compactness alone.

## Results

* `ClayNS.SmallReynoldsStationary` — the property of being a compactly
  supported stationary similarity profile with a dominated Bernoulli head;
* `ClayNS.smallReynolds_stationary_eq_zero` — such a profile *is* the zero
  profile when `L·K < 2ν`;
* `ClayNS.finite_projective_expenditure_smallReynolds_rigidity` — the C-lane
  conclusion: finite projective expenditure plus compactness onto
  small-Reynolds stationary limits force the normalized profile to converge to
  the trivial profile along similarity times going to infinity.  Rigidity is no
  longer a hypothesis.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.FiniteProjectiveExpenditure
import RequestProject.NavierStokes.StationarySimilarityRigidity

open Filter Set Topology
open RealInnerProductSpace

noncomputable section

namespace ClayNS

/-- A compactly supported stationary similarity profile with a Bernoulli head
dominated by `K|V|` on a support of radius `L`. -/
def SmallReynoldsStationary (nu L K : ℝ) (V : E3 → E3) : Prop :=
  ∃ p : E3 → ℝ, ContDiff ℝ (2 : ℕ) V ∧ ContDiff ℝ (1 : ℕ) p ∧
    (∀ y, divSpace V y = 0) ∧ (∀ y : E3, L ≤ ‖y‖ → V y = 0) ∧
    (∀ y : E3, |‖V y‖ ^ 2 + 2 * p y| ≤ K * ‖V y‖) ∧ IsStationarySimilarity nu V p

/-- **Such a profile is trivial below the Reynolds threshold.** -/
theorem smallReynolds_stationary_eq_zero {nu L K : ℝ} (hnu : 0 < nu) (hL : 0 < L)
    (hsmall : L * K < 2 * nu) {V : E3 → E3} (hV : SmallReynoldsStationary nu L K V) :
    V = 0 := by
  obtain ⟨p, hVC, hpC, hdiv, hsupp, hhead, heq⟩ := hV
  funext y
  exact stationary_similarity_rigidity hnu hL hVC hpC hdiv hsupp hhead heq hsmall y

/-- **The C lane, with rigidity discharged.**  Finite total projective
expenditure of the normalized profile (which the A lane supplies) plus
compactness onto stationary small-Reynolds limits give convergence of the
normalized profile to the trivial profile along similarity times going to
infinity.  Compare `ClayNS.finite_projective_expenditure_ancient_rigidity`,
where rigidity was still an assumption. -/
theorem finite_projective_expenditure_smallReynolds_rigidity
    {nu L K : ℝ} (hnu : 0 < nu) (hL : 0 < L) (hsmall : L * K < 2 * nu)
    {Vhat : ℝ → (E3 → E3)} {f Fp : ℝ → ℝ} {C : ℝ}
    (hf : ∀ s, 0 ≤ f s) (hF : ∀ s, HasDerivAt Fp (f s) s) (hb : ∀ s, Fp s ≤ C)
    (hcpt : ∀ tau : ℕ → ℝ, Tendsto tau atTop atTop →
      Tendsto (fun j => f (tau j)) atTop (𝓝 0) →
      ∃ (sub : ℕ → ℕ) (Vinf : E3 → E3), StrictMono sub ∧
        Tendsto (fun j => Vhat (tau (sub j))) atTop (𝓝 Vinf) ∧
        SmallReynoldsStationary nu L K Vinf) :
    ∃ sigma : ℕ → ℝ, Tendsto sigma atTop atTop ∧
      Tendsto (fun j => Vhat (sigma j)) atTop (𝓝 (0 : E3 → E3)) :=
  finite_projective_expenditure_ancient_rigidity
    (Stationary := SmallReynoldsStationary nu L K) (triv := (0 : E3 → E3))
    hf hF hb hcpt (fun _ hVinf => smallReynolds_stationary_eq_zero hnu hL hsmall hVinf)

end ClayNS
