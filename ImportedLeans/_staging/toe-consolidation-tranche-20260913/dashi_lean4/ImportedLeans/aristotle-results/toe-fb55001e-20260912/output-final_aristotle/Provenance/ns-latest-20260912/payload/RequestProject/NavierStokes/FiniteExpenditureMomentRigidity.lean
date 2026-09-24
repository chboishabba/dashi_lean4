/-
# The C lane with a support-radius-free rigidity input

`FiniteExpenditureSmallReynoldsRigidity.lean` discharges the rigidity
obligation of the C lane under the threshold `L·K < 2ν`, where `L` is the
radius of the support of the limiting profile.  That is unsatisfactory for a
blow-up limit: the compactness statement then has to produce limits supported
in a *fixed* ball, uniformly.

`GaussianMomentRigidity.lean` removes `L` from the threshold.  This file plugs
the improved rigidity theorem into the same C-lane skeleton, with the support
radius existentially quantified inside the predicate:

  `HeadBoundedStationary ν K V` — `V` is *some* compactly supported,
  divergence-free `C²` stationary similarity profile whose Bernoulli head is
  dominated by `K|V|`.

The threshold is then `4K² < ν`, a condition on the head constant and the
viscosity only.

## Results

* `ClayNS.HeadBoundedStationary` — the predicate, with the support radius
  existentially quantified;
* `ClayNS.headBounded_stationary_eq_zero` — such a profile is trivial when
  `4K² < ν`;
* `ClayNS.finite_projective_expenditure_headBounded_rigidity` — the C-lane
  conclusion with the support-radius-free rigidity input.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.FiniteExpenditureSmallReynoldsRigidity
import RequestProject.NavierStokes.GaussianMomentRigidity

open Filter Set Topology
open RealInnerProductSpace

noncomputable section

namespace ClayNS

/-- A compactly supported (radius unspecified) stationary similarity profile
whose Bernoulli head is dominated by `K|V|`. -/
def HeadBoundedStationary (nu K : ℝ) (V : E3 → E3) : Prop :=
  ∃ (L : ℝ) (p : E3 → ℝ), 0 < L ∧ ContDiff ℝ (2 : ℕ) V ∧ ContDiff ℝ (1 : ℕ) p ∧
    (∀ y, divSpace V y = 0) ∧ (∀ y : E3, L ≤ ‖y‖ → V y = 0) ∧
    (∀ y : E3, |‖V y‖ ^ 2 + 2 * p y| ≤ K * ‖V y‖) ∧ IsStationarySimilarity nu V p

/-- **Such a profile is trivial below the support-radius-free threshold.** -/
theorem headBounded_stationary_eq_zero {nu K : ℝ} (hnu : 0 < nu)
    (hsmall : 4 * K ^ 2 < nu) {V : E3 → E3} (hV : HeadBoundedStationary nu K V) :
    V = 0 := by
  obtain ⟨L, p, hL, hVC, hpC, hdiv, hsupp, hhead, heq⟩ := hV
  funext y
  exact stationary_similarity_rigidity_moment hnu hVC hpC hdiv hL hsupp hhead heq hsmall y

/-- **The C lane with the support-radius-free rigidity input.**  Finite total
projective expenditure of the normalized profile (which the A lane supplies)
plus compactness onto stationary head-bounded limits give convergence of the
normalized profile to the trivial profile along similarity times going to
infinity.  Compare
`ClayNS.finite_projective_expenditure_smallReynolds_rigidity`, whose threshold
still involved the radius of the support. -/
theorem finite_projective_expenditure_headBounded_rigidity
    {nu K : ℝ} (hnu : 0 < nu) (hsmall : 4 * K ^ 2 < nu)
    {Vhat : ℝ → (E3 → E3)} {f Fp : ℝ → ℝ} {C : ℝ}
    (hf : ∀ s, 0 ≤ f s) (hF : ∀ s, HasDerivAt Fp (f s) s) (hb : ∀ s, Fp s ≤ C)
    (hcpt : ∀ tau : ℕ → ℝ, Tendsto tau atTop atTop →
      Tendsto (fun j => f (tau j)) atTop (𝓝 0) →
      ∃ (sub : ℕ → ℕ) (Vinf : E3 → E3), StrictMono sub ∧
        Tendsto (fun j => Vhat (tau (sub j))) atTop (𝓝 Vinf) ∧
        HeadBoundedStationary nu K Vinf) :
    ∃ sigma : ℕ → ℝ, Tendsto sigma atTop atTop ∧
      Tendsto (fun j => Vhat (sigma j)) atTop (𝓝 (0 : E3 → E3)) :=
  finite_projective_expenditure_ancient_rigidity
    (Stationary := HeadBoundedStationary nu K) (triv := (0 : E3 → E3))
    hf hF hb hcpt (fun _ hVinf => headBounded_stationary_eq_zero hnu hsmall hVinf)

end ClayNS
