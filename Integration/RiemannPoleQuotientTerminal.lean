import Mathlib

/-!
# The terminal pole–quotient algebra (§§4, 6, 8 of the manuscript)

`Riemann_Pole_Quotient_Reduction_2026.pdf` attaches to a hypothetical high
off-critical-line zero `ρ`, an admissible taper `g` and a cutoff `J` four real
scalars

```
Ccluster (ρ; g)     the distinguished cluster response,
Doff     (ρ; g)     the complementary off-ordinate contribution,
DΓ       (ρ; g)     the Gamma-factor contribution,
Dnear    (ρ; g, J)  the finite signed near part,
```

together with the far majorant `Bfar (ρ; g, J)`.  The terminal step of the
manuscript is pure algebra on these five reals:

* the **exact balance** `Ccluster = Doff + DΓ` (a representation theorem, (1));
* the **near/far split** `Doff ≤ Dnear + Bfar` (2);
* the **strict high inequality** `Dnear + Bfar + DΓ < Ccluster` (3).

Theorem 8.1 says the three together are contradictory.  Proposition 6.3 says
that a certified upper bound `U` for the literal finite near sum `Snear`,
together with the near representation `Dnear = Snear`, suffices to produce (3).

This module proves exactly those two statements.  **No analytic content is
asserted here**: `PoleQuotientResponse` is a record of five arbitrary reals,
and the analytic obligations of the manuscript — that the explicit formula
really produces such data satisfying (1), (2) and (3) — are *hypotheses*, never
discharged in this corpus.
-/

namespace Integration.RiemannPoleQuotient

/-- The five scalars of the pole–quotient explicit-formula response attached to
one zero, one taper and one cutoff.  The fields carry no analytic meaning here;
they are named after the manuscript's quantities. -/
structure PoleQuotientResponse where
  /-- The distinguished cluster response `Ccluster`. -/
  cluster : ℝ
  /-- The complementary off-ordinate contribution `Doff`. -/
  off : ℝ
  /-- The Gamma-factor contribution `DΓ`. -/
  gamma : ℝ
  /-- The finite signed near part `Dnear` at the chosen cutoff. -/
  near : ℝ
  /-- The nonnegative far-tail majorant `Bfar` at the chosen cutoff. -/
  far : ℝ

namespace PoleQuotientResponse

variable (R : PoleQuotientResponse)

/-- Equation (1): the exact explicit-formula balance
`Ccluster = Doff + DΓ`. -/
def Balance : Prop := R.cluster = R.off + R.gamma

/-- Equation (2): the near/far upper split `Doff ≤ Dnear + Bfar`. -/
def NearFarSplit : Prop := R.off ≤ R.near + R.far

/-- Equation (3): the strict terminal high inequality
`Dnear + Bfar + DΓ < Ccluster`. -/
def StrictHigh : Prop := R.near + R.far + R.gamma < R.cluster

end PoleQuotientResponse

open PoleQuotientResponse

/-- **Theorem 8.1 (high off-line zero contradiction).**  The exact balance, the
near/far upper split and the strict high inequality cannot hold simultaneously. -/
theorem terminal_contradiction {R : PoleQuotientResponse}
    (hbal : R.Balance) (hsplit : R.NearFarSplit) (hstrict : R.StrictHigh) : False := by
  unfold PoleQuotientResponse.Balance at hbal
  unfold PoleQuotientResponse.NearFarSplit at hsplit
  unfold PoleQuotientResponse.StrictHigh at hstrict
  linarith

/-- **Proposition 6.3 (certified sufficient high inequality).**  If the near
response equals the literal finite signed sum `Snear`, if `U` is an upper
certificate for that sum, and if the certified inequality
`U + Bfar + DΓ < Ccluster` holds, then the strict high inequality (3) holds. -/
theorem strictHigh_of_certificate {R : PoleQuotientResponse} {Snear U : ℝ}
    (hrep : R.near = Snear) (hcert : Snear ≤ U)
    (hstrict : U + R.far + R.gamma < R.cluster) : R.StrictHigh := by
  unfold PoleQuotientResponse.StrictHigh
  rw [hrep]
  linarith

/-- The certified route also lands directly in a contradiction. -/
theorem terminal_contradiction_of_certificate {R : PoleQuotientResponse} {Snear U : ℝ}
    (hbal : R.Balance) (hsplit : R.NearFarSplit) (hrep : R.near = Snear)
    (hcert : Snear ≤ U) (hstrict : U + R.far + R.gamma < R.cluster) : False :=
  terminal_contradiction hbal hsplit (strictHigh_of_certificate hrep hcert hstrict)

/-- Sharpness in the other direction: the balance and the near/far split alone
are consistent — they are satisfied by a response with `Dnear + Bfar + DΓ =
Ccluster`.  So the strict inequality (3) really is the whole analytic payment,
and Theorem 8.1 is not vacuous. -/
theorem balance_and_split_consistent :
    ∃ R : PoleQuotientResponse, R.Balance ∧ R.NearFarSplit ∧ ¬ R.StrictHigh := by
  refine ⟨⟨0, 0, 0, 0, 0⟩, ?_, ?_, ?_⟩ <;>
    simp [PoleQuotientResponse.Balance, PoleQuotientResponse.NearFarSplit,
      PoleQuotientResponse.StrictHigh]

end Integration.RiemannPoleQuotient
