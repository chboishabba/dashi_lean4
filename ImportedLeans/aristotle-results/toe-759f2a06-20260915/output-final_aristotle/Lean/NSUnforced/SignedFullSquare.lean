/-
# Signed full-square carriers for the unforced A1 (R568) programme

## Object

`DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact.fullSquareSum`
is the complete *ordered* square of a rational pair scalar over a finite list of
triad incidences,

```agda
fullSquareSum F []         = 0
fullSquareSum F (x ∷ rest) = F x x + rowSum F x rest + columnSum F rest x
                             + fullSquareSum F rest
```

which is literally `∑_{a ∈ s} ∑_{b ∈ s} F a b` on the underlying finite index
set.  This file re-erects that carrier over `ℝ`, where the analysis actually
happens, and proves the three structural facts the R568 route needs *before*
any positive majorisation is allowed to run:

* `fullSquareSum_transpose` — transpose invariance (the R566 input);
* `fullSquareSum_two_add_transpose` — the R567 collapse
  `Full(2·(P + Pᵀ)) = 4 · Full P`, which is the source of the literal factor `4`
  in the R568 endpoint `4 ∫ globalForcingFull ≤ B(T)`;
* `fullSquareSum_gram_collapse` — the **signed** collapse of a
  Gram-factorised resolvent against an inner-product pair kernel.  This is the
  step the control record insists on: all cancellation in the `α`,`β` sums is
  performed *exactly*, as an identity between the full square and a sum of
  `J`-many honest inner products, and only afterwards
  (`abs_fullSquareSum_gram_collapse_le`) is a positive Cauchy–Schwarz
  majorisation applied.

## Lineage

`R543` (full ordered square), `R566` (transpose symmetry of the forcing /
amplitude halves), `R567` (`Full(pairScalar) = 4 · Full(forcingPair)`),
`R566.forcingPairScalarized` (`forcingPair α β = ρ α β · ⟪D α, C β⟫`, with `ρ`
the *symmetric* pair resolvent `Swap.pairResolvent`), `R503`/`R572` (the
signed-cross / compiler consumers that read the collapsed form).

## Consumer

`DASHI.NS.Unforced.A1Budget568` — the collapsed inner-product form is what the
pointwise absorption hypothesis of the cutoff-uniform budget is stated about.

## Status

Infrastructure: exact identities, no analytic estimate, no PDE input.
-/
import Mathlib

namespace DASHI.NS.Unforced

open Finset

variable {ι : Type*} {κ : Type*} {E : Type*}

/-- The complete ordered square of a pair scalar over a finite index set.  This
is the `ℝ`-carrier of the Agda `R543.fullSquareSum`. -/
def fullSquareSum (F : ι → ι → ℝ) (s : Finset ι) : ℝ := ∑ a ∈ s, ∑ b ∈ s, F a b

@[simp] theorem fullSquareSum_empty (F : ι → ι → ℝ) : fullSquareSum F ∅ = 0 := by
  simp [fullSquareSum]

/-- **R543 split.**  The full ordered square is the diagonal plus the ordered
off-diagonal. -/
theorem fullSquareSum_eq_diag_add_offDiag [DecidableEq ι] (F : ι → ι → ℝ) (s : Finset ι) :
    fullSquareSum F s
      = (∑ a ∈ s, F a a) + ∑ a ∈ s, ∑ b ∈ s.erase a, F a b := by
  unfold fullSquareSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [← Finset.add_sum_erase s (fun b => F a b) ha]

/-- **R566 transpose invariance.**  The full ordered square does not see the
transpose. -/
theorem fullSquareSum_transpose (F : ι → ι → ℝ) (s : Finset ι) :
    fullSquareSum (fun a b => F b a) s = fullSquareSum F s :=
  Finset.sum_comm

theorem fullSquareSum_add (P Q : ι → ι → ℝ) (s : Finset ι) :
    fullSquareSum (fun a b => P a b + Q a b) s
      = fullSquareSum P s + fullSquareSum Q s := by
  simp [fullSquareSum, Finset.sum_add_distrib]

theorem fullSquareSum_const_mul (c : ℝ) (P : ι → ι → ℝ) (s : Finset ι) :
    fullSquareSum (fun a b => c * P a b) s = c * fullSquareSum P s := by
  simp [fullSquareSum, Finset.mul_sum]

/-- **R567 collapse, over `ℝ`.**  The literal R545 pointwise normal form is
`pairScalar = 2 · (forcingPair + amplitudePair)` and R566 identifies
`amplitudePair` with the transpose of `forcingPair`.  Hence the complete pair
scalar's full square is exactly four times the commutator-only full square.
This is the provenance of the constant `4` in the R568 endpoint. -/
theorem fullSquareSum_two_add_transpose (P : ι → ι → ℝ) (s : Finset ι) :
    fullSquareSum (fun a b => 2 * (P a b + P b a)) s = 4 * fullSquareSum P s := by
  have h : fullSquareSum (fun a b => 2 * (P a b + P b a)) s
      = 2 * (fullSquareSum P s + fullSquareSum (fun a b => P b a) s) := by
    rw [← fullSquareSum_add P (fun a b => P b a) s,
      ← fullSquareSum_const_mul 2 (fun a b => P a b + P b a) s]
  rw [h, fullSquareSum_transpose]
  ring

section Gram

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The literal R566 shape of the commutator-only pair scalar:
`forcingPair α β = ρ α β * ⟪Dvec α, Cvec β⟫`, where `ρ` is the symmetric pair
resolvent and `Dvec`/`Cvec` are the doubled forcing and cell vectors. -/
def resolventPair (rho : ι → ι → ℝ) (Dvec Cvec : ι → E) (a b : ι) : ℝ :=
  rho a b * (inner (𝕜 := ℝ) (Dvec a) (Cvec b))

/-- **Signed Gram collapse (exact).**  If the pair resolvent admits a finite
Gram factorisation `ρ a b = ∑_{j ∈ J} r j a * r j b` — which the R503/R572
spectator-row machinery produces for the literal symmetric `Swap.pairResolvent`
— then the full ordered square of the commutator-only pair scalar collapses
*exactly* to a finite sum of inner products of assembled vectors.

No absolute value, no norm and no estimate occurs: every cancellation in the
`α`,`β` double sum survives into the right-hand side. -/
theorem fullSquareSum_gram_collapse (J : Finset κ) (r : κ → ι → ℝ)
    (Dvec Cvec : ι → E) (s : Finset ι) :
    fullSquareSum (resolventPair (fun a b => ∑ j ∈ J, r j a * r j b) Dvec Cvec) s
      = ∑ j ∈ J,
          inner (𝕜 := ℝ) (∑ a ∈ s, r j a • Dvec a) (∑ b ∈ s, r j b • Cvec b) := by
  have hr : ∀ j : κ,
      inner (𝕜 := ℝ) (∑ a ∈ s, r j a • Dvec a) (∑ b ∈ s, r j b • Cvec b)
        = ∑ a ∈ s, ∑ b ∈ s, r j a * r j b * (inner (𝕜 := ℝ) (Dvec a) (Cvec b)) := by
    intro j
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, mul_assoc]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  simp only [hr, fullSquareSum, resolventPair, Finset.sum_mul]
  calc ∑ a ∈ s, ∑ b ∈ s, ∑ j ∈ J, r j a * r j b * (inner (𝕜 := ℝ) (Dvec a) (Cvec b))
      = ∑ a ∈ s, ∑ j ∈ J, ∑ b ∈ s, r j a * r j b * (inner (𝕜 := ℝ) (Dvec a) (Cvec b)) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ j ∈ J, ∑ a ∈ s, ∑ b ∈ s, r j a * r j b * (inner (𝕜 := ℝ) (Dvec a) (Cvec b)) :=
        Finset.sum_comm

/-- **Positive majorisation, applied only after the signed collapse.**  Cauchy–
Schwarz on each collapsed channel. -/
theorem abs_fullSquareSum_gram_collapse_le (J : Finset κ) (r : κ → ι → ℝ)
    (Dvec Cvec : ι → E) (s : Finset ι) :
    |fullSquareSum (resolventPair (fun a b => ∑ j ∈ J, r j a * r j b) Dvec Cvec) s|
      ≤ ∑ j ∈ J, ‖∑ a ∈ s, r j a • Dvec a‖ * ‖∑ b ∈ s, r j b • Cvec b‖ := by
  rw [fullSquareSum_gram_collapse]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
  exact abs_real_inner_le_norm _ _

/-- **Rank-one (constant-resolvent) specialisation.**  With a single Gram
channel the collapse is a single inner product: the entire fibre double sum is
paid by one assembled forcing vector against one assembled cell vector. -/
theorem fullSquareSum_rankOne_collapse (r : ι → ℝ) (Dvec Cvec : ι → E)
    (s : Finset ι) :
    fullSquareSum (resolventPair (fun a b => r a * r b) Dvec Cvec) s
      = inner (𝕜 := ℝ) (∑ a ∈ s, r a • Dvec a) (∑ b ∈ s, r b • Cvec b) := by
  have h := fullSquareSum_gram_collapse (ι := ι) (κ := Unit) {()} (fun _ => r)
    Dvec Cvec s
  simpa using h

end Gram

end DASHI.NS.Unforced
